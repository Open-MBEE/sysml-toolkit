//! Expression → SMT translation against a resolved model.
//!
//! The supported (decidable) fragment: boolean/integer/real literals and
//! arithmetic (`+ - * /`, power by a small constant exponent), comparisons,
//! logical connectives, conditionals, and references — bound features
//! constant-fold through the evaluator or inline their defining
//! expressions; user-calculation invocations inline their bodies with
//! arguments bound to parameters (recursion and unbound default-less
//! parameters bail); unbound features become free SMT constants whose sorts come
//! from their declared types (`Boolean`/`Integer`/`Natural`/`Positive`/
//! `Real`/`Rational`/`Number`, found by walking explicit typings and
//! specializations upward) with enumeration definitions lowering to finite
//! datatypes. Everything else — sequences, strings, classification,
//! `%` on quantities, `..`, `??` — is outside the fragment and reported
//! as [`Unsupported`].
//!
//! Sort discipline: variable sorts start unknown and are *demanded* by
//! context (boolean operand, numeric operand, equality with a known-sorted
//! term); equalities between two still-unknown variables unify at
//! finalization; anything still numeric-or-unknown defaults to `Real`.
//!
//! Unit discipline: quantity constants fold to bare numbers but carry a
//! *unit tag* (dimensional key + scale) through translation; a bracket
//! whose magnitude is unbound (`x [mm]`) translates the magnitude
//! structurally and reads its unit expression alone. Tags unify
//! across `+ - < <= > >= == !=` and conditionals (propagating onto free
//! variables through additive subterms) and compose through `* /`. Two
//! tags over one dimension with different scales *convert* — the right
//! term rescales into the left's unit, mirroring the evaluator's
//! measurement-reference conversion; two different *dimensions* meeting
//! in one operation — or on one variable — bail. Each variable still
//! lives in a single unit; witnesses report it.

use crate::term::{EnumSort, Op, Sort, Term};
use std::collections::{HashMap, HashSet, VecDeque};
use sysmlv2_model::eval::Value;
use sysmlv2_model::json::{ConstraintInfo, ElementRef, ResolvedModel, ScopeRef};
use sysmlv2_model::rational::Rational;
use sysmlv2_syntax::ast::*;

/// The construct (with context) that put an expression outside the
/// solvable fragment.
pub(crate) struct Unsupported(pub String);

fn bail<T>(msg: impl Into<String>) -> Result<T, Unsupported> {
    Err(Unsupported(msg.into()))
}

/// One free SMT constant.
pub(crate) struct VarInfo {
    /// Model-facing name (the reference's source spelling).
    pub display: String,
    /// SMT symbol.
    pub sym: String,
    /// Finalized sort.
    pub sort: Sort,
    /// Inferred measurement unit (display spelling), for witness output.
    pub unit: Option<String>,
    /// An auxiliary introduced by the translation itself (it names one
    /// step of a sequence fold and is defined by a side equality) — part
    /// of the variable space, never reported to callers.
    pub aux: bool,
}

/// A measurement-unit tag: canonical *dimensional* key, the scale to
/// the reference magnitude (`min` = 60), and the display spelling. Two
/// tags with one key but different scales measure the same dimension
/// and convert.
#[derive(Clone, Debug)]
struct UTag {
    key: String,
    scale: Rational,
    display: String,
}

impl PartialEq for UTag {
    fn eq(&self, other: &UTag) -> bool {
        self.key == other.key && self.scale == other.scale
    }
}

/// A translated term with its unit tag (`None` = unitless/unknown).
struct UT {
    term: Term,
    unit: Option<UTag>,
}

impl UT {
    fn plain(term: Term) -> UT {
        UT { term, unit: None }
    }
}

/// A fully translated constraint, ready to render and hand to the solver.
pub(crate) struct Translation {
    /// The constraint's goal term (`assert not` negation already applied):
    /// the constraint holds iff this boolean term is true.
    pub root: Term,
    pub vars: Vec<VarInfo>,
    pub enums: Vec<EnumSort>,
    /// Extra assertions: declared-type range constraints (e.g. `Natural`)
    /// and the defining equalities of auxiliary variables.
    pub side: Vec<Term>,
    /// Features that carry a defining expression the translator could not
    /// encode and therefore treated as free — SAT results are then only
    /// over-approximations (UNSAT/validity stay definitive).
    pub approx: Vec<String>,
}

#[derive(Clone, Copy, PartialEq, Debug)]
enum SortState {
    Unknown,
    Numeric,
    Fixed(Sort),
}

/// What a parameter/lambda name is bound to in the environment.
#[derive(Clone)]
enum Binding {
    /// An ordinary scalar term (calculation arguments, sequence items).
    Scalar(Term, Option<UTag>),
    /// The k-th anonymous member of a skolemized bounded collection:
    /// a bare reference mints one variable per instance
    /// (`path`, sorted like the collection feature); chains resolve
    /// members from `ty` and mint per-instance leaf variables.
    Instance {
        feature: ElementRef,
        ty: Option<ElementRef>,
        path: String,
    },
}

/// Cap on skolem instances per collection — quantifier expansion is
/// n × body-size, so a runaway multiplicity must stay a bail, not a blowup.
const SKOLEM_CAP: usize = 32;

#[derive(Clone, Copy, PartialEq, Debug)]
enum Demand {
    Bool,
    Numeric,
    Exact(Sort),
}

/// What [`Translator::finish`] hands back: finalized variables, used enum
/// sorts, side assertions, and over-approximated features.
type Finished = (Vec<VarInfo>, Vec<EnumSort>, Vec<Term>, Vec<String>);

/// One constraint's place in a joint translation: its goal term
/// (negation applied), or the reason it stayed outside the fragment.
pub(crate) enum JointRoot {
    Root(Term),
    /// A conjunction that translated only partially: the conjuncts
    /// inside the fragment (each stands as a fact on its own — a
    /// conjunction asserts all of them), plus the reason the whole
    /// expression bailed. The translated conjuncts can still prove the
    /// constraint violated or unsatisfiable and still narrow domains;
    /// satisfaction is out of reach (a conjunct is unaccounted for).
    /// Never produced for a negated constraint — `not (a and b)` does
    /// not assert its conjuncts.
    Partial {
        terms: Vec<Term>,
        skipped: String,
    },
    Skipped(String),
}

/// Several constraints translated against ONE variable space: a feature
/// shared across constraints becomes one free variable, so a domain
/// contracted through one constraint narrows the others — the joint
/// system the propagation backend works on. A constraint outside the
/// fragment is skipped (recorded) without poisoning the rest; variables
/// and side assertions it half-registered stay — they are
/// true-by-declaration facts or definitions of auxiliaries, so keeping
/// them narrows nothing.
///
/// An over-approximated feature (a definition outside the fragment, treated
/// as free) is not tracked here the way [`Translation::approx`] tracks it
/// for the SMT path: propagation's definitive verdicts (satisfied /
/// violated / unsatisfiable) all stay sound under a *wider* reachable set,
/// so the extra freedom never invalidates them.
pub(crate) struct JointTranslation {
    /// Index-aligned with the input constraints.
    pub roots: Vec<JointRoot>,
    pub vars: Vec<VarInfo>,
    pub enums: Vec<EnumSort>,
    pub side: Vec<Term>,
}

/// The model's enumeration literals, indexed for translation. Deriving
/// them walks every scope's name table, so they are derived **once** per
/// resolved model and shared by every constraint's translation rather
/// than rebuilt per constraint. The element and scope tables a resolved
/// model is built from do not change afterwards, so one derivation
/// serves the whole run.
pub(crate) struct EnumTables {
    /// Enum literal → its EnumerationDefinition.
    lit_to_enum: HashMap<ElementRef, ElementRef>,
    /// EnumerationDefinition → its literals in declaration order.
    enum_lits: HashMap<ElementRef, Vec<ElementRef>>,
    /// Literal → position within its definition.
    lit_pos: HashMap<ElementRef, usize>,
}

impl EnumTables {
    pub(crate) fn build(r: &ResolvedModel) -> EnumTables {
        let mut lit_to_enum = HashMap::new();
        let mut enum_lits = HashMap::new();
        let mut lit_pos = HashMap::new();
        for (def, lits) in r.enum_types() {
            for (i, &lit) in lits.iter().enumerate() {
                lit_to_enum.insert(lit, def);
                lit_pos.insert(lit, i);
            }
            enum_lits.insert(def, lits);
        }
        EnumTables {
            lit_to_enum,
            enum_lits,
            lit_pos,
        }
    }
}

/// Translate `cs` jointly. `Err` means finalization itself failed (a
/// sort or unit conflict *between* constraints) — the caller degrades to
/// no propagation, not to a partial one.
pub(crate) fn translate_all(
    r: &mut ResolvedModel,
    tables: &EnumTables,
    cs: &[&ConstraintInfo],
) -> Result<JointTranslation, Unsupported> {
    let mut tr = Translator::new(r, tables);
    let mut roots = Vec::with_capacity(cs.len());
    for c in cs {
        let translated = tr
            .expr(c.scope, &c.expr)
            .and_then(|ut| tr.demand(&ut.term, Demand::Bool).map(|()| ut));
        match translated {
            Ok(ut) => roots.push(JointRoot::Root(if c.negated {
                Term::App(Op::Not, vec![ut.term])
            } else {
                ut.term
            })),
            Err(Unsupported(m)) => {
                // A conjunction degrades per conjunct: the ones inside
                // the fragment still contribute (one spoiled term no
                // longer silences its siblings' narrowing). Half-
                // registered state from failed conjuncts stays, like
                // any skipped constraint's — declaration facts only.
                let conjuncts = if c.negated {
                    Vec::new()
                } else {
                    conjuncts_of(&c.expr)
                };
                let terms: Vec<Term> = conjuncts
                    .iter()
                    .filter_map(|e| {
                        tr.expr(c.scope, e)
                            .and_then(|ut| tr.demand(&ut.term, Demand::Bool).map(|()| ut.term))
                            .ok()
                    })
                    .collect();
                roots.push(if terms.is_empty() {
                    JointRoot::Skipped(m)
                } else {
                    JointRoot::Partial { terms, skipped: m }
                });
            }
        }
    }
    // `approx` is intentionally dropped — see [`JointTranslation`].
    let (vars, enums, side, _approx) = tr.finish()?;
    Ok(JointTranslation {
        roots,
        vars,
        enums,
        side,
    })
}

/// The top-level conjuncts of an `and`/`&` chain, flattened through
/// nesting; empty when the expression is not a conjunction (fewer than
/// two conjuncts — nothing to degrade to).
fn conjuncts_of(e: &Expr) -> Vec<&Expr> {
    fn walk<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
        match &e.kind {
            ExprKind::Binary {
                op: BinaryOp::CondAnd | BinaryOp::AndAmp,
                lhs,
                rhs,
            } => {
                walk(lhs, out);
                walk(rhs, out);
            }
            _ => out.push(e),
        }
    }
    let mut out = Vec::new();
    walk(e, &mut out);
    if out.len() < 2 { Vec::new() } else { out }
}

/// Argument-count admission for the sequence-intrinsic table — a shape
/// outside it falls through to the ordinary calculation path, mirroring
/// the evaluator's dispatch.
fn seq_intrinsic_arity_ok(name: &str, n: usize) -> bool {
    match name {
        "sum" | "product" | "size" | "isEmpty" | "notEmpty" | "head" | "last" | "abs" => n == 1,
        "max" | "min" => (1..=2).contains(&n),
        _ => false,
    }
}

pub(crate) fn translate(
    r: &mut ResolvedModel,
    tables: &EnumTables,
    c: &ConstraintInfo,
) -> Result<Translation, Unsupported> {
    let mut tr = Translator::new(r, tables);
    let root = tr.expr(c.scope, &c.expr)?.term;
    tr.demand(&root, Demand::Bool)?;
    let (vars, enums, side, approx) = tr.finish()?;
    let root = if c.negated {
        Term::App(Op::Not, vec![root])
    } else {
        root
    };
    Ok(Translation {
        root,
        vars,
        enums,
        side,
        approx,
    })
}

struct Translator<'m> {
    r: &'m mut ResolvedModel,
    /// Free variables keyed by (element, featuring context) — the same
    /// inherited feature reached through two different usages is two
    /// distinct unknowns.
    var_keys: HashMap<(ElementRef, Option<ScopeRef>), usize>,
    displays: Vec<String>,
    states: Vec<SortState>,
    /// Whether each variable is a translation-made auxiliary
    /// (index-aligned with `displays`).
    aux: Vec<bool>,
    /// Auxiliary variable → index in `side` of its defining equality.
    aux_defs: HashMap<usize, usize>,
    side: Vec<Term>,
    /// Equalities between two still-unknown variables, unified at finish.
    pending_eq: Vec<(usize, usize)>,
    /// Features whose defining expressions are being inlined (cycle guard).
    inlining: HashSet<ElementRef>,
    /// Calculations whose bodies are being inlined (recursion bails —
    /// unbounded unrolling has no finite translation).
    inlining_calcs: HashSet<ElementRef>,
    /// Calculation/lambda-parameter bindings, innermost last — dynamic
    /// extent with one level of shadowing, exactly like the evaluator's
    /// lambda/parameter environment.
    env: Vec<(String, Binding)>,
    /// Per-instance variables of skolemized bounded collections,
    /// keyed by their display path (`ws#2.radius`) — the same collection
    /// quantified twice shares its instances.
    skolem_vars: HashMap<String, usize>,
    approx: Vec<String>,
    /// Inferred unit tag per variable (index-aligned with `displays`).
    var_units: Vec<Option<UTag>>,
    /// Unit linkage between two still-untagged variables, unified at
    /// finish (piggybacks the sort mechanism).
    pending_unit_eq: Vec<(usize, usize)>,
    /// The model's enumeration literal index, derived once per run.
    tables: &'m EnumTables,
    /// Enum definitions actually used, in first-use order.
    enum_defs: Vec<ElementRef>,
    enum_index: HashMap<ElementRef, usize>,
}

impl<'m> Translator<'m> {
    fn new(r: &'m mut ResolvedModel, tables: &'m EnumTables) -> Translator<'m> {
        Translator {
            r,
            var_keys: HashMap::new(),
            displays: Vec::new(),
            states: Vec::new(),
            aux: Vec::new(),
            aux_defs: HashMap::new(),
            side: Vec::new(),
            pending_eq: Vec::new(),
            inlining: HashSet::new(),
            inlining_calcs: HashSet::new(),
            env: Vec::new(),
            skolem_vars: HashMap::new(),
            approx: Vec::new(),
            var_units: Vec::new(),
            pending_unit_eq: Vec::new(),
            tables,
            enum_defs: Vec::new(),
            enum_index: HashMap::new(),
        }
    }

    // -- constant folding ---------------------------------------------------

    /// Try the evaluator first: anything it computes to a scalar is a
    /// literal term (quantities carry their unit tag). `Ok(None)` = not a
    /// constant (translate structurally).
    fn fold(&mut self, scope: ScopeRef, e: &Expr) -> Result<Option<UT>, Unsupported> {
        match self.r.evaluate_in(scope, e) {
            Ok(Value::Boolean(b)) => Ok(Some(UT::plain(Term::BoolLit(b)))),
            Ok(Value::Integer(i)) => Ok(Some(UT::plain(Term::IntLit(i)))),
            Ok(Value::Rational(r)) => Ok(Some(UT::plain(Term::RealLit(r)))),
            Ok(Value::Real(f)) => match Rational::from_f64(f) {
                Some(r) => Ok(Some(UT::plain(Term::RealLit(r)))),
                None => bail("a non-finite numeric value"),
            },
            Ok(Value::Quantity(n, u)) => {
                let unit = Some(UTag {
                    key: u.dims_key(),
                    scale: u.scale().clone(),
                    display: u.display().to_string(),
                });
                let term = match *n {
                    Value::Integer(i) => Term::IntLit(i),
                    Value::Rational(r) => Term::RealLit(r),
                    Value::Real(f) => match Rational::from_f64(f) {
                        Some(r) => Term::RealLit(r),
                        None => return bail("a non-finite numeric value"),
                    },
                    _ => return bail("a non-numeric quantity magnitude"),
                };
                Ok(Some(UT { term, unit }))
            }
            Ok(Value::String(s)) => Ok(Some(UT::plain(Term::StrLit(s)))),
            Ok(Value::Element(el)) if self.tables.lit_to_enum.contains_key(&el) => {
                Ok(Some(UT::plain(self.enum_term(el)?)))
            }
            Ok(Value::Element(_))
            | Ok(Value::Unbound(_) | Value::UnboundMember(_))
            | Ok(Value::Indeterminate)
            | Ok(Value::Instance { .. })
            | Ok(Value::Sequence(_))
            | Err(_) => Ok(None),
        }
    }

    // -- expression translation ----------------------------------------------

    fn expr(&mut self, scope: ScopeRef, e: &Expr) -> Result<UT, Unsupported> {
        if let Some(t) = self.fold(scope, e)? {
            return Ok(t);
        }
        match &e.kind {
            ExprKind::Ref(qn) => self.ref_term(scope, qn),
            ExprKind::ChainStep { target, member } => self.chain(scope, e, target, member),
            ExprKind::Unary { op, operand } => match op {
                UnaryOp::Plus => self.expr(scope, operand),
                UnaryOp::Minus => {
                    let t = self.expr(scope, operand)?;
                    self.demand(&t.term, Demand::Numeric)?;
                    Ok(UT {
                        term: Term::App(Op::Neg, vec![t.term]),
                        unit: t.unit,
                    })
                }
                UnaryOp::Not => {
                    let t = self.expr(scope, operand)?;
                    self.demand(&t.term, Demand::Bool)?;
                    Ok(UT::plain(Term::App(Op::Not, vec![t.term])))
                }
                UnaryOp::Tilde => bail("`~` conjugation"),
            },
            ExprKind::Binary { op, lhs, rhs } => self.binary(scope, *op, lhs, rhs),
            ExprKind::Conditional {
                cond,
                then_branch,
                else_branch,
            } => {
                let c = self.expr(scope, cond)?;
                self.demand(&c.term, Demand::Bool)?;
                let mut a = self.expr(scope, then_branch)?;
                let mut b = self.expr(scope, else_branch)?;
                self.unify(&a.term, &b.term)?;
                let unit = self.unify_units(&mut a, &mut b)?;
                Ok(UT {
                    term: Term::App(Op::Ite, vec![c.term, a.term, b.term]),
                    unit,
                })
            }
            ExprKind::Literal(_) => bail("a literal outside the numeric/boolean range"),
            ExprKind::Null => bail("`null`"),
            ExprKind::Sequence(_) => bail("sequence expressions"),
            ExprKind::Index { .. } => bail("sequence indexing"),
            // A quantity bracket over a magnitude the evaluator could not
            // fold (constant brackets fold above): translate the
            // magnitude structurally, read the unit expression alone, and
            // tag the term — mirroring the evaluator's semantics,
            // including folding a dimensionless residual scale (`[mm/m]`)
            // into the number.
            ExprKind::Bracket { target, arg } => {
                let t = self.expr(scope, target)?;
                if t.unit.is_some() {
                    return bail("a quantity magnitude that is itself a quantity");
                }
                self.demand(&t.term, Demand::Numeric)?;
                let unit = self
                    .r
                    .unit_of_in(scope, arg)
                    .map_err(|e| Unsupported(format!("a quantity-unit bracket: {e}")))?;
                if unit.dims_key().is_empty() {
                    return if unit.scale().is_one() {
                        Ok(UT::plain(t.term))
                    } else {
                        Ok(UT::plain(Term::App(
                            Op::Mul,
                            vec![t.term, Term::RealLit(unit.scale().clone())],
                        )))
                    };
                }
                Ok(UT {
                    term: t.term,
                    unit: Some(UTag {
                        key: unit.dims_key(),
                        scale: unit.scale().clone(),
                        display: unit.display().to_string(),
                    }),
                })
            }
            ExprKind::Invocation { ty, args } => self.invocation(scope, ty, args),
            ExprKind::Arrow { target, ty, args } => self.arrow(scope, target, ty, args),
            ExprKind::Collect { .. } | ExprKind::Select { .. } => {
                bail("collect/select over unbound features")
            }
            ExprKind::Constructor { .. } => bail("`new` constructors"),
            ExprKind::Body { .. } | ExprKind::BodyTerminator => {
                bail("expression bodies over unbound features")
            }
            ExprKind::Classification { .. } => bail("classification operators"),
            ExprKind::Extent { .. } => bail("`all` extents"),
            ExprKind::MetadataAccess { .. } => bail("`.metadata` access"),
        }
    }

    fn binary(
        &mut self,
        scope: ScopeRef,
        op: BinaryOp,
        lhs: &Expr,
        rhs: &Expr,
    ) -> Result<UT, Unsupported> {
        use BinaryOp::*;
        let bool_op = |tr: &mut Self, o: Op| -> Result<UT, Unsupported> {
            let l = tr.expr(scope, lhs)?;
            let r = tr.expr(scope, rhs)?;
            tr.demand(&l.term, Demand::Bool)?;
            tr.demand(&r.term, Demand::Bool)?;
            Ok(UT::plain(Term::App(o, vec![l.term, r.term])))
        };
        // Comparisons and additive arithmetic unify the operand units.
        let num_op = |tr: &mut Self, o: Op| -> Result<UT, Unsupported> {
            let mut l = tr.expr(scope, lhs)?;
            let mut r = tr.expr(scope, rhs)?;
            tr.demand(&l.term, Demand::Numeric)?;
            tr.demand(&r.term, Demand::Numeric)?;
            let unit = tr.unify_units(&mut l, &mut r)?;
            let unit = match o {
                Op::Lt | Op::Le | Op::Gt | Op::Ge => None,
                _ => unit,
            };
            Ok(UT {
                term: Term::App(o, vec![l.term, r.term]),
                unit,
            })
        };
        match op {
            CondAnd | AndAmp => bool_op(self, Op::And),
            CondOr | OrBar => bool_op(self, Op::Or),
            Xor => bool_op(self, Op::Xor),
            Implies => bool_op(self, Op::Implies),
            Eq | Same => self.eq_term(scope, lhs, rhs),
            NotEq | NotSame => Ok(UT::plain(Term::App(
                Op::Not,
                vec![self.eq_term(scope, lhs, rhs)?.term],
            ))),
            Lt => num_op(self, Op::Lt),
            LtEq => num_op(self, Op::Le),
            Gt => num_op(self, Op::Gt),
            GtEq => num_op(self, Op::Ge),
            Add => num_op(self, Op::Add),
            Sub => num_op(self, Op::Sub),
            // `* /` scale rather than unify: units compose structurally.
            Mul | Div => {
                let l = self.expr(scope, lhs)?;
                let r = self.expr(scope, rhs)?;
                self.demand(&l.term, Demand::Numeric)?;
                self.demand(&r.term, Demand::Numeric)?;
                let (o, unit) = match op {
                    Mul => (Op::Mul, compose_mul(&l.unit, &r.unit)),
                    _ => (Op::Div, compose_div(&l.unit, &r.unit)),
                };
                Ok(UT {
                    term: Term::App(o, vec![l.term, r.term]),
                    unit,
                })
            }
            Pow | Caret => {
                let l = self.expr(scope, lhs)?;
                let r = self.expr(scope, rhs)?;
                let Term::IntLit(k) = r.term else {
                    return bail("exponentiation by a non-constant");
                };
                if !(0..=16).contains(&k) {
                    return bail("exponentiation outside 0..=16");
                }
                self.demand(&l.term, Demand::Numeric)?;
                let mut out = Term::IntLit(1);
                for i in 0..k {
                    out = if i == 0 {
                        l.term.clone()
                    } else {
                        Term::App(Op::Mul, vec![out, l.term.clone()])
                    };
                }
                let unit = match (&l.unit, k) {
                    (None, _) | (_, 0) => None,
                    (Some(u), 1) => Some(u.clone()),
                    (Some(u), k) => Some(UTag {
                        key: format!("({}^{k})", u.key),
                        scale: u.scale.pow_or_approx(k as i32),
                        display: format!("{}**{k}", u.display),
                    }),
                };
                Ok(UT { term: out, unit })
            }
            // Truncated remainder (Rust/evaluator `%` semantics) over
            // integer operands; plain numbers only — a remainder of
            // unit-tagged quantities has no evaluator meaning either.
            Rem => {
                let l = self.expr(scope, lhs)?;
                let r = self.expr(scope, rhs)?;
                if l.unit.is_some() || r.unit.is_some() {
                    return bail("`%` on unit-tagged operands");
                }
                self.demand(&l.term, Demand::Exact(Sort::Int))?;
                self.demand(&r.term, Demand::Exact(Sort::Int))?;
                Ok(UT::plain(Term::App(Op::TRem, vec![l.term, r.term])))
            }
            Range => bail("`..` ranges"),
            // `a ?? b`: a left side the evaluator proves to be exactly
            // null yields the right side (checked first — the freeing
            // over-approximation would otherwise swallow it); anything
            // else translates the left side, which then denotes a
            // *present* scalar (free variables model existing values —
            // the fragment-wide treatment of multiplicities) and wins.
            NullCoalescing => match self.r.evaluate_in(scope, lhs) {
                Ok(Value::Sequence(s)) if s.is_empty() => self.expr(scope, rhs),
                _ => self.expr(scope, lhs),
            },
        }
    }

    fn eq_term(&mut self, scope: ScopeRef, lhs: &Expr, rhs: &Expr) -> Result<UT, Unsupported> {
        let mut l = self.expr(scope, lhs)?;
        let mut r = self.expr(scope, rhs)?;
        self.unify(&l.term, &r.term)?;
        self.unify_units(&mut l, &mut r)?;
        Ok(UT::plain(Term::App(Op::Eq, vec![l.term, r.term])))
    }

    /// Translate *through* a user-calculation body: arguments translate
    /// in the caller's scope, bind to the declared `in`/`inout`
    /// parameters (positionally or by name), and the body translates in
    /// the calculation's own scope with the bindings shadowing model
    /// names. Unbound parameters must carry defaults (their references
    /// inline like any defined feature) — otherwise the invocation has
    /// no finite meaning here and bails; recursion bails (unbounded
    /// unrolling has no finite translation).
    fn invocation(
        &mut self,
        scope: ScopeRef,
        ty: &TargetRef,
        args: &[Arg],
    ) -> Result<UT, Unsupported> {
        let TargetRef::Name(qn) = ty else {
            return bail("chained function references");
        };
        let display = qn.to_display_string();
        // Kernel Function Library sequence intrinsics: KFL names
        // are *reserved* — dispatched on the invoked name's last segment
        // with positional arguments, before resolution and before any
        // user body, exactly like the evaluator. A shape the table does
        // not admit (named arguments, wrong arity) falls through to the
        // ordinary calculation path.
        let simple = qn
            .segments
            .last()
            .map(|s| s.value.clone())
            .unwrap_or_default();
        if args.iter().all(|a| a.name.is_none()) {
            let exprs: Vec<&Expr> = args.iter().map(|a| &a.value).collect();
            if seq_intrinsic_arity_ok(&simple, exprs.len()) {
                return self.seq_intrinsic(scope, &simple, &exprs, &display);
            }
        }
        let Some(callee) = self.r.resolve_in(scope, qn) else {
            return bail(format!("unresolved function `{display}`"));
        };
        let Some((body_scope, body)) = self.r.calc_body(callee) else {
            // Abstract library functions and bodiless declarations.
            return bail("function invocation over unbound features");
        };
        let params = self.r.calc_params(callee);
        // Arguments translate in the caller's scope *before* any
        // parameter binding is visible (applicative order).
        let mut bindings: Vec<(String, Binding)> = Vec::with_capacity(args.len());
        let mut pos = 0usize;
        for a in args {
            let t = self.expr(scope, &a.value)?;
            let name = match &a.name {
                Some(n) => n
                    .segments
                    .last()
                    .map(|s| s.value.clone())
                    .unwrap_or_default(),
                None => {
                    let p = params.get(pos).cloned().unwrap_or_default();
                    pos += 1;
                    p
                }
            };
            bindings.push((name, Binding::Scalar(t.term, t.unit)));
        }
        // Every unbound parameter must have its own (default) value —
        // otherwise two call sites would share one free variable, which
        // could prove a spurious UNSAT.
        for p in &params {
            if bindings.iter().any(|(n, _)| n == p) {
                continue;
            }
            let has_default = self
                .r
                .owned_member(callee, p)
                .and_then(|m| self.r.value_expr(m))
                .is_some();
            if !has_default {
                return bail(format!("invocation of `{display}` leaves `{p}` unbound"));
            }
        }
        if !self.inlining_calcs.insert(callee) {
            return bail(format!("recursive calculation `{display}`"));
        }
        let depth = self.env.len();
        self.env.extend(bindings);
        let out = self.expr(body_scope, &body);
        self.env.truncate(depth);
        self.inlining_calcs.remove(&callee);
        out
    }

    // -- sequence-argument intrinsics ----------------------------------------

    /// Lower an expression to a vector of scalar terms when its arity is
    /// statically known: sequence expressions flatten (KerML sequences
    /// are flat), `null` is empty, and a reference to a feature with a
    /// value expression recurses into it (cycle-guarded, like
    /// [`Self::feature_term`]). A valueless reference contributes one
    /// scalar exactly when it is declared scalar — no explicit
    /// multiplicity (the source default) or an explicit `[1]`, the
    /// fragment-wide one-existing-value treatment; any other declared
    /// multiplicity has no static arity here (bounded expansion is the
    /// quantifier path). Anything else contributes one scalar via the ordinary
    /// expression path.
    fn seq_terms(
        &mut self,
        scope: ScopeRef,
        e: &Expr,
        out: &mut Vec<UT>,
    ) -> Result<(), Unsupported> {
        match &e.kind {
            ExprKind::Sequence(items) => {
                for i in items {
                    self.seq_terms(scope, i, out)?;
                }
                Ok(())
            }
            ExprKind::Null => Ok(()),
            ExprKind::Ref(qn) => {
                // Parameter bindings shadow model names, as one item.
                if let Some(b) = self.env_binding(qn) {
                    out.push(self.binding_term(b)?);
                    return Ok(());
                }
                let display = qn.to_display_string();
                let Some(elem) = self.r.resolve_in(scope, qn) else {
                    return bail(format!("unresolved reference `{display}`"));
                };
                let Some((own_scope, vexpr)) = self.r.value_expr(elem) else {
                    return match self.r.declared_multiplicity(elem) {
                        None | Some((1.0, 1.0)) => {
                            out.push(self.feature_term(elem, None, display)?);
                            Ok(())
                        }
                        Some((lo, hi)) => bail(format!(
                            "a collection `{display}` (multiplicity [{lo}..{hi}]) \
                             with no bound value: arity unknown"
                        )),
                    };
                };
                if !self.inlining.insert(elem) {
                    return bail(format!("cyclic value of `{display}`"));
                }
                let r = self.seq_terms(own_scope, &vexpr, out);
                self.inlining.remove(&elem);
                r
            }
            _ => {
                out.push(self.expr(scope, e)?);
                Ok(())
            }
        }
    }

    /// The one sequence argument of a one-argument intrinsic, lowered.
    fn seq_arg(
        &mut self,
        scope: ScopeRef,
        args: &[&Expr],
        display: &str,
    ) -> Result<Vec<UT>, Unsupported> {
        let [a] = args else {
            return bail(format!("`{display}` with {} arguments", args.len()));
        };
        let mut items = Vec::new();
        self.seq_terms(scope, a, &mut items)?;
        Ok(items)
    }

    /// Kernel Function Library intrinsics over statically-known-arity
    /// sequence arguments, mirroring the evaluator's table: folds build
    /// the finite term directly (`sum` → `+` chain through the same
    /// unit unification as binary `+`; extrema → `ite` chains), counts
    /// fold to constants. Both backends consume the result — the terms
    /// use only fragment ops.
    fn seq_intrinsic(
        &mut self,
        scope: ScopeRef,
        name: &str,
        args: &[&Expr],
        display: &str,
    ) -> Result<UT, Unsupported> {
        match name {
            "sum" => {
                let items = self.seq_arg(scope, args, display)?;
                self.fold_additive(items)
            }
            "product" => {
                let items = self.seq_arg(scope, args, display)?;
                self.fold_product(items)
            }
            "size" => {
                let items = self.seq_arg(scope, args, display)?;
                Ok(UT::plain(Term::IntLit(items.len() as i128)))
            }
            "isEmpty" => {
                let items = self.seq_arg(scope, args, display)?;
                Ok(UT::plain(Term::BoolLit(items.is_empty())))
            }
            "notEmpty" => {
                let items = self.seq_arg(scope, args, display)?;
                Ok(UT::plain(Term::BoolLit(!items.is_empty())))
            }
            "head" => {
                let items = self.seq_arg(scope, args, display)?;
                items
                    .into_iter()
                    .next()
                    .ok_or_else(|| Unsupported("`head` of an empty sequence".into()))
            }
            "last" => {
                let mut items = self.seq_arg(scope, args, display)?;
                items
                    .pop()
                    .ok_or_else(|| Unsupported("`last` of an empty sequence".into()))
            }
            // One sequence, or the two-scalar spelling — either way a
            // fold over the flattened elements.
            "max" | "min" => {
                let mut items = Vec::new();
                for a in args {
                    self.seq_terms(scope, a, &mut items)?;
                }
                let cmp = if name == "max" { Op::Ge } else { Op::Le };
                self.fold_extremum(items, cmp, display)
            }
            "abs" => {
                let mut items = self.seq_arg(scope, args, display)?;
                let [x] = items.as_mut_slice() else {
                    return bail("`abs` of a non-scalar");
                };
                self.demand(&x.term, Demand::Numeric)?;
                let term = Term::App(
                    Op::Ite,
                    vec![
                        Term::App(Op::Ge, vec![x.term.clone(), Term::IntLit(0)]),
                        x.term.clone(),
                        Term::App(Op::Neg, vec![x.term.clone()]),
                    ],
                );
                Ok(UT {
                    term,
                    unit: x.unit.clone(),
                })
            }
            _ => bail(format!("intrinsic `{display}`")),
        }
    }

    /// `sum`: pairwise `+` through the same unit unification binary `+`
    /// uses; the empty sum is the plain (unit-agnostic) zero.
    fn fold_additive(&mut self, items: Vec<UT>) -> Result<UT, Unsupported> {
        let mut it = items.into_iter();
        let Some(mut acc) = it.next() else {
            return Ok(UT::plain(Term::IntLit(0)));
        };
        self.demand(&acc.term, Demand::Numeric)?;
        for mut x in it {
            self.demand(&x.term, Demand::Numeric)?;
            let unit = self.unify_units(&mut acc, &mut x)?;
            acc = UT {
                term: Term::App(Op::Add, vec![acc.term, x.term]),
                unit,
            };
        }
        Ok(acc)
    }

    /// `product`: pairwise `*`; units compose structurally like binary
    /// `*`; the empty product is the plain one.
    fn fold_product(&mut self, items: Vec<UT>) -> Result<UT, Unsupported> {
        let mut it = items.into_iter();
        let Some(acc) = it.next() else {
            return Ok(UT::plain(Term::IntLit(1)));
        };
        self.demand(&acc.term, Demand::Numeric)?;
        let mut acc = acc;
        for x in it {
            self.demand(&x.term, Demand::Numeric)?;
            let unit = compose_mul(&acc.unit, &x.unit);
            acc = UT {
                term: Term::App(Op::Mul, vec![acc.term, x.term]),
                unit,
            };
        }
        Ok(acc)
    }

    /// `max`/`min`: pairwise `ite(a ⋛ b, a, b)` with the comparison's
    /// unit unification at each step. Each step's value is named by an
    /// auxiliary variable defined through a side equality, so the next
    /// step references a variable rather than a copy of the whole prefix
    /// (the operand appears in both the condition and a branch): the
    /// fold stays linear in the item count for both backends.
    fn fold_extremum(&mut self, items: Vec<UT>, cmp: Op, display: &str) -> Result<UT, Unsupported> {
        let mut it = items.into_iter();
        let Some(mut acc) = it.next() else {
            return bail(format!("`{display}` of an empty sequence"));
        };
        self.demand(&acc.term, Demand::Numeric)?;
        for (k, mut x) in it.enumerate() {
            self.demand(&x.term, Demand::Numeric)?;
            let unit = self.unify_units(&mut acc, &mut x)?;
            let linked: Vec<usize> = [&acc.term, &x.term]
                .into_iter()
                .filter_map(|t| match t {
                    Term::Var(j) => Some(*j),
                    _ => None,
                })
                .collect();
            let step = Term::App(
                Op::Ite,
                vec![
                    Term::App(cmp, vec![acc.term.clone(), x.term.clone()]),
                    acc.term,
                    x.term,
                ],
            );
            let i = self.aux_var(format!("{display}#{}", k + 1), unit.clone(), &linked);
            self.aux_defs.insert(i, self.side.len());
            self.side.push(Term::App(Op::Eq, vec![Term::Var(i), step]));
            acc = UT {
                term: Term::Var(i),
                unit,
            };
        }
        Ok(acc)
    }

    /// A fresh auxiliary numeric variable standing for a value the
    /// translation names (`display` only seeds its symbol). It carries
    /// the value's unit tag and is unit-linked to the `linked`
    /// variables (the operands of its definition), so a tag arriving
    /// later on either side reaches the other at finalization exactly as
    /// it would through a direct comparison. The caller records the
    /// defining equality.
    fn aux_var(&mut self, display: String, unit: Option<UTag>, linked: &[usize]) -> usize {
        let i = self.displays.len();
        self.displays.push(display);
        self.states.push(SortState::Numeric);
        self.var_units.push(unit);
        self.aux.push(true);
        for &j in linked {
            self.pending_unit_eq.push((i, j));
        }
        i
    }

    // -- finite quantifier expansion -----------------------------------------

    /// `target->Fn …` — quantifiers with a lambda body expand finitely;
    /// list-argument arrows are the invocation spelling of the sequence
    /// intrinsics (the target is the first argument, exactly the
    /// evaluator's arrow ≡ invocation rule).
    fn arrow(
        &mut self,
        scope: ScopeRef,
        target: &Expr,
        ty: &TargetRef,
        args: &ArrowArgs,
    ) -> Result<UT, Unsupported> {
        let TargetRef::Name(qn) = ty else {
            return bail("chained function references");
        };
        let simple = qn
            .segments
            .last()
            .map(|s| s.value.clone())
            .unwrap_or_default();
        let display = qn.to_display_string();
        match args {
            ArrowArgs::Body(body) if simple == "forAll" || simple == "exists" => {
                self.quantifier(scope, simple == "forAll", target, body)
            }
            ArrowArgs::List(list) if list.iter().all(|a| a.name.is_none()) => {
                let mut exprs: Vec<&Expr> = vec![target];
                exprs.extend(list.iter().map(|a| &a.value));
                if seq_intrinsic_arity_ok(&simple, exprs.len()) {
                    self.seq_intrinsic(scope, &simple, &exprs, &display)
                } else {
                    bail("function invocation over unbound features")
                }
            }
            _ => bail(format!(
                "control function `{display}` over unbound features"
            )),
        }
    }

    /// `coll->forAll {in w; body}` / `->exists`: expand over a
    /// statically-known collection — a conjunction (disjunction) of the
    /// body translated once per member, the lambda parameter bound to
    /// that member. The empty collection is `true` (`false`).
    fn quantifier(
        &mut self,
        scope: ScopeRef,
        forall: bool,
        target: &Expr,
        body: &Expr,
    ) -> Result<UT, Unsupported> {
        // Lambda parts, exactly the evaluator's `apply_lambda` reading:
        // direction members are parameters, the Result member is the body.
        let ExprKind::Body { members } = &body.kind else {
            return bail("a quantifier without a lambda body");
        };
        let mut param: Option<String> = None;
        let mut result: Option<&Expr> = None;
        for m in members {
            match &m.kind {
                MemberKind::Usage(u) if u.prefix.direction.is_some() => {
                    if param.is_some() {
                        return bail("a quantifier lambda with several parameters");
                    }
                    param = u.declaration.id.name.as_ref().map(|n| n.value.clone());
                }
                MemberKind::Result(e) => result = Some(e),
                _ => return bail("a quantifier lambda with local members"),
            }
        }
        let Some(result) = result else {
            return bail("a lambda body without a result");
        };
        let bindings = self.collection_bindings(scope, target)?;
        let mut acc: Option<Term> = None;
        for b in bindings {
            let depth = self.env.len();
            if let Some(p) = &param {
                self.env.push((p.clone(), b));
            }
            let t = self.expr(scope, result);
            self.env.truncate(depth);
            let t = t?;
            self.demand(&t.term, Demand::Bool)?;
            acc = Some(match acc {
                None => t.term,
                Some(a) => Term::App(if forall { Op::And } else { Op::Or }, vec![a, t.term]),
            });
        }
        Ok(UT::plain(acc.unwrap_or(Term::BoolLit(forall))))
    }

    /// The members a quantifier ranges over. An *unbound* feature with an
    /// exact declared multiplicity `[n]` (≤ the skolem cap; own
    /// declaration, or borrowed one hop from a redefinition target)
    /// skolemizes into `n` anonymous instances — sound for `forAll` /
    /// `exists` because quantified bodies are aliasing-insensitive.
    /// Everything else lowers through [`Self::seq_terms`] as scalars.
    fn collection_bindings(
        &mut self,
        scope: ScopeRef,
        target: &Expr,
    ) -> Result<Vec<Binding>, Unsupported> {
        if let ExprKind::Ref(qn) = &target.kind {
            if self.env_binding(qn).is_none() {
                if let Some(elem) = self.r.resolve_in(scope, qn) {
                    if self.r.value_expr(elem).is_none() {
                        if let Some((lo, hi)) = self.multiplicity_with_hop(elem) {
                            let display = qn.to_display_string();
                            if lo == hi && lo >= 0.0 && lo.fract() == 0.0 {
                                let n = lo as usize;
                                if n > SKOLEM_CAP {
                                    return bail(format!(
                                        "a collection `{display}` with multiplicity \
                                         [{n}] over the expansion cap ({SKOLEM_CAP})"
                                    ));
                                }
                                let ty = self.r.typings(elem).into_iter().next();
                                return Ok((1..=n)
                                    .map(|k| Binding::Instance {
                                        feature: elem,
                                        ty,
                                        path: format!("{display}#{k}"),
                                    })
                                    .collect());
                            }
                            if hi != 1.0 {
                                return bail(format!(
                                    "a collection `{display}` (multiplicity \
                                     [{lo}..{hi}]) without static arity"
                                ));
                            }
                        }
                    }
                }
            }
        }
        let mut items = Vec::new();
        self.seq_terms(scope, target, &mut items)?;
        Ok(items
            .into_iter()
            .map(|ut| Binding::Scalar(ut.term, ut.unit))
            .collect())
    }

    /// The element's evaluated exact multiplicity bounds: its own
    /// explicit declaration, else (one hop) a redefinition target's —
    /// the same borrow the semantic checks use for undeclared
    /// characteristics of redefining features.
    fn multiplicity_with_hop(&mut self, elem: ElementRef) -> Option<(f64, f64)> {
        if let Some(b) = self.r.declared_multiplicity(elem) {
            return Some(b);
        }
        for t in self.r.redefinition_targets(elem) {
            if let Some(b) = self.r.declared_multiplicity(t) {
                return Some(b);
            }
        }
        None
    }

    /// A per-instance variable of a skolemized collection, keyed by its
    /// display path so the same collection quantified twice shares its
    /// instances. Sorted like `sort_from`'s declaration.
    fn skolem_var(&mut self, sort_from: ElementRef, display: String) -> Result<UT, Unsupported> {
        if let Some(&i) = self.skolem_vars.get(&display) {
            return Ok(UT::plain(Term::Var(i)));
        }
        let (state, lower) = self.declared_sort(sort_from)?;
        let i = self.displays.len();
        self.skolem_vars.insert(display.clone(), i);
        self.displays.push(display);
        self.states.push(state);
        self.var_units.push(None);
        self.aux.push(false);
        if let Some(lo) = lower {
            self.side
                .push(Term::App(Op::Ge, vec![Term::Var(i), Term::IntLit(lo)]));
        }
        Ok(UT::plain(Term::Var(i)))
    }

    /// A leaf reached through a skolem instance. Instance-independent
    /// leaves (enum literals) translate normally. A *closed* value
    /// expression — one the evaluator settles with no unbound references
    /// — inlines shared (it is the same constant for every instance); an
    /// *open* one must not (shared inlining would equate the instances'
    /// sibling features, a spurious-UNSAT risk), so it falls to a
    /// per-instance free variable recorded as an over-approximation,
    /// exactly [`Self::feature_term`]'s out-of-fragment fallback.
    fn skolem_leaf(
        &mut self,
        elem: ElementRef,
        ctx: Option<ScopeRef>,
        display: String,
    ) -> Result<UT, Unsupported> {
        if self.tables.lit_to_enum.contains_key(&elem) || self.r.is_enum_value(elem) {
            return self.feature_term(elem, ctx, display);
        }
        if let Some((own_scope, vexpr)) = self.r.value_expr(elem) {
            let scope = ctx.unwrap_or(own_scope);
            let closed = self.r.evaluate_in(scope, &vexpr).is_ok_and(|v| {
                !matches!(
                    v,
                    Value::Element(_)
                        | Value::Unbound(_)
                        | Value::UnboundMember(_)
                        | Value::Indeterminate
                )
            });
            if closed && self.inlining.insert(elem) {
                let out = self.expr(scope, &vexpr);
                self.inlining.remove(&elem);
                if let Ok(t) = out {
                    return Ok(t);
                }
            }
            if !self.approx.contains(&display) {
                self.approx.push(display.clone());
            }
        }
        self.skolem_var(elem, display)
    }

    /// A chain whose spine roots at a skolem-instance lambda parameter:
    /// members resolve statically from the instance's type, minting the
    /// per-instance leaf. `Ok(None)` = not such a chain (the ordinary
    /// path applies).
    fn instance_chain(&mut self, whole: &Expr) -> Result<Option<UT>, Unsupported> {
        let mut links: Vec<&QualifiedName> = Vec::new();
        let mut cur = whole;
        let (ty, path) = loop {
            match &cur.kind {
                ExprKind::ChainStep { target, member } => {
                    let TargetRef::Name(qn) = member else {
                        return Ok(None);
                    };
                    links.push(qn);
                    cur = target;
                }
                ExprKind::Ref(qn) => match self.env_binding(qn) {
                    Some(Binding::Instance { ty, path, .. }) => break (ty, path),
                    _ => return Ok(None),
                },
                _ => return Ok(None),
            }
        };
        links.reverse();
        let Some(ty) = ty else {
            return bail(format!("an untyped skolemized collection `{path}`"));
        };
        let display = {
            let tail: Vec<String> = links.iter().map(|q| q.to_display_string()).collect();
            format!("{path}.{}", tail.join("."))
        };
        let mut cur_elem = ty;
        for (i, qn) in links.iter().enumerate() {
            let Some((hit, s)) = self.r.member_of(cur_elem, qn) else {
                return bail(format!("unresolved reference `{display}`"));
            };
            if i + 1 == links.len() {
                return self.skolem_leaf(hit, s, display).map(Some);
            }
            cur_elem = hit;
        }
        unreachable!("a chain has at least one link")
    }

    // -- references and free variables ---------------------------------------

    /// The environment binding of a single-segment name, if any.
    fn env_binding(&self, qn: &QualifiedName) -> Option<Binding> {
        if qn.segments.len() != 1 || qn.is_global {
            return None;
        }
        let name = &qn.segments[0].value;
        self.env
            .iter()
            .rev()
            .find(|(n, _)| n == name)
            .map(|(_, b)| b.clone())
    }

    /// A binding used as a value: scalars pass through; a skolem
    /// instance mints its per-instance variable, sorted like the
    /// collection feature (bool/enum/variant collections — a
    /// non-scalar-sorted collection bails here).
    fn binding_term(&mut self, b: Binding) -> Result<UT, Unsupported> {
        match b {
            Binding::Scalar(t, u) => Ok(UT { term: t, unit: u }),
            Binding::Instance { feature, path, .. } => self.skolem_leaf(feature, None, path),
        }
    }

    fn ref_term(&mut self, scope: ScopeRef, qn: &QualifiedName) -> Result<UT, Unsupported> {
        // Calculation/lambda parameters shadow model names (dynamic
        // extent, like the evaluator's environment).
        if let Some(b) = self.env_binding(qn) {
            return self.binding_term(b);
        }
        let display = qn.to_display_string();
        let Some(elem) = self.r.resolve_in(scope, qn) else {
            return bail(format!("unresolved reference `{display}`"));
        };
        self.feature_term(elem, None, display)
    }

    fn chain(
        &mut self,
        scope: ScopeRef,
        whole: &Expr,
        target: &Expr,
        member: &TargetRef,
    ) -> Result<UT, Unsupported> {
        let TargetRef::Name(qn) = member else {
            return bail("chained chain members");
        };
        // A spine rooted at a skolem-instance lambda parameter resolves
        // statically — the evaluator below cannot see the binding.
        if let Some(out) = self.instance_chain(whole)? {
            return Ok(out);
        }
        let tval = self
            .r
            .evaluate_in(scope, target)
            .map_err(|e| Unsupported(format!("chain target: {e}")))?;
        if matches!(tval, Value::Indeterminate | Value::UnboundMember(_)) {
            // A nested unknown member has no concrete featuring context.
            // Do not identify distinct receiver paths by their shared
            // declaration, or inline defaults from that declaration.
            return bail("a chain through an unknown receiver member");
        }
        let unbound = matches!(&tval, Value::Unbound(t) if self.r.is_reference_feature(*t));
        let (Value::Element(t) | Value::Unbound(t)) = tval else {
            return bail("a chain whose target is not a model element");
        };
        let Some((hit, sub)) = self.r.member_of(t, qn) else {
            return bail(format!("unresolved reference `{}`", display_expr(whole)));
        };
        if unbound {
            // Closed results were already handled by `fold`, which uses
            // the evaluator's receiver-aware default rules. An unknown
            // fixed formula may depend on sibling defaults too; inlining
            // it without that context would invent a definitive value.
            let display = display_expr(whole);
            if self.r.has_own_fixed_value(hit) && !self.approx.contains(&display) {
                self.approx.push(display.clone());
            }
            return self.var(hit, sub, display);
        }
        self.feature_term(hit, sub, display_expr(whole))
    }

    /// A resolved feature as a term: enum literal, inlined definition, or
    /// free variable. `ctx` is the featuring context of a chain step — it
    /// both distinguishes the unknown (car1.mass ≠ car2.mass) and overrides
    /// the scope its defining expression resolves from (one level, exactly
    /// like the evaluator).
    fn feature_term(
        &mut self,
        elem: ElementRef,
        ctx: Option<ScopeRef>,
        display: String,
    ) -> Result<UT, Unsupported> {
        if self.tables.lit_to_enum.contains_key(&elem) {
            return self.enum_term(elem).map(UT::plain);
        }
        if self.r.is_enum_value(elem) {
            return bail(format!("variant value `{display}`"));
        }
        if let Some((own_scope, vexpr)) = self.r.value_expr(elem) {
            if !self.inlining.insert(elem) {
                return bail(format!("cyclic value of `{display}`"));
            }
            let out = self.expr(ctx.unwrap_or(own_scope), &vexpr);
            self.inlining.remove(&elem);
            match out {
                Ok(t) => return Ok(t),
                Err(_) => {
                    // The definition is outside the fragment: treat the
                    // feature as free but remember the over-approximation.
                    if !self.approx.contains(&display) {
                        self.approx.push(display.clone());
                    }
                }
            }
        }
        self.var(elem, ctx, display)
    }

    fn var(
        &mut self,
        elem: ElementRef,
        ctx: Option<ScopeRef>,
        display: String,
    ) -> Result<UT, Unsupported> {
        if let Some(&i) = self.var_keys.get(&(elem, ctx)) {
            return Ok(UT::plain(Term::Var(i)));
        }
        let (state, lower) = self.declared_sort(elem)?;
        let i = self.displays.len();
        self.var_keys.insert((elem, ctx), i);
        self.displays.push(display);
        self.states.push(state);
        self.var_units.push(None);
        self.aux.push(false);
        if let Some(lo) = lower {
            self.side
                .push(Term::App(Op::Ge, vec![Term::Var(i), Term::IntLit(lo)]));
        }
        Ok(UT::plain(Term::Var(i)))
    }

    // -- unit discipline -------------------------------------------------------

    /// The effective unit of a term: an explicit tag has already been
    /// consumed by the caller; here only variables carry latent tags.
    fn term_unit(&self, t: &Term) -> Option<UTag> {
        match t {
            Term::Var(i) => self.var_units[*i].clone(),
            _ => None,
        }
    }

    /// Push a unit tag down a term: variables take (or check) the tag,
    /// additive structure recurses, anything else stops (scaling and
    /// literals are unit-agnostic).
    /// Demand that `t` (an additive/conditional subterm) denote a value
    /// in `u`. An untagged variable takes the tag; a variable already
    /// tagged in the *same dimension* at a different scale converts at
    /// this occurrence — the variable keeps its own unit (and its
    /// witness prints in it), the occurrence rewrites to
    /// `var × (scale_var / scale_u)` — mirroring the evaluator's
    /// measurement-reference conversion. A different dimension bails.
    fn demand_unit(&mut self, t: &mut Term, u: &UTag) -> Result<(), Unsupported> {
        match t {
            Term::Var(i) => {
                let i = *i;
                match &self.var_units[i] {
                    None => {
                        self.var_units[i] = Some(u.clone());
                        // An auxiliary's tag reaches the value it names,
                        // exactly as the tag would have reached that value
                        // spelled in place.
                        let Some(&k) = self.aux_defs.get(&i) else {
                            return Ok(());
                        };
                        let mut def = std::mem::replace(&mut self.side[k], Term::BoolLit(true));
                        let out = match &mut def {
                            Term::App(Op::Eq, args) => self.demand_unit(&mut args[1], u),
                            _ => Ok(()),
                        };
                        self.side[k] = def;
                        out
                    }
                    Some(v) if v == u => Ok(()),
                    Some(v) if v.key == u.key => {
                        let Some(ratio) = v.scale.div(&u.scale) else {
                            return bail("a zero unit scale");
                        };
                        *t = Term::App(Op::Mul, vec![Term::Var(i), Term::RealLit(ratio)]);
                        Ok(())
                    }
                    Some(v) => bail(format!(
                        "`{}` is used in `{}` and `{}` (no unit conversion)",
                        self.displays[i], v.display, u.display
                    )),
                }
            }
            Term::App(Op::Add | Op::Sub | Op::Neg, args) => {
                for a in args {
                    self.demand_unit(a, u)?;
                }
                Ok(())
            }
            Term::App(Op::Ite, args) => {
                let mut it = args.iter_mut().skip(1);
                let then_arm = it.next().expect("ite arity");
                let else_arm = it.next().expect("ite arity");
                self.demand_unit(then_arm, u)?;
                self.demand_unit(else_arm, u)
            }
            _ => Ok(()),
        }
    }

    /// Unify the units of two operands (comparison, equality, `+`, `-`,
    /// conditional branches): equal tags pass, one-sided tags propagate
    /// onto the untagged side's variables, two different tags bail.
    fn unify_units(&mut self, a: &mut UT, b: &mut UT) -> Result<Option<UTag>, Unsupported> {
        let ua = a.unit.clone().or_else(|| self.term_unit(&a.term));
        let ub = b.unit.clone().or_else(|| self.term_unit(&b.term));
        match (ua, ub) {
            (Some(u), Some(v)) if u == v => Ok(Some(u)),
            // Same dimension, different scale: *convert* — rescale the
            // right term into the left's unit (mirroring the
            // evaluator's measurement-reference conversion).
            (Some(u), Some(v)) if u.key == v.key => {
                let Some(ratio) = v.scale.div(&u.scale) else {
                    return bail("a zero unit scale");
                };
                b.term = Term::App(
                    Op::Mul,
                    vec![
                        std::mem::replace(&mut b.term, Term::BoolLit(false)),
                        Term::RealLit(ratio),
                    ],
                );
                b.unit = Some(u.clone());
                Ok(Some(u))
            }
            (Some(u), Some(v)) => bail(format!(
                "mixed measurement units `{}` and `{}` (no unit conversion)",
                u.display, v.display
            )),
            // A unit-tagged side against an untagged side with *no
            // variables* is a plain number against a quantity — the
            // evaluator calls that a type error, so deciding it here
            // (constants would fold and "prove" UNSAT) would be unsound.
            // With variables present, the tag propagates onto them.
            (Some(u), None) if !has_var(&b.term) => bail(format!(
                "a plain constant against a quantity in `{}` (no unit conversion)",
                u.display
            )),
            (None, Some(u)) if !has_var(&a.term) => bail(format!(
                "a plain constant against a quantity in `{}` (no unit conversion)",
                u.display
            )),
            (Some(u), None) => {
                self.demand_unit(&mut b.term, &u)?;
                Ok(Some(u))
            }
            (None, Some(u)) => {
                self.demand_unit(&mut a.term, &u)?;
                Ok(Some(u))
            }
            (None, None) => {
                // Link two still-untagged variables so a later tag on one
                // reaches the other.
                if let (Term::Var(i), Term::Var(j)) = (&a.term, &b.term) {
                    self.pending_unit_eq.push((*i, *j));
                }
                Ok(None)
            }
        }
    }

    /// Walk the feature's explicit typings/specializations upward looking
    /// for a scalar type name or an enumeration definition.
    fn declared_sort(&mut self, e: ElementRef) -> Result<(SortState, Option<i128>), Unsupported> {
        let mut queue: VecDeque<ElementRef> = self.r.explicit_supertypes(e).into();
        let mut seen: HashSet<ElementRef> = queue.iter().copied().collect();
        let mut steps = 0;
        while let Some(t) = queue.pop_front() {
            steps += 1;
            if steps > 64 {
                break;
            }
            if self.r.element_type(t) == "EnumerationDefinition"
                && self.tables.enum_lits.contains_key(&t)
            {
                let idx = self.intern_enum(t)?;
                return Ok((SortState::Fixed(Sort::Enum(idx)), None));
            }
            let name = self.r.element_name(t).map(str::to_string);
            match name.as_deref() {
                Some("Boolean") => return Ok((SortState::Fixed(Sort::Bool), None)),
                Some("Integer") => return Ok((SortState::Fixed(Sort::Int), None)),
                Some("Natural") => return Ok((SortState::Fixed(Sort::Int), Some(0))),
                Some("Positive") => return Ok((SortState::Fixed(Sort::Int), Some(1))),
                Some("Real" | "Rational" | "Number" | "NumericalValue") => {
                    return Ok((SortState::Fixed(Sort::Real), None));
                }
                Some("String") => return Ok((SortState::Fixed(Sort::Str), None)),
                _ => {}
            }
            for s in self.r.explicit_supertypes(t) {
                if seen.insert(s) {
                    queue.push_back(s);
                }
            }
        }
        Ok((SortState::Unknown, None))
    }

    fn enum_term(&mut self, lit: ElementRef) -> Result<Term, Unsupported> {
        let def = self.tables.lit_to_enum[&lit];
        let idx = self.intern_enum(def)?;
        Ok(Term::EnumLit(idx, self.tables.lit_pos[&lit]))
    }

    fn intern_enum(&mut self, def: ElementRef) -> Result<usize, Unsupported> {
        if let Some(&i) = self.enum_index.get(&def) {
            return Ok(i);
        }
        if self.tables.enum_lits[&def].is_empty() {
            return bail("an enumeration without literals");
        }
        let i = self.enum_defs.len();
        self.enum_defs.push(def);
        self.enum_index.insert(def, i);
        Ok(i)
    }

    // -- sort discipline -----------------------------------------------------

    /// The demand a term's shape imposes in an equality, if determinable.
    fn kind_of(&self, t: &Term) -> Option<Demand> {
        match t {
            Term::BoolLit(_) => Some(Demand::Bool),
            Term::IntLit(_) | Term::RealLit(_) => Some(Demand::Numeric),
            Term::StrLit(_) => Some(Demand::Exact(Sort::Str)),
            Term::EnumLit(s, _) => Some(Demand::Exact(Sort::Enum(*s))),
            Term::Var(i) => match self.states[*i] {
                SortState::Unknown => None,
                SortState::Numeric => Some(Demand::Numeric),
                SortState::Fixed(Sort::Bool) => Some(Demand::Bool),
                SortState::Fixed(Sort::Int | Sort::Real) => Some(Demand::Numeric),
                SortState::Fixed(s @ (Sort::Enum(_) | Sort::Str)) => Some(Demand::Exact(s)),
            },
            Term::App(op, args) => match op {
                Op::And
                | Op::Or
                | Op::Xor
                | Op::Implies
                | Op::Not
                | Op::Eq
                | Op::Lt
                | Op::Le
                | Op::Gt
                | Op::Ge => Some(Demand::Bool),
                Op::Add | Op::Sub | Op::Mul | Op::Div | Op::Neg | Op::TRem => Some(Demand::Numeric),
                Op::Ite => self.kind_of(&args[1]).or_else(|| self.kind_of(&args[2])),
            },
        }
    }

    /// Impose a sort demand on a term (recursing into `ite` branches).
    fn demand(&mut self, t: &Term, d: Demand) -> Result<(), Unsupported> {
        match t {
            Term::Var(i) => self.demand_var(*i, d),
            Term::App(Op::Ite, args) => {
                self.demand(&args[1], d)?;
                self.demand(&args[2], d)
            }
            _ => match (self.kind_of(t), d) {
                (Some(Demand::Bool), Demand::Bool | Demand::Exact(Sort::Bool)) => Ok(()),
                (Some(Demand::Numeric), Demand::Numeric)
                | (Some(Demand::Numeric), Demand::Exact(Sort::Int | Sort::Real)) => Ok(()),
                (Some(Demand::Exact(a)), Demand::Exact(b)) if a == b => Ok(()),
                _ => bail("mixed types in an expression"),
            },
        }
    }

    fn demand_var(&mut self, i: usize, d: Demand) -> Result<(), Unsupported> {
        let conflict = || {
            Unsupported(format!(
                "conflicting type requirements on `{}`",
                self.displays[i]
            ))
        };
        let state = self.states[i];
        let next = match (state, d) {
            (SortState::Unknown, Demand::Bool) => SortState::Fixed(Sort::Bool),
            (SortState::Unknown, Demand::Numeric) => SortState::Numeric,
            (SortState::Unknown, Demand::Exact(s)) => SortState::Fixed(s),
            (SortState::Numeric, Demand::Numeric) => state,
            (SortState::Numeric, Demand::Exact(s @ (Sort::Int | Sort::Real))) => {
                SortState::Fixed(s)
            }
            (SortState::Fixed(Sort::Bool), Demand::Bool | Demand::Exact(Sort::Bool)) => state,
            (
                SortState::Fixed(Sort::Int | Sort::Real),
                Demand::Numeric | Demand::Exact(Sort::Int | Sort::Real),
            ) => state,
            (SortState::Fixed(a @ (Sort::Enum(_) | Sort::Str)), Demand::Exact(b)) if a == b => {
                state
            }
            _ => return Err(conflict()),
        };
        self.states[i] = next;
        Ok(())
    }

    /// Sort-unify the two sides of an equality or conditional.
    fn unify(&mut self, a: &Term, b: &Term) -> Result<(), Unsupported> {
        match (self.kind_of(a), self.kind_of(b)) {
            (Some(ka), Some(kb)) => {
                let ok = matches!(
                    (ka, kb),
                    (Demand::Bool, Demand::Bool) | (Demand::Numeric, Demand::Numeric)
                ) || ka == kb;
                if ok {
                    Ok(())
                } else {
                    bail("mixed types in a comparison")
                }
            }
            (Some(k), None) => self.demand(b, k),
            (None, Some(k)) => self.demand(a, k),
            (None, None) => match (a, b) {
                (Term::Var(i), Term::Var(j)) => {
                    self.pending_eq.push((*i, *j));
                    Ok(())
                }
                _ => bail("a comparison whose types cannot be inferred"),
            },
        }
    }

    // -- finalization ----------------------------------------------------------

    fn finish(mut self) -> Result<Finished, Unsupported> {
        // Propagate pending variable-variable equalities to a fixpoint.
        let mut changed = true;
        while changed {
            changed = false;
            for &(i, j) in &self.pending_eq {
                let (a, b) = (self.states[i], self.states[j]);
                let merged = match (a, b) {
                    _ if a == b => a,
                    (SortState::Unknown, s) | (s, SortState::Unknown) => s,
                    (SortState::Numeric, SortState::Fixed(s @ (Sort::Int | Sort::Real)))
                    | (SortState::Fixed(s @ (Sort::Int | Sort::Real)), SortState::Numeric) => {
                        SortState::Fixed(s)
                    }
                    (SortState::Fixed(Sort::Int), SortState::Fixed(Sort::Real))
                    | (SortState::Fixed(Sort::Real), SortState::Fixed(Sort::Int)) => a,
                    _ => return bail("mixed types in a comparison"),
                };
                if merged != a || merged != b {
                    self.states[i] = merged;
                    self.states[j] = merged;
                    changed = true;
                }
            }
        }
        // Propagate unit tags across linked still-untagged variables.
        let mut changed = true;
        while changed {
            changed = false;
            for &(i, j) in &self.pending_unit_eq {
                match (&self.var_units[i], &self.var_units[j]) {
                    (Some(u), Some(v)) if u != v => {
                        return bail(format!(
                            "`{}` and `{}` are compared but live in `{}` and `{}` \
                             (no unit conversion)",
                            self.displays[i], self.displays[j], u.display, v.display
                        ));
                    }
                    (Some(u), None) => {
                        self.var_units[j] = Some(u.clone());
                        changed = true;
                    }
                    (None, Some(v)) => {
                        self.var_units[i] = Some(v.clone());
                        changed = true;
                    }
                    _ => {}
                }
            }
        }
        let mut vars = Vec::with_capacity(self.displays.len());
        for (i, display) in self.displays.iter().enumerate() {
            let sort = match self.states[i] {
                SortState::Fixed(s) => s,
                // Context never pinned it down: `Real` is a sound default
                // for both numeric use and pure-equality use.
                SortState::Numeric | SortState::Unknown => Sort::Real,
            };
            vars.push(VarInfo {
                display: display.clone(),
                sym: format!("v{i}_{}", sanitize(display)),
                sort,
                unit: self.var_units[i].as_ref().map(|u| u.display.clone()),
                aux: self.aux[i],
            });
        }
        let mut enums = Vec::with_capacity(self.enum_defs.len());
        for (k, &def) in self.enum_defs.iter().enumerate() {
            let def_name = self.r.element_name(def).unwrap_or("enum").to_string();
            let lits = &self.tables.enum_lits[&def];
            let mut ctors = Vec::with_capacity(lits.len());
            let mut displays = Vec::with_capacity(lits.len());
            for (j, &lit) in lits.iter().enumerate() {
                let name = self
                    .r
                    .element_name(lit)
                    .unwrap_or("<anonymous>")
                    .to_string();
                ctors.push(format!("E{k}c{j}_{}", sanitize(&name)));
                displays.push(name);
            }
            enums.push(EnumSort {
                sym: format!("E{k}_{}", sanitize(&def_name)),
                ctors,
                displays,
            });
        }
        Ok((vars, enums, self.side, self.approx))
    }
}

/// Does the term contain any solver variable? (Constant-only terms
/// cannot absorb a unit tag.)
fn has_var(t: &Term) -> bool {
    match t {
        Term::Var(_) => true,
        Term::App(_, args) => args.iter().any(has_var),
        _ => false,
    }
}

/// Unit of a product: scalar scaling keeps the tagged side; two tags
/// compose into a canonical (order-independent) key.
fn compose_mul(a: &Option<UTag>, b: &Option<UTag>) -> Option<UTag> {
    match (a, b) {
        (None, None) => None,
        (Some(u), None) | (None, Some(u)) => Some(u.clone()),
        (Some(u), Some(v)) => {
            let (x, y) = if u.key <= v.key { (u, v) } else { (v, u) };
            Some(UTag {
                key: format!("({}*{})", x.key, y.key),
                scale: u.scale.mul(&v.scale),
                display: format!("{}*{}", u.display, v.display),
            })
        }
    }
}

/// Unit of a quotient: same units cancel, a scalar divisor keeps the
/// dividend's unit, otherwise the units compose.
fn compose_div(a: &Option<UTag>, b: &Option<UTag>) -> Option<UTag> {
    match (a, b) {
        (None, None) => None,
        (Some(u), None) => Some(u.clone()),
        (Some(u), Some(v)) if u == v => None,
        (x, Some(v)) => {
            let (nk, nd, ns) = match x {
                Some(u) => (u.key.clone(), u.display.clone(), u.scale.clone()),
                None => ("1".to_string(), "1".to_string(), Rational::one()),
            };
            Some(UTag {
                key: format!("({nk}/{})", v.key),
                scale: ns.div(&v.scale).unwrap_or_else(Rational::one),
                display: format!("{nd}/{}", v.display),
            })
        }
    }
}

/// Source-like spelling of a reference expression, for variable display
/// names and diagnostics.
fn display_expr(e: &Expr) -> String {
    match &e.kind {
        ExprKind::Ref(qn) => qn.to_display_string(),
        ExprKind::ChainStep {
            target,
            member: TargetRef::Name(qn),
        } => format!("{}.{}", display_expr(target), qn.to_display_string()),
        _ => "<expr>".into(),
    }
}

/// SMT-symbol-safe fragment of a display name.
fn sanitize(s: &str) -> String {
    let mut out: String = s
        .chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect();
    out.truncate(24);
    out
}
