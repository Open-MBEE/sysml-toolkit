//! Typed SMT term model and SMT-LIB 2 rendering.
//!
//! Terms are built by the translator ([`crate::translate`]) with free-
//! variable sorts still undetermined; rendering happens after sort
//! finalization and inserts `to_real` coercions wherever `Int`- and
//! `Real`-sorted operands mix (SMT-LIB has no implicit numeric widening).

use sysmlv2_model::rational::Rational;

/// SMT sort of a term. `Enum` carries an index into the translation's enum
/// sort table.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Sort {
    Bool,
    Int,
    Real,
    /// SMT-LIB string sort (literals, variables, equality).
    Str,
    Enum(usize),
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Op {
    And,
    Or,
    Xor,
    Implies,
    Not,
    Eq,
    Lt,
    Le,
    Gt,
    Ge,
    Add,
    Sub,
    Mul,
    /// Always real-valued division (both operands coerced to `Real`).
    Div,
    /// Truncated integer remainder — Rust `%` semantics (sign follows the
    /// dividend), matching the evaluator. Integer-sorted operands only.
    TRem,
    Neg,
    Ite,
}

#[derive(Clone, Debug)]
pub(crate) enum Term {
    BoolLit(bool),
    IntLit(i128),
    /// Exact real literal; rendered as `3.0` or `(/ 3.0 10.0)`.
    RealLit(Rational),
    /// String literal (unescaped; rendering doubles interior quotes).
    StrLit(String),
    /// Free variable — index into the translation's variable table.
    Var(usize),
    /// Enum literal: (enum sort index, constructor position).
    EnumLit(usize, usize),
    App(Op, Vec<Term>),
}

/// Collect the free-variable indices a term references (for reporting
/// which features participate in a constraint).
pub(crate) fn term_vars(t: &Term, out: &mut std::collections::BTreeSet<usize>) {
    match t {
        Term::Var(i) => {
            out.insert(*i);
        }
        Term::App(_, args) => {
            for a in args {
                term_vars(a, out);
            }
        }
        _ => {}
    }
}

/// One finite enum sort to declare: `(declare-datatypes ((sym 0)) (((c0)
/// (c1) …)))`. `displays` are the literals' model-facing names, index-
/// aligned with `ctors`.
pub(crate) struct EnumSort {
    pub sym: String,
    pub ctors: Vec<String>,
    pub displays: Vec<String>,
}

/// Everything rendering needs besides the term: finalized variable sorts
/// and symbols, and the enum sort table.
pub(crate) struct RenderCtx<'a> {
    pub var_sorts: &'a [Sort],
    pub var_syms: &'a [String],
    pub enums: &'a [EnumSort],
}

/// A rendered SMT expression with its sort.
type Rendered = (String, Sort);

impl RenderCtx<'_> {
    pub fn sort_name(&self, s: Sort) -> String {
        match s {
            Sort::Bool => "Bool".into(),
            Sort::Int => "Int".into(),
            Sort::Real => "Real".into(),
            Sort::Str => "String".into(),
            Sort::Enum(i) => self.enums[i].sym.clone(),
        }
    }

    /// Render to an SMT-LIB expression. Errors indicate a translator bug
    /// (sort discipline is enforced during translation) and surface as an
    /// `Unknown` outcome rather than a panic.
    pub fn render(&self, t: &Term) -> Result<Rendered, String> {
        match t {
            Term::BoolLit(b) => Ok((b.to_string(), Sort::Bool)),
            Term::IntLit(i) => Ok((render_int(*i), Sort::Int)),
            Term::RealLit(r) => Ok((render_real(r), Sort::Real)),
            Term::StrLit(s) => Ok((format!("\"{}\"", s.replace('"', "\"\"")), Sort::Str)),
            Term::Var(i) => Ok((self.var_syms[*i].clone(), self.var_sorts[*i])),
            Term::EnumLit(s, c) => Ok((self.enums[*s].ctors[*c].clone(), Sort::Enum(*s))),
            Term::App(op, args) => {
                let parts: Vec<Rendered> = args
                    .iter()
                    .map(|a| self.render(a))
                    .collect::<Result<_, _>>()?;
                self.apply(*op, parts)
            }
        }
    }

    fn apply(&self, op: Op, parts: Vec<Rendered>) -> Result<Rendered, String> {
        use Op::*;
        let smt = |head: &str, args: &[String]| format!("({head} {})", args.join(" "));
        match op {
            And | Or | Xor | Implies | Not => {
                let head = match op {
                    And => "and",
                    Or => "or",
                    Xor => "xor",
                    Implies => "=>",
                    _ => "not",
                };
                for (_, s) in &parts {
                    if *s != Sort::Bool {
                        return Err(format!("non-boolean operand to `{head}`"));
                    }
                }
                let args: Vec<String> = parts.into_iter().map(|(t, _)| t).collect();
                Ok((smt(head, &args), Sort::Bool))
            }
            Eq => {
                let (a, b) = two(parts)?;
                let (a, b, _) = unify_pair(a, b)?;
                Ok((smt("=", &[a, b]), Sort::Bool))
            }
            Lt | Le | Gt | Ge => {
                let head = match op {
                    Lt => "<",
                    Le => "<=",
                    Gt => ">",
                    _ => ">=",
                };
                let (a, b) = two(parts)?;
                let (a, b) = unify_numeric(a, b)?;
                Ok((smt(head, &[a.0, b.0]), Sort::Bool))
            }
            Add | Sub | Mul => {
                let head = match op {
                    Add => "+",
                    Sub => "-",
                    _ => "*",
                };
                let (a, b) = two(parts)?;
                let (a, b) = unify_numeric(a, b)?;
                let sort = a.1;
                Ok((smt(head, &[a.0, b.0]), sort))
            }
            Div => {
                let (a, b) = two(parts)?;
                let a = coerce_real(a)?;
                let b = coerce_real(b)?;
                Ok((smt("/", &[a, b]), Sort::Real))
            }
            TRem => {
                // Truncated remainder over SMT's Euclidean `mod`:
                // sign(a) * (|a| mod |b|), matching Rust/evaluator `%`.
                let (a, b) = two(parts)?;
                if a.1 != Sort::Int || b.1 != Sort::Int {
                    return Err("`%` on non-integer operands".into());
                }
                let (a, b) = (a.0, b.0);
                let abs_b = format!("(ite (>= {b} 0) {b} (- {b}))");
                let m_pos = format!("(mod {a} {abs_b})");
                let m_neg = format!("(- (mod (- {a}) {abs_b}))");
                Ok((format!("(ite (>= {a} 0) {m_pos} {m_neg})"), Sort::Int))
            }
            Neg => {
                let (t, s) = parts.into_iter().next().ok_or("missing operand")?;
                if !matches!(s, Sort::Int | Sort::Real) {
                    return Err("non-numeric operand to unary `-`".into());
                }
                Ok((smt("-", &[t]), s))
            }
            Ite => {
                let mut it = parts.into_iter();
                let (c, cs) = it.next().ok_or("missing condition")?;
                let a = it.next().ok_or("missing branch")?;
                let b = it.next().ok_or("missing branch")?;
                if cs != Sort::Bool {
                    return Err("non-boolean `if` condition".into());
                }
                let (a, b, sort) = unify_pair(a, b)?;
                Ok((smt("ite", &[c, a, b]), sort))
            }
        }
    }
}

fn two(parts: Vec<Rendered>) -> Result<(Rendered, Rendered), String> {
    let mut it = parts.into_iter();
    let a = it.next().ok_or("missing operand")?;
    let b = it.next().ok_or("missing operand")?;
    Ok((a, b))
}

fn coerce_real((t, s): Rendered) -> Result<String, String> {
    match s {
        Sort::Real => Ok(t),
        Sort::Int => Ok(format!("(to_real {t})")),
        _ => Err("non-numeric operand".into()),
    }
}

/// Coerce a numeric pair to a common sort.
fn unify_numeric(a: Rendered, b: Rendered) -> Result<(Rendered, Rendered), String> {
    match (a.1, b.1) {
        (Sort::Int, Sort::Int) | (Sort::Real, Sort::Real) => Ok((a, b)),
        (Sort::Int, Sort::Real) => Ok(((coerce_real(a)?, Sort::Real), b)),
        (Sort::Real, Sort::Int) => Ok((a, (coerce_real(b)?, Sort::Real))),
        _ => Err("non-numeric operand to a numeric operator".into()),
    }
}

/// Unify an equality/ite pair: numerics coerce, other sorts must match.
/// Returns the two rendered terms and their common sort.
fn unify_pair(a: Rendered, b: Rendered) -> Result<(String, String, Sort), String> {
    match (a.1, b.1) {
        (Sort::Bool, Sort::Bool) => Ok((a.0, b.0, Sort::Bool)),
        (Sort::Enum(x), Sort::Enum(y)) if x == y => Ok((a.0, b.0, Sort::Enum(x))),
        (Sort::Str, Sort::Str) => Ok((a.0, b.0, Sort::Str)),
        (Sort::Int | Sort::Real, Sort::Int | Sort::Real) => {
            let (a, b) = unify_numeric(a, b)?;
            let sort = a.1;
            Ok((a.0, b.0, sort))
        }
        _ => Err("sort mismatch in equality".into()),
    }
}

pub(crate) fn render_int(i: i128) -> String {
    if i < 0 {
        format!("(- {})", i.unsigned_abs())
    } else {
        i.to_string()
    }
}

/// Render an exact rational as an SMT-LIB real literal: `3.0`,
/// `(/ 3.0 10.0)`, or either inside `(- …)` when negative.
pub(crate) fn render_real(r: &Rational) -> String {
    let (n, d) = r.abs().to_string_parts();
    let body = if d == "1" {
        format!("{n}.0")
    } else {
        format!("(/ {n}.0 {d}.0)")
    };
    if r.is_negative() {
        format!("(- {body})")
    } else {
        body
    }
}
