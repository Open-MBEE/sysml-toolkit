//! SMT solving for SysML v2 / KerML constraints.
//!
//! Where the checking stage (`sysmlv2-model::check::check_constraints`)
//! evaluates each constraint body to a satisfied/violated/undecided
//! verdict, this crate takes the *undecided* ones — typically comparisons
//! over unbound features — translates the decidable fragment (linear and
//! nonlinear arithmetic over reals and integers, booleans, enumerations)
//! to SMT-LIB 2, and asks Z3:
//!
//! - **[`SolveOutcome::Valid`]** — the condition holds for *every*
//!   assignment of the unbound features: the constraint is satisfied.
//! - **[`SolveOutcome::Unsatisfiable`]** — no assignment can make it hold:
//!   the constraint is violated (provably, not just for current values).
//! - **[`SolveOutcome::Satisfiable`]** — contingent; carries a witness
//!   assignment as (feature spelling, value) pairs.
//! - **[`SolveOutcome::Unknown`]** — outside the fragment, solver timeout,
//!   or an over-approximation (a feature whose *definition* is outside the
//!   fragment was treated as free — see below).
//!
//! Soundness note: a feature with a defining expression the translator
//! cannot encode is treated as a free variable. That over-approximates the
//! reachable states, so `Valid` and `Unsatisfiable` remain definitive, but
//! a bare `sat` no longer proves reachability — such results are reported
//! as `Unknown`, never as `Satisfiable`.
//!
//! Z3 runs as a subprocess (`z3` on `PATH`, or [`SolverConfig::z3_path`]);
//! nothing links libz3, so this crate builds without Z3 installed and only
//! needs the binary at run time. Full KerML semantics (occurrence and
//! temporal logic) are out of scope — the fragment above is the supported
//! one.

mod ival;
mod term;
mod translate;
mod z3;

use std::fmt;
use std::path::PathBuf;
pub use sysmlv2_model::check::ConstraintBinding;
use sysmlv2_model::check::{ConstraintVerdict, constraint_bindings, constraint_verdict};
use sysmlv2_model::json::ResolvedModel;
use sysmlv2_model::model::Model;
use term::RenderCtx;
use z3::{QueryResult, SExpr};

/// How to reach Z3.
#[derive(Clone, Debug)]
pub struct SolverConfig {
    /// Path to the `z3` binary; `None` = `z3` on `PATH`.
    pub z3_path: Option<PathBuf>,
    /// Soft solver timeout per query, milliseconds (a hard process kill
    /// sits one second above it).
    pub timeout_ms: u64,
}

impl Default for SolverConfig {
    fn default() -> Self {
        SolverConfig {
            z3_path: None,
            timeout_ms: 4000,
        }
    }
}

impl SolverConfig {
    fn z3(&self) -> PathBuf {
        self.z3_path.clone().unwrap_or_else(|| PathBuf::from("z3"))
    }
}

/// A witness value for one unbound feature.
#[derive(Clone, Debug, PartialEq)]
pub enum WitnessValue {
    Bool(bool),
    Int(i128),
    Real(f64),
    /// An enumeration literal, by declared name.
    Enum(String),
    /// A value in an inferred measurement unit (e.g. `30 [d]`) — units are
    /// never converted; the unit is the one the constraint compared the
    /// feature against.
    WithUnit(Box<WitnessValue>, String),
    /// A solver value this crate does not decode; raw SMT text.
    Other(String),
}

impl fmt::Display for WitnessValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            WitnessValue::Bool(b) => write!(f, "{b}"),
            WitnessValue::Int(i) => write!(f, "{i}"),
            WitnessValue::Real(r) => write!(f, "{r}"),
            WitnessValue::WithUnit(v, u) => write!(f, "{v} [{u}]"),
            WitnessValue::Enum(n) | WitnessValue::Other(n) => write!(f, "{n}"),
        }
    }
}

/// What solving concluded about one undecided constraint.
#[derive(Clone, Debug, PartialEq)]
pub enum SolveOutcome {
    /// Holds for every assignment of the unbound features.
    Valid,
    /// Holds for some assignments; here is one, as (feature, value) pairs.
    Satisfiable(Vec<(String, WitnessValue)>),
    /// No assignment can make it hold.
    Unsatisfiable,
    /// Not decided (reason: unsupported construct, solver unknown/timeout,
    /// or an over-approximated definition).
    Unknown(String),
}

/// One constraint with its evaluation verdict and, when that verdict was
/// undecided, the solver's conclusion.
#[derive(Clone, Debug)]
pub struct SolvedConstraint {
    /// Index into [`Model::units`].
    pub unit: usize,
    /// Span of the result expression.
    pub span: sysmlv2_syntax::span::Span,
    /// Declared name of the owning element, if any.
    pub name: Option<String>,
    /// Metaclass of the owning element (e.g. `AssertConstraintUsage`).
    pub element_type: &'static str,
    /// Whether the constraint is asserted to hold.
    pub asserted: bool,
    /// Verdict of the evaluation (checking) stage.
    pub verdict: ConstraintVerdict,
    /// Solver conclusion; `Some` exactly when `verdict` is undecided.
    pub solve: Option<SolveOutcome>,
    /// Feature bindings of the result expression (empty for satisfied
    /// constraints — nothing to explain).
    pub bindings: Vec<ConstraintBinding>,
}

/// Why solving could not run at all.
#[derive(Debug)]
pub enum SolveError {
    /// The Z3 binary was not found or did not identify itself.
    SolverUnavailable(String),
}

impl fmt::Display for SolveError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolveError::SolverUnavailable(m) => write!(f, "Z3 is not available: {m}"),
        }
    }
}

impl std::error::Error for SolveError {}

/// The configured Z3's version banner (the availability probe).
pub fn z3_version(cfg: &SolverConfig) -> Result<String, SolveError> {
    z3::version(&cfg.z3()).map_err(SolveError::SolverUnavailable)
}

/// Check every constraint of `model` (library units skipped) exactly like
/// `check_constraints`, then run Z3 over each undecided one.
pub fn solve_constraints(
    model: &Model,
    cfg: &SolverConfig,
) -> Result<Vec<SolvedConstraint>, SolveError> {
    z3_version(cfg)?;
    let mut r = ResolvedModel::build(model);
    let mut out = Vec::new();
    for c in r.constraints() {
        if model.units()[c.unit].is_library {
            continue;
        }
        let verdict = constraint_verdict(&mut r, &c);
        let solve = match &verdict {
            ConstraintVerdict::Undecided(_) => Some(solve_one(&mut r, &c, cfg, None)),
            _ => None,
        };
        let bindings = match verdict {
            ConstraintVerdict::Satisfied => Vec::new(),
            _ => constraint_bindings(&mut r, &c),
        };
        out.push(SolvedConstraint {
            unit: c.unit,
            span: c.span,
            name: c.name.clone(),
            element_type: c.element_type,
            asserted: c.asserted,
            verdict,
            solve,
            bindings,
        });
    }
    Ok(out)
}

// ---------------------------------------------------- interval propagation

/// Configuration for interval constraint propagation. Propagation
/// uses no external solver, so unlike [`SolverConfig`] it needs no Z3.
#[derive(Clone, Debug)]
pub struct PropagateConfig {
    /// Maximum fixpoint passes per unit before stopping. SysMD caps at 100;
    /// the driver also stops early at the first quiescent pass.
    pub max_iters: usize,
}

impl Default for PropagateConfig {
    fn default() -> Self {
        PropagateConfig { max_iters: 100 }
    }
}

/// A narrowed domain for one feature: an over-approximation of every value
/// the feature can take under the asserted constraints.
#[derive(Clone, Debug, PartialEq)]
pub struct FeatureRange {
    /// Model-facing feature spelling.
    pub feature: String,
    /// Inferred measurement unit (display spelling), if any.
    pub unit: Option<String>,
    /// Rendered range or set (`[10, +∞]`, `[3, 7]`, `{Red, Green}`).
    pub range: String,
    /// Whether propagation tightened the domain past its declared type.
    pub narrowed: bool,
}

/// What propagation concluded about one undecided constraint. All verdicts
/// are definitive (the narrowed domains contain every satisfying
/// assignment), never heuristic.
#[derive(Clone, Debug, PartialEq)]
pub enum PropagateOutcome {
    /// The body's forward interval is `{true}`: holds for every assignment
    /// consistent with the narrowed domains.
    Satisfied,
    /// The body's forward interval is `{false}`: holds for none.
    Violated,
    /// The asserted set contracted some feature's domain to empty — a proof
    /// the conjunction is inconsistent (same verdict Z3's `unsat` gives).
    Unsatisfiable,
    /// Still contingent; the narrowed [`FeatureRange`]s carry the residual
    /// information.
    Undecided,
    /// Outside the propagatable fragment (the translator's reason).
    Unsupported(String),
}

/// One constraint with its evaluation verdict and, when undecided, the
/// propagation conclusion. Mirrors [`SolvedConstraint`] for the no-solver
/// mode.
#[derive(Clone, Debug)]
pub struct PropagatedConstraint {
    /// Index into [`Model::units`].
    pub unit: usize,
    /// Span of the result expression.
    pub span: sysmlv2_syntax::span::Span,
    /// Declared name of the owning element, if any.
    pub name: Option<String>,
    /// Metaclass of the owning element.
    pub element_type: &'static str,
    /// Whether the constraint is asserted to hold.
    pub asserted: bool,
    /// Verdict of the evaluation (checking) stage.
    pub verdict: ConstraintVerdict,
    /// Propagation conclusion; `Some` exactly when `verdict` is undecided.
    pub propagate: Option<PropagateOutcome>,
    /// Feature bindings of the result expression (empty for satisfied
    /// constraints — nothing to explain).
    pub bindings: Vec<ConstraintBinding>,
    /// Display spellings of the free features this constraint's
    /// propagation term references — the keys to correlate with
    /// [`Propagation::ranges`]. Empty when the constraint was decided
    /// by evaluation or fell outside the propagatable fragment.
    pub features: Vec<String>,
}

/// The result of propagating over a whole model.
#[derive(Clone, Debug)]
pub struct Propagation {
    /// One entry per non-library constraint, in model order.
    pub constraints: Vec<PropagatedConstraint>,
    /// Narrowed feature domains, in first-encountered order. A feature may
    /// recur across units (distinct elements sharing a spelling).
    pub ranges: Vec<FeatureRange>,
}

/// Check every constraint of `model` like [`solve_constraints`], then run
/// interval propagation over each unit's asserted constraints jointly —
/// narrowing every free feature's domain, upgrading verdicts definitively,
/// and proving empty domains inconsistent — without any external solver.
pub fn propagate_constraints(model: &Model, cfg: &PropagateConfig) -> Propagation {
    let mut r = ResolvedModel::build(model);
    let all = user_constraints(&mut r, model);
    let verdicts: Vec<ConstraintVerdict> =
        all.iter().map(|c| constraint_verdict(&mut r, c)).collect();
    let (outcomes, ranges, features) = propagate_core(&mut r, &all, &verdicts, cfg);
    let constraints = all
        .iter()
        .enumerate()
        .map(|(i, c)| {
            let bindings = match verdicts[i] {
                ConstraintVerdict::Satisfied => Vec::new(),
                _ => constraint_bindings(&mut r, c),
            };
            PropagatedConstraint {
                unit: c.unit,
                span: c.span,
                name: c.name.clone(),
                element_type: c.element_type,
                asserted: c.asserted,
                verdict: verdicts[i].clone(),
                propagate: outcomes[i].clone(),
                bindings,
                features: features[i].clone(),
            }
        })
        .collect();
    Propagation {
        constraints,
        ranges,
    }
}

/// The non-library constraints of `model`, in model order.
fn user_constraints(
    r: &mut ResolvedModel,
    model: &Model,
) -> Vec<sysmlv2_model::json::ConstraintInfo> {
    r.constraints()
        .into_iter()
        .filter(|c| !model.units()[c.unit].is_library)
        .collect()
}

/// Whether a propagation outcome settled the constraint on its own (so no
/// solver call is needed for it).
fn propagation_is_definitive(o: &Option<PropagateOutcome>) -> bool {
    matches!(
        o,
        Some(
            PropagateOutcome::Satisfied
                | PropagateOutcome::Violated
                | PropagateOutcome::Unsatisfiable
        )
    )
}

/// Joint interval propagation over `all`, grouped by owning unit. Returns
/// (per-constraint propagation outcome — `Some` only for undecided
/// constraints, `None` for eval-decided ones; narrowed feature ranges;
/// per-constraint referenced-feature spellings, index-aligned with
/// `all`). Shared by [`propagate_constraints`] and
/// [`verify_constraints`].
fn propagate_core(
    r: &mut ResolvedModel,
    all: &[sysmlv2_model::json::ConstraintInfo],
    verdicts: &[ConstraintVerdict],
    cfg: &PropagateConfig,
) -> (
    Vec<Option<PropagateOutcome>>,
    Vec<FeatureRange>,
    Vec<Vec<String>>,
) {
    let undecided = |i: usize| matches!(verdicts[i], ConstraintVerdict::Undecided(_));

    // A feature belongs to one unit, so units are the natural joint
    // boundary: constraints in different units share no free variables.
    let mut by_unit: Vec<(usize, Vec<usize>)> = Vec::new();
    for (i, c) in all.iter().enumerate() {
        match by_unit.iter_mut().find(|(u, _)| *u == c.unit) {
            Some((_, v)) => v.push(i),
            None => by_unit.push((c.unit, vec![i])),
        }
    }

    let mut outcomes: Vec<Option<PropagateOutcome>> = vec![None; all.len()];
    let mut ranges: Vec<FeatureRange> = Vec::new();
    let mut features: Vec<Vec<String>> = vec![Vec::new(); all.len()];

    for (_, idxs) in &by_unit {
        let cs: Vec<&sysmlv2_model::json::ConstraintInfo> = idxs.iter().map(|&i| &all[i]).collect();
        let jt = match translate::translate_all(r, &cs) {
            Ok(jt) => jt,
            Err(translate::Unsupported(m)) => {
                for &i in idxs {
                    if undecided(i) {
                        outcomes[i] = Some(PropagateOutcome::Unsupported(format!(
                            "not in the propagatable fragment: {m}"
                        )));
                    }
                }
                continue;
            }
        };
        let enum_sizes: Vec<usize> = jt.enums.iter().map(|e| e.ctors.len()).collect();
        let init: Vec<ival::Dom> = jt
            .vars
            .iter()
            .map(|v| ival::init_dom(v.sort, &enum_sizes))
            .collect();
        // Declared-type ranges (e.g. `Natural ≥ 0`) set the baseline; the
        // asserted constraints narrow past it. Only undecided asserted
        // constraints contribute facts — a decided one is either vacuous
        // (fully bound) or already reported as violated.
        let (baseline, _) = ival::drive(init, &jt.side, cfg.max_iters);
        let mut facts = jt.side.clone();
        for (k, &i) in idxs.iter().enumerate() {
            if all[i].asserted && undecided(i) {
                match &jt.roots[k] {
                    translate::JointRoot::Root(t) => facts.push(t.clone()),
                    // A partially translated conjunction asserts each
                    // translated conjunct on its own.
                    translate::JointRoot::Partial { terms, .. } => {
                        facts.extend(terms.iter().cloned())
                    }
                    translate::JointRoot::Skipped(_) => {}
                }
            }
        }
        let (doms, _unsat) = ival::drive(baseline.clone(), &facts, cfg.max_iters);

        for (vi, v) in jt.vars.iter().enumerate() {
            ranges.push(FeatureRange {
                feature: v.display.clone(),
                unit: v.unit.clone(),
                range: ival::fmt_dom(doms[vi], &jt.enums),
                narrowed: doms[vi] != baseline[vi],
            });
        }

        for (k, &i) in idxs.iter().enumerate() {
            if !undecided(i) {
                continue;
            }
            {
                let mut vs = std::collections::BTreeSet::new();
                match &jt.roots[k] {
                    translate::JointRoot::Root(t) => term::term_vars(t, &mut vs),
                    translate::JointRoot::Partial { terms, .. } => {
                        for t in terms {
                            term::term_vars(t, &mut vs);
                        }
                    }
                    translate::JointRoot::Skipped(_) => {}
                }
                features[i] = vs.iter().map(|&v| jt.vars[v].display.clone()).collect();
            }
            outcomes[i] = Some(match &jt.roots[k] {
                translate::JointRoot::Skipped(m) => PropagateOutcome::Unsupported(m.clone()),
                // Each constraint's verdict is its OWN root forward-evaluated
                // over the joint domains — so an empty domain proves only the
                // constraints that actually reference the emptied feature
                // unsatisfiable, not innocent siblings that happen to share
                // the unit. (`eval_term` poisons to empty through any empty
                // operand, so a reference to an emptied feature reads as
                // `Empty` here.)
                translate::JointRoot::Root(t) => match ival::eval_term(t, &doms) {
                    ival::Dom::B(ival::Tri::True) => PropagateOutcome::Satisfied,
                    ival::Dom::B(ival::Tri::False) => PropagateOutcome::Violated,
                    d if d.is_empty() => PropagateOutcome::Unsatisfiable,
                    _ => PropagateOutcome::Undecided,
                },
                // A partial conjunction: the translated conjuncts can
                // refute (any false or empty) but never prove — the
                // untranslated one is unaccounted for, so everything
                // else stays outside the fragment with its reason.
                translate::JointRoot::Partial { terms, skipped } => {
                    let mut verdict = None;
                    for t in terms {
                        match ival::eval_term(t, &doms) {
                            ival::Dom::B(ival::Tri::False) => {
                                verdict = Some(PropagateOutcome::Violated);
                                break;
                            }
                            d if d.is_empty() => {
                                verdict = Some(PropagateOutcome::Unsatisfiable);
                                break;
                            }
                            _ => {}
                        }
                    }
                    verdict.unwrap_or_else(|| PropagateOutcome::Unsupported(skipped.clone()))
                }
            });
        }
    }
    (outcomes, ranges, features)
}

/// One constraint's full verification: its evaluation verdict, the
/// interval-propagation conclusion (always attempted for an undecided
/// constraint), and — only when solving was requested *and* propagation
/// left it open — the Z3 conclusion.
#[derive(Clone, Debug)]
pub struct VerifiedConstraint {
    /// Index into [`Model::units`].
    pub unit: usize,
    /// Span of the result expression.
    pub span: sysmlv2_syntax::span::Span,
    /// Declared name of the owning element, if any.
    pub name: Option<String>,
    /// Metaclass of the owning element.
    pub element_type: &'static str,
    /// Whether the constraint is asserted to hold.
    pub asserted: bool,
    /// Verdict of the evaluation (checking) stage.
    pub verdict: ConstraintVerdict,
    /// Propagation conclusion; `Some` exactly when `verdict` is undecided.
    pub propagate: Option<PropagateOutcome>,
    /// Z3 conclusion; `Some` only when solving was requested and neither
    /// evaluation nor propagation settled the constraint.
    pub solve: Option<SolveOutcome>,
    /// Feature bindings of the result expression (empty for satisfied
    /// constraints — nothing to explain).
    pub bindings: Vec<ConstraintBinding>,
    /// Display spellings of the free features this constraint's
    /// propagation term references (see [`PropagatedConstraint::features`]).
    pub features: Vec<String>,
}

/// The whole model verified in one pass: per-constraint verdicts and the
/// narrowed feature ranges.
#[derive(Clone, Debug)]
pub struct VerifyReport {
    pub constraints: Vec<VerifiedConstraint>,
    pub ranges: Vec<FeatureRange>,
}

/// The full verification pipeline. Interval propagation runs first over
/// every constraint (narrowing ranges, upgrading verdicts, proving empty
/// domains inconsistent); then, when `solver` is `Some`, Z3 runs **only**
/// on the constraints propagation could not settle — fewer, smaller
/// queries. With `solver` `None` this is the solverless `--ranges` mode.
///
/// `Err` only when solving was requested and the Z3 binary is unavailable.
pub fn verify_constraints(
    model: &Model,
    solver: Option<&SolverConfig>,
    prop_cfg: &PropagateConfig,
) -> Result<VerifyReport, SolveError> {
    if let Some(cfg) = solver {
        z3_version(cfg)?;
    }
    let mut r = ResolvedModel::build(model);
    let all = user_constraints(&mut r, model);
    let verdicts: Vec<ConstraintVerdict> =
        all.iter().map(|c| constraint_verdict(&mut r, c)).collect();
    let (propagate, ranges, features) = propagate_core(&mut r, &all, &verdicts, prop_cfg);

    let mut constraints = Vec::with_capacity(all.len());
    for (i, c) in all.iter().enumerate() {
        // Solve only the residue: an undecided constraint propagation could
        // not settle on its own.
        let solve = match solver {
            Some(cfg)
                if matches!(verdicts[i], ConstraintVerdict::Undecided(_))
                    && !propagation_is_definitive(&propagate[i]) =>
            {
                Some(solve_one(&mut r, c, cfg, Some(prop_cfg)))
            }
            _ => None,
        };
        let bindings = match verdicts[i] {
            ConstraintVerdict::Satisfied => Vec::new(),
            _ => constraint_bindings(&mut r, c),
        };
        constraints.push(VerifiedConstraint {
            unit: c.unit,
            span: c.span,
            name: c.name.clone(),
            element_type: c.element_type,
            asserted: c.asserted,
            verdict: verdicts[i].clone(),
            propagate: propagate[i].clone(),
            solve,
            bindings,
            features: features[i].clone(),
        });
    }
    Ok(VerifyReport {
        constraints,
        ranges,
    })
}

/// Render single-constraint propagated domains as SMT bound assertions
/// (`(assert (>= x lo))`, enum membership, boolean fixing). Infinite /
/// saturated endpoints and full domains contribute nothing. These are
/// sound to add **only** to the "can it hold?" query — see [`solve_one`].
fn domain_bound_asserts(
    vars: &[translate::VarInfo],
    doms: &[ival::Dom],
    enums: &[term::EnumSort],
) -> String {
    let mut out = String::new();
    for (i, v) in vars.iter().enumerate() {
        match doms[i] {
            ival::Dom::R(iv) => {
                if iv.lo.is_finite() {
                    if let Some(l) = term::real_from_f64(iv.lo) {
                        out.push_str(&format!("(assert (>= {} {l}))\n", v.sym));
                    }
                }
                if iv.hi.is_finite() {
                    if let Some(h) = term::real_from_f64(iv.hi) {
                        out.push_str(&format!("(assert (<= {} {h}))\n", v.sym));
                    }
                }
            }
            ival::Dom::I(iv) => {
                if iv.lo != i128::MIN {
                    out.push_str(&format!(
                        "(assert (>= {} {}))\n",
                        v.sym,
                        term::render_int(iv.lo)
                    ));
                }
                if iv.hi != i128::MAX {
                    out.push_str(&format!(
                        "(assert (<= {} {}))\n",
                        v.sym,
                        term::render_int(iv.hi)
                    ));
                }
            }
            ival::Dom::B(ival::Tri::True) => out.push_str(&format!("(assert {})\n", v.sym)),
            ival::Dom::B(ival::Tri::False) => out.push_str(&format!("(assert (not {}))\n", v.sym)),
            ival::Dom::E(s, set) => {
                // A strict, non-empty subset of the enum's literals.
                let lits: Vec<String> = enums[s]
                    .ctors
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| set.contains(*j))
                    .map(|(_, ctor)| format!("(= {} {ctor})", v.sym))
                    .collect();
                if !lits.is_empty() && lits.len() < enums[s].ctors.len() {
                    if lits.len() == 1 {
                        out.push_str(&format!("(assert {})\n", lits[0]));
                    } else {
                        out.push_str(&format!("(assert (or {}))\n", lits.join(" ")));
                    }
                }
            }
            _ => {}
        }
    }
    out
}

/// Solve one undecided constraint with Z3. When `propagate_bounds` is
/// `Some` (the `verify` pipeline, passing its propagation config through),
/// single-constraint interval propagation runs first and its narrowed
/// domains are asserted as bounds on the **first** query only.
///
/// Soundness of the injection: the propagated domains contain *every*
/// assignment satisfying the constraint (the propagation invariant), so
/// intersecting Q1 — "can the body hold?" — with them removes no
/// satisfying model; it only shrinks Z3's search and sharpens sorts.
/// The bounds must never reach Q2 — "can the body fail?" — because a
/// falsifying witness may lie *outside* the goal-derived domains, and
/// clipping it away would fake a validity proof.
fn solve_one(
    r: &mut ResolvedModel,
    c: &sysmlv2_model::json::ConstraintInfo,
    cfg: &SolverConfig,
    propagate_bounds: Option<&PropagateConfig>,
) -> SolveOutcome {
    let tr = match translate::translate(r, c) {
        Ok(tr) => tr,
        Err(translate::Unsupported(m)) => {
            return SolveOutcome::Unknown(format!("not in the solvable fragment: {m}"));
        }
    };
    let var_sorts: Vec<_> = tr.vars.iter().map(|v| v.sort).collect();
    let var_syms: Vec<_> = tr.vars.iter().map(|v| v.sym.clone()).collect();
    let ctx = RenderCtx {
        var_sorts: &var_sorts,
        var_syms: &var_syms,
        enums: &tr.enums,
    };
    let internal = |e: String| SolveOutcome::Unknown(format!("internal translation error: {e}"));
    let (goal, _) = match ctx.render(&tr.root) {
        Ok(g) => g,
        Err(e) => return internal(e),
    };
    let mut decls = String::new();
    decls.push_str(&format!("(set-option :timeout {})\n", cfg.timeout_ms));
    for e in &tr.enums {
        let ctors: Vec<String> = e.ctors.iter().map(|c| format!("({c})")).collect();
        decls.push_str(&format!(
            "(declare-datatypes (({} 0)) (({})))\n",
            e.sym,
            ctors.join(" ")
        ));
    }
    for v in &tr.vars {
        decls.push_str(&format!(
            "(declare-const {} {})\n",
            v.sym,
            ctx.sort_name(v.sort)
        ));
    }
    for s in &tr.side {
        match ctx.render(s) {
            Ok((t, _)) => decls.push_str(&format!("(assert {t})\n")),
            Err(e) => return internal(e),
        }
    }

    // Bounds from single-constraint propagation, asserted on Q1 only.
    let q1_bounds = if let Some(pc) = propagate_bounds {
        let enum_sizes: Vec<usize> = tr.enums.iter().map(|e| e.ctors.len()).collect();
        let init: Vec<ival::Dom> = tr
            .vars
            .iter()
            .map(|v| ival::init_dom(v.sort, &enum_sizes))
            .collect();
        let mut facts = tr.side.clone();
        facts.push(tr.root.clone());
        let (doms, unsat) = ival::drive(init, &facts, pc.max_iters);
        // An emptied domain would mean the constraint is unsatisfiable — a
        // residual constraint never is (propagation would have caught it),
        // but guard anyway rather than emit a contradictory bound.
        if unsat {
            String::new()
        } else {
            domain_bound_asserts(&tr.vars, &doms, &tr.enums)
        }
    } else {
        String::new()
    };

    // Q1: can the condition hold at all? (witness requested)
    let q1 = format!(
        "{decls}{q1_bounds}(assert {goal})\n(check-sat)\n{}",
        if var_syms.is_empty() {
            String::new()
        } else {
            format!("(get-value ({}))\n", var_syms.join(" "))
        }
    );
    let witness = match z3::run_query(&cfg.z3(), cfg.timeout_ms, &q1, var_syms.len()) {
        Err(e) => return SolveOutcome::Unknown(e),
        Ok(QueryResult::Unsat) => return SolveOutcome::Unsatisfiable,
        Ok(QueryResult::Unknown(m)) => return SolveOutcome::Unknown(m),
        Ok(QueryResult::Sat(values)) => values,
    };

    // Q2: can it fail? (unsat here = valid)
    let q2 = format!("{decls}(assert (not {goal}))\n(check-sat)\n");
    match z3::run_query(&cfg.z3(), cfg.timeout_ms, &q2, 0) {
        Ok(QueryResult::Unsat) => return SolveOutcome::Valid,
        Ok(QueryResult::Sat(_)) | Ok(QueryResult::Unknown(_)) | Err(_) => {}
    }
    if !tr.approx.is_empty() {
        return SolveOutcome::Unknown(format!(
            "`{}` has a definition outside the solvable fragment",
            tr.approx.join("`, `")
        ));
    }
    let pairs = tr
        .vars
        .iter()
        .zip(&witness)
        .map(|(v, val)| {
            let decoded = decode_value(val, &tr.enums);
            let decoded = match &v.unit {
                Some(u) => WitnessValue::WithUnit(Box::new(decoded), u.clone()),
                None => decoded,
            };
            (v.display.clone(), decoded)
        })
        .collect();
    SolveOutcome::Satisfiable(pairs)
}

/// Decode one `(get-value …)` value expression.
fn decode_value(s: &SExpr, enums: &[term::EnumSort]) -> WitnessValue {
    fn raw(s: &SExpr) -> String {
        match s {
            SExpr::Atom(a) => a.clone(),
            SExpr::List(items) => {
                let inner: Vec<String> = items.iter().map(raw).collect();
                format!("({})", inner.join(" "))
            }
        }
    }
    fn go(s: &SExpr, enums: &[term::EnumSort]) -> Option<WitnessValue> {
        match s {
            SExpr::Atom(a) => {
                if a == "true" {
                    return Some(WitnessValue::Bool(true));
                }
                if a == "false" {
                    return Some(WitnessValue::Bool(false));
                }
                if let Ok(i) = a.parse::<i128>() {
                    return Some(WitnessValue::Int(i));
                }
                if a.contains('.') {
                    if let Ok(f) = a.parse::<f64>() {
                        return Some(WitnessValue::Real(f));
                    }
                }
                for e in enums {
                    if let Some(j) = e.ctors.iter().position(|c| c == a) {
                        return Some(WitnessValue::Enum(e.displays[j].clone()));
                    }
                }
                None
            }
            SExpr::List(items) => match items.as_slice() {
                [SExpr::Atom(op), x] if op == "-" => match go(x, enums)? {
                    WitnessValue::Int(i) => Some(WitnessValue::Int(-i)),
                    WitnessValue::Real(f) => Some(WitnessValue::Real(-f)),
                    _ => None,
                },
                [SExpr::Atom(op), a, b] if op == "/" => {
                    let num = match go(a, enums)? {
                        WitnessValue::Int(i) => i as f64,
                        WitnessValue::Real(f) => f,
                        _ => return None,
                    };
                    let den = match go(b, enums)? {
                        WitnessValue::Int(i) => i as f64,
                        WitnessValue::Real(f) => f,
                        _ => return None,
                    };
                    Some(WitnessValue::Real(num / den))
                }
                _ => None,
            },
        }
    }
    go(s, enums).unwrap_or_else(|| WitnessValue::Other(raw(s)))
}

/// Witness-containment cross-check: the two backends verify each
/// other. For every corpus constraint where Z3 exhibits a satisfying
/// witness, that witness must lie inside the domains interval propagation
/// derives for the *same* single-constraint system — the soundness
/// invariant (a propagated domain contains every satisfying assignment)
/// made empirical over the whole corpus. A contractor that over-narrowed
/// would let a real witness escape and this test would catch it.
#[cfg(test)]
mod witness_containment {
    use super::*;
    use crate::ival::Dom;
    use crate::term::EnumSort;

    fn dom_contains(val: &WitnessValue, d: Dom, enums: &[EnumSort]) -> bool {
        // A quantity witness carries its magnitude in the same reference
        // scale the term (and thus the domain) uses.
        let val = match val {
            WitnessValue::WithUnit(inner, _) => inner.as_ref(),
            v => v,
        };
        match (val, d) {
            (WitnessValue::Int(i), Dom::I(iv)) => iv.contains(*i),
            (WitnessValue::Int(i), Dom::R(rv)) => rv.contains(*i as f64),
            (WitnessValue::Real(f), Dom::R(rv)) => rv.contains(*f),
            (WitnessValue::Real(f), Dom::I(iv)) => iv.to_ival().contains(*f),
            (WitnessValue::Bool(b), Dom::B(t)) => {
                if *b {
                    t.may_true()
                } else {
                    t.may_false()
                }
            }
            (WitnessValue::Enum(name), Dom::E(s, set)) => enums[s]
                .displays
                .iter()
                .enumerate()
                .any(|(i, n)| n == name && set.contains(i)),
            // Opaque values (strings, undecoded) carry no interval to test.
            _ => true,
        }
    }

    #[test]
    fn corpus_witnesses_lie_in_propagated_ranges() {
        let cfg = SolverConfig::default();
        if z3_version(&cfg).is_err() {
            eprintln!("skipping corpus_witnesses_lie_in_propagated_ranges: no z3 on PATH");
            return;
        }
        let mut model = Model::new();
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        for f in sysmlv2_testkit::user_files() {
            let src = std::fs::read_to_string(&f).unwrap();
            model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
        }
        let mut r = ResolvedModel::build(&model);
        let mut checked = 0usize;
        for c in r.constraints() {
            if model.units()[c.unit].is_library {
                continue;
            }
            if !matches!(
                constraint_verdict(&mut r, &c),
                ConstraintVerdict::Undecided(_)
            ) {
                continue;
            }
            let SolveOutcome::Satisfiable(pairs) = solve_one(&mut r, &c, &cfg, None) else {
                continue;
            };
            // Re-translate the identical single constraint and propagate its
            // asserted system {root} ∪ declared-type side facts — exactly
            // what Z3's first query asserted. Determinism guarantees the
            // variable order matches the witness pairs.
            let Ok(tr) = translate::translate(&mut r, &c) else {
                continue;
            };
            let enum_sizes: Vec<usize> = tr.enums.iter().map(|e| e.ctors.len()).collect();
            let init: Vec<Dom> = tr
                .vars
                .iter()
                .map(|v| ival::init_dom(v.sort, &enum_sizes))
                .collect();
            let mut facts = tr.side.clone();
            facts.push(tr.root.clone());
            let (doms, unsat) = ival::drive(init, &facts, PropagateConfig::default().max_iters);
            let where_ = &model.units()[c.unit].name;
            assert!(
                !unsat,
                "propagation proved unsat but Z3 found a witness: {:?} in {where_}",
                c.name
            );
            assert_eq!(pairs.len(), tr.vars.len(), "witness/var count mismatch");
            for (k, (disp, val)) in pairs.iter().enumerate() {
                assert!(
                    dom_contains(val, doms[k], &tr.enums),
                    "witness {disp} = {val} escapes propagated range {} ({:?} in {where_})",
                    ival::fmt_dom(doms[k], &tr.enums),
                    c.name
                );
            }
            checked += 1;
        }
        eprintln!("witness containment: cross-checked {checked} witnessed constraints");
    }
}

/// Bound-injection soundness: asserting single-
/// constraint propagated domains on Z3's first query must never change a
/// definitive verdict — it only sharpens sorts and shrinks the search. So
/// over the corpus, the bounded and unbounded solves must never disagree
/// on a constraint both decide; any difference is `Unknown`-vs-decided.
#[cfg(test)]
mod bound_injection {
    use super::*;
    use crate::ival::{Dom, EnumSet, IntIval, Ival, Tri};
    use crate::term::{EnumSort, Sort};

    fn var(sym: &str, sort: Sort) -> translate::VarInfo {
        translate::VarInfo {
            display: sym.into(),
            sym: sym.into(),
            sort,
            unit: None,
        }
    }

    #[test]
    fn bound_rendering_covers_each_domain_kind() {
        let enums = vec![EnumSort {
            sym: "Phase".into(),
            ctors: vec!["halt".into(), "mid".into(), "init".into()],
            displays: vec!["halt".into(), "mid".into(), "init".into()],
        }];
        let vars = vec![
            var("x", Sort::Real),
            var("n", Sort::Int),
            var("b", Sort::Bool),
            var("c", Sort::Enum(0)),
            var("free", Sort::Real),
        ];
        let doms = vec![
            Dom::R(Ival::new(10.0, f64::INFINITY)), // one-sided real
            Dom::I(IntIval::new(0, 5)),             // closed integer
            Dom::B(Tri::True),                      // fixed boolean
            Dom::E(0, EnumSet { bits: 0b101 }),     // {halt, init}
            Dom::R(Ival::TOP),                      // nothing to say
        ];
        let out = domain_bound_asserts(&vars, &doms, &enums);
        assert!(out.contains("(assert (>= x 10.0))"), "{out}");
        assert!(
            !out.contains("(<= x"),
            "one-sided real must not bound above:\n{out}"
        );
        assert!(
            out.contains("(assert (>= n 0))") && out.contains("(assert (<= n 5))"),
            "{out}"
        );
        assert!(out.contains("(assert b)"), "{out}");
        assert!(out.contains("(assert (or (= c halt) (= c init)))"), "{out}");
        assert!(
            !out.contains("free"),
            "an unbounded ⊤ real emits nothing:\n{out}"
        );
    }

    /// A verdict's definitive discriminant, or `None` for `Unknown`.
    fn discriminant(o: &SolveOutcome) -> Option<u8> {
        match o {
            SolveOutcome::Valid => Some(1),
            SolveOutcome::Unsatisfiable => Some(2),
            SolveOutcome::Satisfiable(_) => Some(3),
            SolveOutcome::Unknown(_) => None,
        }
    }

    #[test]
    fn bounds_never_change_a_definitive_verdict() {
        let cfg = SolverConfig::default();
        if z3_version(&cfg).is_err() {
            eprintln!("skipping bounds_never_change_a_definitive_verdict: no z3 on PATH");
            return;
        }
        let mut model = Model::new();
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        for f in sysmlv2_testkit::user_files() {
            let src = std::fs::read_to_string(&f).unwrap();
            model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
        }
        let mut r = ResolvedModel::build(&model);
        let (mut agree, mut improved, mut regressed) = (0usize, 0usize, 0usize);
        for c in r.constraints() {
            if model.units()[c.unit].is_library {
                continue;
            }
            if !matches!(
                constraint_verdict(&mut r, &c),
                ConstraintVerdict::Undecided(_)
            ) {
                continue;
            }
            let plain = solve_one(&mut r, &c, &cfg, None);
            let bounded = solve_one(&mut r, &c, &cfg, Some(&PropagateConfig::default()));
            let where_ = &model.units()[c.unit].name;
            match (discriminant(&plain), discriminant(&bounded)) {
                (Some(a), Some(b)) => {
                    assert_eq!(
                        a, b,
                        "bounds flipped the verdict for {:?} in {where_}: {plain:?} vs {bounded:?}",
                        c.name
                    );
                    agree += 1;
                }
                // Bounds turned an unknown into a decision — the point of
                // the optimization.
                (None, Some(_)) => improved += 1,
                // Extra assertions can, rarely, slow Z3 into a timeout; not
                // unsound, but worth surfacing.
                (Some(_), None) => regressed += 1,
                (None, None) => {}
            }
        }
        eprintln!(
            "bound injection: {agree} verdicts agree, {improved} newly decided, {regressed} regressed to unknown"
        );
    }
}
