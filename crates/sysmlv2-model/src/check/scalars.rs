//! Feature-value scalar conformance: a bound value whose evaluated
//! scalar partition can never inhabit any of the feature's declared
//! types.
use crate::{json::ResolvedModel, model::Model};
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    // --- feature-value scalar conformance ---
    // Narrowed to what is provable. A stricter static rule — the value
    // expression's *declared* result type must conform to the feature's
    // declared type — would reject 15 official corpus files whose bindings
    // are legal under KerML multiple classification: a `Rational`-typed
    // literal's value may well inhabit a sibling subtype of `Real`
    // (`ScalarValues::Rational does not conform to EnumerationTest::Size`
    // is exactly the corpus's enum-restriction idiom, and the ISO-8601
    // string encodings and metadata levels follow the same shape). What
    // *is* provable is kind-level disjointness of the evaluated value:
    // `ScalarValues` partitions its scalars into Boolean, String, and the
    // Number tower, and a value of one partition is never an instance of
    // a type in another; within the tower, a non-integral rational is
    // never an instance of an `Integer`-conforming type. Declared types
    // classify by simple scalar names over the explicit supertype closure
    // (the solver's `declared_sort` discipline — works with or without
    // the standard library); an untyped redefining feature borrows the
    // redefinition target's declared types (one hop). Unclassifiable
    // declared types, unevaluable values, quantities, sequences, and
    // element values all stay silent. Warnings, per checker policy.
    let value_sites: Vec<(usize, usize, sysmlv2_syntax::ast::Expr)> =
        r.b.values
            .iter()
            .filter(|(o, _)| !model.is_library_unit(r.b.unit_of_elem(**o)))
            .map(|(o, (s, e))| (*o, *s, e.clone()))
            .collect();
    for (owner, scope, expr) in value_sites {
        let unit = r.b.unit_of_elem(owner);
        if model.is_library_unit(unit) {
            continue;
        }
        let mut tys = r.b.direct_typing_elems(owner);
        if tys.is_empty() {
            for t in r.b.redefinition_target_elems(owner) {
                for ty in r.b.direct_typing_elems(t) {
                    if !tys.contains(&ty) {
                        tys.push(ty);
                    }
                }
            }
        }
        // Every declared type must classify — a type this walk cannot
        // place may admit the value through bases it cannot see.
        let kinds: Vec<ScalarKind> = tys
            .iter()
            .filter_map(|&ty| declared_scalar_kind(&mut r.b, ty))
            .collect();
        if kinds.is_empty() || kinds.len() != tys.len() {
            continue;
        }
        let Ok(v) = crate::eval::evaluate_expr_in(&mut r.b, scope, &expr) else {
            continue; // undecided, not wrong
        };
        let Some(value_kind) = value_scalar_kind(&v) else {
            continue; // quantities, sequences, instances, elements
        };
        if kinds.iter().any(|&k| scalar_kind_admits(k, value_kind)) {
            continue;
        }
        let ty_name = r.b.elements[tys[0]]
            .props
            .get("declaredName")
            .and_then(|v| v.as_str())
            .unwrap_or("<anonymous>")
            .to_string();
        let msg = match value_kind {
            ScalarKind::Number { integral: false }
                if matches!(kinds[0], ScalarKind::Number { .. }) =>
            {
                format!(
                    "feature value {v} is not an integer and can never conform \
                     to the declared type `{ty_name}`"
                )
            }
            _ => {
                let vdesc = match value_kind {
                    ScalarKind::Boolean => "a Boolean",
                    ScalarKind::Str => "a String",
                    ScalarKind::Number { .. } => "a number",
                };
                format!(
                    "feature value evaluates to {vdesc}, which can never \
                     conform to the declared type `{ty_name}`"
                )
            }
        };
        out.push((unit, Diagnostic::warning(expr.span, msg)));
    }
    out
}

/// The provably-disjoint `ScalarValues` partitions: Boolean, String, and
/// the Number tower (with `Integer`-and-below tracked for integrality).
#[derive(Clone, Copy, PartialEq)]
enum ScalarKind {
    Boolean,
    Str,
    Number { integral: bool },
}

/// The partition an evaluated value inhabits — `None` for the values
/// the conformance check stays silent on (quantities, sequences,
/// instances, elements).
fn value_scalar_kind(v: &crate::eval::Value) -> Option<ScalarKind> {
    use crate::eval::Value;
    Some(match v {
        Value::Boolean(_) => ScalarKind::Boolean,
        Value::String(_) => ScalarKind::Str,
        Value::Integer(_) => ScalarKind::Number { integral: true },
        Value::Rational(r) => ScalarKind::Number {
            integral: r.is_integer(),
        },
        Value::Real(f) => ScalarKind::Number {
            integral: f.fract() == 0.0 && f.is_finite(),
        },
        _ => return None,
    })
}

/// Whether a declared partition admits a value's: same partition, and
/// within the Number tower an integral requirement met by an integral
/// value. Cross-partition pairs are provably disjoint.
fn scalar_kind_admits(decl: ScalarKind, value: ScalarKind) -> bool {
    match (decl, value) {
        (ScalarKind::Boolean, ScalarKind::Boolean) => true,
        (ScalarKind::Str, ScalarKind::Str) => true,
        (ScalarKind::Number { integral: need }, ScalarKind::Number { integral: have }) => {
            !need || have
        }
        _ => false,
    }
}

impl crate::json::ResolvedModel {
    /// The feature-value scalar-conformance verdict the semantic check
    /// would reach for `value` bound to a feature declaring exactly
    /// `declared` as its types: `Some(false)` when the check would
    /// report the value as never conforming, `Some(true)` when some
    /// declared type admits it, `None` where the check stays silent
    /// (no declared type, a declared type it cannot classify, or a
    /// non-scalar value). Lets a fix that writes a typing verify its
    /// result against the value before offering it.
    pub fn scalar_value_admitted(
        &mut self,
        declared: &[crate::json::ElementRef],
        value: &crate::eval::Value,
    ) -> Option<bool> {
        let kinds: Vec<ScalarKind> = declared
            .iter()
            .filter_map(|t| declared_scalar_kind(&mut self.b, t.0))
            .collect();
        if kinds.is_empty() || kinds.len() != declared.len() {
            return None;
        }
        let value_kind = value_scalar_kind(value)?;
        Some(kinds.iter().any(|&k| scalar_kind_admits(k, value_kind)))
    }
}

/// Classify a declared type into its scalar partition by walking the
/// explicit typing/specialization closure and matching the `ScalarValues`
/// simple names — the same name-based discipline as the solver's
/// `declared_sort`, so it works with or without the standard library.
/// Breadth-first, first match wins: the nearest scalar ancestor decides
/// integrality (`Size :> Real` classifies non-integral even though `Real`
/// has integral subtypes). `None` = not provably a scalar type.
fn declared_scalar_kind(b: &mut crate::json::Builder, ty: usize) -> Option<ScalarKind> {
    use std::collections::{HashSet, VecDeque};
    let mut queue: VecDeque<usize> = VecDeque::new();
    queue.push_back(ty);
    let mut seen: HashSet<usize> = HashSet::new();
    let mut steps = 0;
    while let Some(t) = queue.pop_front() {
        if !seen.insert(t) {
            continue;
        }
        steps += 1;
        if steps > 64 {
            break;
        }
        let name = b.elements[t]
            .props
            .get("declaredName")
            .and_then(|v| v.as_str());
        match name {
            Some("Boolean") => return Some(ScalarKind::Boolean),
            Some("String") => return Some(ScalarKind::Str),
            Some("Integer" | "Natural" | "Positive") => {
                return Some(ScalarKind::Number { integral: true });
            }
            Some("NumericalValue" | "Number" | "Complex" | "Real" | "Rational") => {
                return Some(ScalarKind::Number { integral: false });
            }
            _ => {}
        }
        for s in b.explicit_supertype_elems(t) {
            queue.push_back(s);
        }
    }
    None
}
