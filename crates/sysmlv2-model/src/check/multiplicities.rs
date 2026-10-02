//! Multiplicity bounds. A bound that provably evaluates to something
//! other than a natural number, to a negative number, or to a lower end
//! above the upper end is an error; a bound that does not evaluate — an
//! unbound feature, a symbolic expression — stays undecided.
use super::user_rows;
use crate::{eval::Value, json::ResolvedModel, model::Model, rational::Rational};
use std::fmt;
use sysmlv2_syntax::diag::Diagnostic;

/// Ordered numeric endpoints without rounding exact values through a double.
/// Infinities stay distinct from finite integers beyond the double range.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum NumericBound {
    NegativeInfinity,
    Finite(Rational),
    Infinity,
}

impl NumericBound {
    pub(super) fn from_value(value: Value) -> Option<Self> {
        match value {
            Value::Integer(n) => Some(Self::Finite(Rational::from_integer(n))),
            Value::Rational(n) => Some(Self::Finite(n)),
            Value::Real(n) if n == f64::INFINITY => Some(Self::Infinity),
            Value::Real(n) if n == f64::NEG_INFINITY => Some(Self::NegativeInfinity),
            Value::Real(n) => Rational::from_f64(n).map(Self::Finite),
            _ => None,
        }
    }

    pub(super) fn is_natural(&self, upper: bool) -> bool {
        match self {
            Self::Finite(n) => n.is_integer() && n >= &Rational::zero(),
            Self::Infinity => upper,
            Self::NegativeInfinity => false,
        }
    }

    pub(super) fn zero() -> Self {
        Self::Finite(Rational::zero())
    }
}

impl fmt::Display for NumericBound {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NegativeInfinity => f.write_str("-inf"),
            Self::Finite(n) => n.fmt(f),
            Self::Infinity => f.write_str("inf"),
        }
    }
}

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    let sites = user_rows(&r.b, model, r.b.multiplicities.iter(), |row| row.0);
    for (owner, scope, mult) in sites {
        // Identity-spelled references are bound within their source unit.
        let origin = r.b.set_identity_origin(owner);
        let upper = crate::eval::evaluate_expr_in(&mut r.b, scope, &mult.upper).ok();
        let lower = match &mult.lower {
            Some(l) => crate::eval::evaluate_expr_in(&mut r.b, scope, l).ok(),
            None => None,
        };
        r.b.identity_origin_unit = origin;
        // Unknown symbolic bounds remain undecided. A known scalar of the
        // wrong kind, fractional count, or collection is not a multiplicity.
        // Infinity denotes an unbounded upper end, never a lower end.
        for (value, upper_end, span) in [
            (upper.as_ref(), true, mult.upper.span),
            (
                lower.as_ref(),
                false,
                mult.lower.as_ref().map_or(mult.span, |e| e.span),
            ),
        ] {
            let invalid = match value {
                None | Some(Value::Indeterminate | Value::Unbound(_) | Value::UnboundMember(_)) => {
                    false
                }
                Some(Value::Integer(_)) => false,
                Some(Value::Rational(v)) => !v.is_integer(),
                Some(Value::Real(v)) => {
                    !(v.is_finite() && v.fract() == 0.0 || upper_end && *v == f64::INFINITY)
                }
                Some(_) => true,
            };
            if invalid {
                out.push((
                    r.b.unit_of_elem(owner),
                    Diagnostic::error(
                        span,
                        "multiplicity bound must be a Natural number (or `*` for the upper bound)",
                    ),
                ));
            }
        }
        let lo = lower.and_then(NumericBound::from_value);
        let hi = upper.and_then(NumericBound::from_value);
        if let Some(lo) = &lo {
            if lo < &NumericBound::zero() {
                out.push((
                    r.b.unit_of_elem(owner),
                    Diagnostic::error(mult.span, "multiplicity lower bound is negative"),
                ));
                continue;
            }
        }
        if let Some(hi) = &hi {
            if hi < &NumericBound::zero() {
                out.push((
                    r.b.unit_of_elem(owner),
                    Diagnostic::error(mult.span, "multiplicity upper bound is negative"),
                ));
                continue;
            }
        }
        if let (Some(lo), Some(hi)) = (lo, hi) {
            if lo > hi {
                out.push((
                    r.b.unit_of_elem(owner),
                    Diagnostic::error(
                        mult.span,
                        format!("multiplicity lower bound {lo} exceeds upper bound {hi}"),
                    ),
                ));
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bound_checks_restore_the_callers_source_origin_on_every_exit() {
        let mut model = Model::new();
        model.add_source("first.kerml", "package A;");
        model.add_source(
            "second.kerml",
            "package B {
            feature n = -1; feature bad[n]; multiplicity wrong[3..2];
            feature unknown; feature skipped[unknown]; class C; feature boundObject : C;
            feature fTyped[boundObject]; feature identity['bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb']; class Base { feature x[1]; }
            class Child specializes Base { feature y[2] subsets x; feature z[unknown] subsets x; }
            class ReceiverBase { feature n default = 3; feature x[0..n]; }
            class ReceiverChild specializes ReceiverBase { feature n redefines ReceiverBase::n = -1; feature y redefines x; }
        }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let n = r.resolve_qualified("B::n").unwrap();
        let id = "bbbbbbbb-bbbb-4bbb-8bbb-bbbbbbbbbbbb".parse().unwrap();
        r.override_ids(&std::collections::HashMap::from([(r.element_id(n), id)]));
        assert!(r.bind_id_spelled_references().contains(&id));
        let previous = r.b.set_identity_origin(n.0);
        assert_eq!(r.b.identity_origin_unit, Some(1));
        r.b.identity_origin_unit = previous;
        for origin in [Some(0), None] {
            r.b.identity_origin_unit = origin;
            let findings = crate::check::validate_semantics_with(&mut r, &model);
            assert_eq!(findings.len(), 6, "{findings:?}");
            assert_eq!(r.b.identity_origin_unit, origin);
        }
    }

    #[test]
    fn numeric_endpoints_preserve_exact_values_and_infinity() {
        let convert = |v| NumericBound::from_value(v).unwrap();
        let exact = convert(Value::Integer(9_007_199_254_740_993));
        let real = convert(Value::Real(9_007_199_254_740_992.0));
        assert!(exact > real);
        assert!(real.is_natural(false));
        let huge = convert(Value::Rational(Rational::parse_decimal("1e400").unwrap()));
        assert!(huge > exact && huge < NumericBound::Infinity);
        assert!(huge.is_natural(false));
        assert_eq!(convert(Value::Real(-0.0)), NumericBound::zero());
        for n in [0.5, -0.5, -1.0, f64::NEG_INFINITY] {
            let bound = convert(Value::Real(n));
            assert!(!bound.is_natural(false));
            assert!(!bound.is_natural(true));
        }
        let tiny = convert(Value::Rational(Rational::parse_decimal("-1e-400").unwrap()));
        assert!(tiny < NumericBound::zero());
        assert!(!tiny.is_natural(true));
        assert!(!NumericBound::Infinity.is_natural(false));
        assert!(NumericBound::Infinity.is_natural(true));
        assert_eq!(convert(Value::Real(f64::INFINITY)), NumericBound::Infinity);
        assert!(NumericBound::from_value(Value::Real(f64::NAN)).is_none());
        assert!(NumericBound::from_value(Value::Indeterminate).is_none());
        assert!(NumericBound::from_value(Value::Boolean(true)).is_none());
    }
}
