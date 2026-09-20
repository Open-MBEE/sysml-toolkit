//! Multiplicity bounds. A bound that provably evaluates to something
//! other than a natural number, to a negative number, or to a lower end
//! above the upper end is an error; a bound that does not evaluate — an
//! unbound feature, a symbolic expression — stays undecided.
use super::user_rows;
use crate::{json::ResolvedModel, model::Model};
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    let sites = user_rows(&r.b, model, r.b.multiplicities.iter(), |row| row.0);
    for (owner, scope, mult) in sites {
        let upper = crate::eval::evaluate_expr_in(&mut r.b, scope, &mult.upper).ok();
        let lower = match &mult.lower {
            Some(l) => crate::eval::evaluate_expr_in(&mut r.b, scope, l).ok(),
            None => None,
        };
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
            use crate::eval::Value;
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
        let lo = lower.as_ref().and_then(super::scalar_f64);
        let hi = upper.as_ref().and_then(super::scalar_f64);
        if let Some(lo) = lo {
            if lo < 0.0 {
                out.push((
                    r.b.unit_of_elem(owner),
                    Diagnostic::error(mult.span, "multiplicity lower bound is negative"),
                ));
                continue;
            }
        }
        if let Some(hi) = hi {
            if hi < 0.0 {
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
