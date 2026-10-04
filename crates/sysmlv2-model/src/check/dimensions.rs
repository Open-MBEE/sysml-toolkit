//! Conservative dimensional inference for arithmetic over unbound quantities.
//! Unknown types stay unknown; no runtime value is invented to type-check an
//! expression. The existing quantity library supplies the dimension algebra.

use crate::{
    eval::{self, Value},
    json::{ElementRef, ResolvedModel},
    model::Model,
    quantity::QuantityDims,
};
use std::collections::HashMap;
use sysmlv2_syntax::{Span, ast::*, diag::Diagnostic};

#[derive(Clone)]
enum Dimension {
    Known(QuantityDims),
    Zero,
    Unknown,
}

pub(super) fn known(r: &mut ResolvedModel, scope: usize, expr: &Expr) -> Option<QuantityDims> {
    let mut infer = Inference {
        model: r,
        features: HashMap::new(),
        types: HashMap::new(),
        units: HashMap::new(),
        findings: Vec::new(),
    };
    match infer.expr(scope, expr) {
        Dimension::Known(d) => Some(d),
        _ => None,
    }
}

struct Inference<'a> {
    model: &'a mut ResolvedModel,
    features: HashMap<usize, Dimension>,
    types: HashMap<usize, Dimension>,
    units: HashMap<Vec<(usize, i32, i32)>, Dimension>,
    findings: Vec<(Span, String)>,
}

impl Inference<'_> {
    fn feature(&mut self, e: usize) -> Dimension {
        if let Some(d) = self.features.get(&e) {
            return d.clone();
        }
        // Also cuts recursive derived values and recursive type relationships.
        self.features.insert(e, Dimension::Unknown);
        let mut result = Dimension::Unknown;
        for ty in self.model.b.direct_typing_elems(e) {
            let dimension = if let Some(d) = self.types.get(&ty) {
                d.clone()
            } else {
                let d = if crate::metaclass::conforms(self.model.b.elements[ty].ty, "DataType") {
                    if let Some(d) = self.model.quantity_dims_of_type(ElementRef(ty)) {
                        Dimension::Known(d)
                    } else {
                        // Real/Integer are not a proof of dimension one:
                        // quantity value types specialize the numeric tower.
                        // Only a measurement reference or an actual numeric
                        // value establishes a dimension here.
                        Dimension::Unknown
                    }
                } else {
                    Dimension::Unknown
                };
                self.types.insert(ty, d.clone());
                d
            };
            if matches!(dimension, Dimension::Known(_)) {
                result = dimension;
                break;
            }
        }
        if matches!(result, Dimension::Unknown) {
            for base in self.model.b.explicit_specialization_elems(e) {
                if matches!(base.0, "Subsetting" | "Redefinition") {
                    let d = self.feature(base.1);
                    if matches!(d, Dimension::Known(_)) {
                        result = d;
                        break;
                    }
                }
            }
        }
        if matches!(result, Dimension::Unknown) {
            if let Some((scope, expr)) = self.model.b.values.get(&e).cloned() {
                // Diagnostics belong to the value's own traversal, not every
                // reference to it in a different file.
                let before = self.findings.len();
                let origin = self.model.b.set_identity_origin(e);
                let d = self.expr(scope, &expr);
                self.model.b.identity_origin_unit = origin;
                self.findings.truncate(before);
                result = d;
            }
        }
        self.features.insert(e, result.clone());
        result
    }

    fn compatible(&mut self, left: Dimension, right: Dimension, span: Span) -> Dimension {
        match (left, right) {
            (Dimension::Known(a), Dimension::Known(b)) => {
                if a != b {
                    self.findings.push((
                        span,
                        format!(
                            "expression combines incompatible quantity dimensions `{}` and `{}`",
                            a.render(self.model),
                            b.render(self.model)
                        ),
                    ));
                    Dimension::Unknown
                } else {
                    Dimension::Known(a)
                }
            }
            (d, Dimension::Zero) | (Dimension::Zero, d) => d,
            _ => Dimension::Unknown,
        }
    }

    fn target(&mut self, scope: usize, expr: &Expr) -> Option<usize> {
        match &expr.kind {
            ExprKind::Ref(qn) => self.model.b.resolve(scope, qn, 0),
            ExprKind::ChainStep {
                target,
                member: TargetRef::Name(qn),
            } => {
                let target = self.target(scope, target)?;
                self.model
                    .member_of(ElementRef(target), qn)
                    .map(|(e, _)| e.0)
            }
            _ => None,
        }
    }

    fn expr(&mut self, scope: usize, expr: &Expr) -> Dimension {
        use BinaryOp as B;
        use Dimension as D;
        use ExprKind as E;
        match &expr.kind {
            E::Literal(Literal::Integer(_) | Literal::Real(_)) => {
                match eval::evaluate_expr_in(&mut self.model.b, scope, expr) {
                    // A literal `0.0` canonicalizes to the integer arm; the
                    // double arm covers a computed approximate zero.
                    Ok(Value::Integer(0)) => D::Zero,
                    Ok(Value::Real(0.0)) => D::Zero,
                    _ => D::Known(QuantityDims::dimensionless()),
                }
            }
            E::Ref(_) | E::ChainStep { .. } => self
                .target(scope, expr)
                .map_or(D::Unknown, |e| self.feature(e)),
            E::Unary {
                operand,
                op: UnaryOp::Plus | UnaryOp::Minus,
            } => self.expr(scope, operand),
            E::Binary { op, lhs, rhs } => {
                let a = self.expr(scope, lhs);
                let b = self.expr(scope, rhs);
                match op {
                    B::Add | B::Sub | B::Rem => self.compatible(a, b, expr.span),
                    B::Eq | B::NotEq | B::Lt | B::Gt | B::LtEq | B::GtEq => {
                        self.compatible(a, b, expr.span);
                        D::Unknown
                    }
                    B::Mul | B::Div => match (a, b) {
                        (D::Known(a), D::Known(b)) => {
                            a.product(&b, *op == B::Div).map_or(D::Unknown, D::Known)
                        }
                        (D::Zero, _) | (_, D::Zero) => D::Zero,
                        _ => D::Unknown,
                    },
                    B::Pow | B::Caret => {
                        let exponent = match eval::evaluate_expr_in(&mut self.model.b, scope, rhs) {
                            Ok(Value::Integer(n)) => i32::try_from(n).ok(),
                            _ => None,
                        };
                        match (a, exponent) {
                            (D::Known(a), Some(n)) => a.pow(n).map_or(D::Unknown, D::Known),
                            _ => D::Unknown,
                        }
                    }
                    _ => D::Unknown,
                }
            }
            E::Bracket { target, arg } => {
                self.expr(scope, target);
                let unit_probe = Expr {
                    span: expr.span,
                    kind: E::Bracket {
                        target: Box::new(Expr {
                            span: target.span,
                            kind: E::Literal(Literal::Integer("1".into())),
                        }),
                        arg: arg.clone(),
                    },
                };
                match eval::evaluate_expr_in(&mut self.model.b, scope, &unit_probe) {
                    Ok(Value::Quantity(_, unit)) => {
                        // Measurement dimensions depend on resolved bases and
                        // exponents, not magnitude, scale, or display spelling.
                        // Repeated unit literals must not rewalk their library
                        // power-factor declarations for every occurrence.
                        let key: Vec<_> =
                            unit.dims.iter().map(|d| (d.elem, d.num, d.den)).collect();
                        if let Some(d) = self.units.get(&key) {
                            d.clone()
                        } else {
                            let d = self
                                .model
                                .unit_quantity_dims(&unit)
                                .map_or(D::Unknown, D::Known);
                            self.units.insert(key, d.clone());
                            d
                        }
                    }
                    _ => D::Unknown,
                }
            }
            E::Conditional {
                cond,
                then_branch,
                else_branch,
            } => {
                self.expr(scope, cond);
                // A constant guard has only one reachable branch. Otherwise
                // branches may legitimately be a union of differently-typed
                // values: do not require their dimensions to agree.
                match eval::evaluate_expr_in(&mut self.model.b, scope, cond) {
                    Ok(Value::Boolean(true)) => self.expr(scope, then_branch),
                    Ok(Value::Boolean(false)) => self.expr(scope, else_branch),
                    _ => {
                        let a = self.expr(scope, then_branch);
                        let b = self.expr(scope, else_branch);
                        match (a, b) {
                            (D::Known(a), D::Known(b)) if a == b => D::Known(a),
                            _ => D::Unknown,
                        }
                    }
                }
            }
            E::Invocation { args, .. } | E::Constructor { args, .. } => {
                for arg in args {
                    self.expr(scope, &arg.value);
                }
                D::Unknown
            }
            E::Sequence(items) => {
                for item in items {
                    self.expr(scope, item);
                }
                D::Unknown
            }
            E::Index { target, index } => {
                self.expr(scope, index);
                self.expr(scope, target)
            }
            E::Unary { operand, .. } => {
                self.expr(scope, operand);
                D::Unknown
            }
            // Lambda bodies need their own parameter scope. Unmodelled
            // operators are deliberately unknown rather than guessed.
            _ => D::Unknown,
        }
    }
}

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    if r.resolve_qualified("Quantities::QuantityValue").is_none() {
        return Vec::new();
    }
    let mut sites: Vec<_> =
        r.b.values
            .iter()
            .filter(|(e, _)| super::user_owned(&r.b, model, **e))
            .map(|(&e, (s, x))| (e, *s, x.clone()))
            .collect();
    sites.extend(
        r.b.result_exprs
            .iter()
            .filter(|row| super::user_owned(&r.b, model, row.0))
            .cloned(),
    );
    sites.sort_by_key(|(e, _, x)| (*e, x.span.start));
    let mut infer = Inference {
        model: r,
        features: HashMap::new(),
        types: HashMap::new(),
        units: HashMap::new(),
        findings: Vec::new(),
    };
    let mut out = Vec::new();
    for (owner, scope, expr) in sites {
        let unit = infer.model.b.unit_of_elem(owner);
        if model.is_library_unit(unit) {
            continue;
        }
        let origin = infer.model.b.set_identity_origin(owner);
        infer.expr(scope, &expr);
        infer.model.b.identity_origin_unit = origin;
        out.extend(
            infer
                .findings
                .drain(..)
                .map(|(span, message)| (unit, Diagnostic::warning(span, message))),
        );
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::check::facts::Facts;

    #[test]
    fn checker_tail_restores_active_origin_on_errors_unknowns_and_cycles() {
        let mut model = Model::new();
        model.add_library_source("lib.kerml", "package Quantities { datatype QuantityValue; } package ScalarValues { datatype Boolean; datatype Integer; }");
        model.add_source("user.kerml", "package P { feature Actual=1; feature '88888888-8888-4888-8888-888888888888'=true; feature value='88888888-8888-4888-8888-888888888888'; feature unknown=missing; feature cyclic=loop; feature loop=cyclic; class Holder { feature n; } metaclass M { feature x; } metadata m:M { feature x=Holder::n; } class C { feature n=Holder::n; feature a { feature leaf; } } feature chain subsets C::a.leaf; datatype T; datatype U; feature t:T; function f { return r:U; t } }");
        model.add_source("actions.sysml", "package Actions { attribute x:ScalarValues::Integer; part def D; part p; action def Work { assign D := 1; send 1 to p; accept when x; accept after missing; } state def S { state a; state b; transition first a if x then b; } }");
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let actual = r.resolve_qualified("P::Actual").unwrap();
        let value = r.resolve_qualified("P::value").unwrap();
        let id = "88888888-8888-4888-8888-888888888888".parse().unwrap();
        r.override_ids(&HashMap::from([(r.element_id(actual), id)]));
        let expr = r.members_via(value, "FeatureValue")[0];
        let edge = r.owned_relationships(expr)[0];
        let mut hints = HashMap::from([((r.element_id(edge), "memberElement".into()), id)]);
        assert!(r.bind_id_spelled_references_with(&mut hints).contains(&id));
        let g = Facts::new(&mut r.b);
        for origin in [None, Some(0)] {
            r.b.identity_origin_unit = origin;
            validate(&mut r, &model);
            assert_eq!(r.b.identity_origin_unit, origin);
            super::super::actions::validate(&mut r, &model, &g);
            assert_eq!(r.b.identity_origin_unit, origin);
            super::super::relationships::validate(&mut r, &model, &g);
            assert_eq!(r.b.identity_origin_unit, origin);
            super::super::values::validate(&mut r, &model, &g);
            assert_eq!(r.b.identity_origin_unit, origin);
            super::super::chains::validate(&mut r, &model);
            assert_eq!(r.b.identity_origin_unit, origin);
        }
    }
}
