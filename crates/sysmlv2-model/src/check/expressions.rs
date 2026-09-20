//! Static expression contracts, independent of whether values can be evaluated.
use super::facts::{Facts, is};
use crate::{json::ResolvedModel, model::Model};
use std::collections::HashSet;
use sysmlv2_syntax::{
    ast::{BinaryOp, ClassificationOp, Expr, ExprKind, Literal, Name, QualifiedName, TargetRef},
    diag::Diagnostic,
    visit::{self, Visit},
};

pub(super) fn library_type(b: &mut crate::json::Builder, fqn: &str) -> Option<usize> {
    let span = sysmlv2_syntax::Span::default();
    b.resolve(
        0,
        &QualifiedName {
            is_global: true,
            span,
            segments: fqn
                .split("::")
                .map(|s| Name {
                    value: s.into(),
                    span,
                })
                .collect(),
        },
        0,
    )
}
pub(super) fn referent(b: &mut crate::json::Builder, scope: usize, expr: &Expr) -> Option<usize> {
    fn spine(expr: &Expr) -> Option<Vec<QualifiedName>> {
        match &expr.kind {
            ExprKind::Ref(qn) => Some(vec![qn.clone()]),
            ExprKind::ChainStep {
                target,
                member: TargetRef::Name(qn),
            } => {
                let mut parts = spine(target)?;
                parts.push(qn.clone());
                Some(parts)
            }
            _ => None,
        }
    }
    match &expr.kind {
        ExprKind::Ref(qn) => b.resolve(scope, qn, 0),
        ExprKind::ChainStep {
            target,
            member: TargetRef::Name(qn),
        } => b.resolve_chain_member(scope, spine(target).as_deref(), qn),
        _ => None,
    }
}

/// Known result types, without evaluating or supplying values to unbound inputs.
pub(super) fn types(
    b: &mut crate::json::Builder,
    g: &Facts,
    scope: usize,
    expr: &Expr,
    depth: usize,
) -> Vec<usize> {
    if depth > 32 {
        return Vec::new();
    }
    let scalar = match &expr.kind {
        ExprKind::Literal(Literal::Bool(_)) => Some("ScalarValues::Boolean"),
        ExprKind::Literal(Literal::String(_)) => Some("ScalarValues::String"),
        ExprKind::Literal(Literal::Integer(_)) => Some("ScalarValues::Integer"),
        ExprKind::Literal(Literal::Real(_)) => Some("ScalarValues::Real"),
        ExprKind::Binary {
            op:
                BinaryOp::Eq
                | BinaryOp::NotEq
                | BinaryOp::Same
                | BinaryOp::NotSame
                | BinaryOp::Lt
                | BinaryOp::LtEq
                | BinaryOp::Gt
                | BinaryOp::GtEq
                | BinaryOp::CondAnd
                | BinaryOp::CondOr
                | BinaryOp::Implies
                | BinaryOp::Xor,
            ..
        } => Some("ScalarValues::Boolean"),
        ExprKind::Classification {
            op: ClassificationOp::IsType | ClassificationOp::HasType,
            ..
        } => Some("ScalarValues::Boolean"),
        _ => None,
    };
    if let Some(name) = scalar {
        return library_type(b, name).into_iter().collect();
    }
    match &expr.kind {
        ExprKind::Ref(_) | ExprKind::ChainStep { .. } => {
            let Some(e) = referent(b, scope, expr) else {
                return Vec::new();
            };
            let ts = g.typed(b, e);
            if !ts.is_empty() {
                return ts;
            }
            if let Some((s, value)) = b.values.get(&e).cloned() {
                return types(b, g, s, &value, depth + 1);
            }
        }
        ExprKind::Constructor { ty, .. }
        | ExprKind::Classification {
            op: ClassificationOp::As,
            ty,
            ..
        } => {
            if let Some(qn) = ty.as_name() {
                return b.resolve(scope, qn, 0).into_iter().collect();
            }
        }
        ExprKind::Invocation { ty, .. } => {
            if let Some(t) = ty.as_name().and_then(|qn| b.resolve(scope, qn, 0)) {
                return g
                    .effective_members(b, t)
                    .into_iter()
                    .filter(|&m| {
                        b.elements[m]
                            .owning_relationship
                            .is_some_and(|rel| is(b, rel, "ReturnParameterMembership"))
                    })
                    .flat_map(|m| g.typed(b, m))
                    .collect();
            }
        }
        ExprKind::Binary {
            lhs,
            rhs,
            op:
                BinaryOp::Add
                | BinaryOp::Sub
                | BinaryOp::Mul
                | BinaryOp::Div
                | BinaryOp::Rem
                | BinaryOp::Pow
                | BinaryOp::Caret,
        } => {
            let a = types(b, g, scope, lhs, depth + 1);
            let z = types(b, g, scope, rhs, depth + 1);
            if !a.is_empty() && a == z {
                return a;
            }
            let numeric = |t| {
                [
                    "ScalarValues::Integer",
                    "ScalarValues::Real",
                    "ScalarValues::Rational",
                    "ScalarValues::Natural",
                    "ScalarValues::Positive",
                ]
                .iter()
                .any(|n| g.named(b, t, n))
            };
            if !a.is_empty() && !z.is_empty() && a.iter().chain(&z).all(|&t| numeric(t)) {
                return library_type(b, "ScalarValues::Real").into_iter().collect();
            }
        }
        ExprKind::Index { target, .. }
        | ExprKind::Unary {
            operand: target, ..
        } => return types(b, g, scope, target, depth + 1),
        _ => {}
    }
    Vec::new()
}

/// Whether a known static result fails a required type. An unresolved type is
/// undecided, including when the standard library is unavailable.
pub(super) fn wrong_type(
    b: &mut crate::json::Builder,
    g: &Facts,
    scope: usize,
    expr: &Expr,
    required: &str,
) -> bool {
    if matches!(
        expr.kind,
        ExprKind::Literal(
            Literal::Integer(_) | Literal::Real(_) | Literal::String(_) | Literal::Infinity
        )
    ) && matches!(
        required,
        "ScalarValues::Boolean" | "ISQ::DurationValue" | "Time::TimeInstantValue"
    ) {
        return true;
    }
    let Some(required) = library_type(b, required) else {
        return false;
    };
    let actual = types(b, g, scope, expr, 0);
    !actual.is_empty()
        && !actual
            .iter()
            .any(|&t| b.conforms_upward_semantic(t, required))
}

/// Model-level evaluability is distinct from the toolkit's ability to execute a
/// user calculation. Recursion and unresolved prerequisites remain undecided.
pub(super) fn model_level(
    b: &mut crate::json::Builder,
    g: &Facts,
    scope: usize,
    expr: &Expr,
    depth: usize,
) -> Option<bool> {
    if depth > 32 {
        return None;
    }
    let mut all = |xs: Vec<&Expr>| {
        let mut unknown = false;
        for x in xs {
            match model_level(b, g, scope, x, depth + 1) {
                Some(false) => return Some(false),
                None => unknown = true,
                Some(true) => {}
            }
        }
        if unknown { None } else { Some(true) }
    };
    match &expr.kind {
        ExprKind::Literal(_) | ExprKind::Null | ExprKind::MetadataAccess { .. } => Some(true),
        ExprKind::Binary { lhs, rhs, .. } => all(vec![lhs, rhs]),
        ExprKind::Unary {
            op: sysmlv2_syntax::ast::UnaryOp::Tilde,
            operand,
        } if matches!(
            operand.kind,
            ExprKind::Literal(Literal::Integer(_) | Literal::Real(_))
        ) =>
        {
            Some(false)
        }
        ExprKind::Unary { operand, .. } => all(vec![operand]),
        ExprKind::Conditional {
            cond,
            then_branch,
            else_branch,
        } => all(vec![cond, then_branch, else_branch]),
        ExprKind::Sequence(xs) => all(xs.iter().collect()),
        ExprKind::Constructor { args, .. } => all(args.iter().map(|a| &a.value).collect()),
        ExprKind::Index { target, index } => all(vec![target, index]),
        ExprKind::Bracket { target, arg } => all(vec![target, arg]),
        ExprKind::Collect { target, .. }
        | ExprKind::Select { target, .. }
        | ExprKind::ChainStep { target, .. } => all(vec![target]),
        ExprKind::Classification { operand: None, .. } => Some(true),
        ExprKind::Classification {
            operand: Some(operand),
            ..
        } => all(vec![operand]),
        ExprKind::Ref(qn) => {
            let e = b.resolve(scope, qn, 0)?;
            if !is(b, e, "Feature") || is(b, e, "MetadataFeature") || is(b, e, "EnumerationUsage") {
                return Some(true);
            }
            if let Some(o) = g.featuring(b, e) {
                return Some(is(b, o, "Metaclass") || is(b, o, "MetadataFeature"));
            }
            let (s, value) = b.values.get(&e)?.clone();
            model_level(b, g, s, &value, depth + 1)
        }
        ExprKind::Invocation { ty, args } => {
            let t = b.resolve(scope, ty.as_name()?, 0)?;
            let model_function = ["BaseFunctions", "DataFunctions", "ControlFunctions"]
                .iter()
                .any(|pkg| g.owner[t].is_some_and(|o| g.named(b, o, pkg)))
                && t < b.lib_boundary;
            if !model_function {
                return Some(false);
            }
            for a in args {
                if model_level(b, g, scope, &a.value, depth + 1) != Some(true) {
                    return None;
                }
            }
            Some(true)
        }
        _ => None,
    }
}

struct Expressions<'a>(Vec<&'a Expr>);
impl<'a> Visit<'a> for Expressions<'a> {
    fn visit_expr(&mut self, expr: &'a Expr) {
        self.0.push(expr);
        // These expressions introduce a new lexical scope. Their lowered
        // result expressions are checked separately with that scope.
        if !matches!(
            expr.kind,
            ExprKind::Body { .. } | ExprKind::Collect { .. } | ExprKind::Select { .. }
        ) {
            visit::walk_expr(self, expr);
        }
    }
}
pub(super) fn validate(
    r: &mut ResolvedModel,
    model: &Model,
    g: &Facts,
) -> Vec<(usize, Diagnostic)> {
    let mut roots: Vec<_> = super::user_entries(&r.b, model, r.b.values.iter())
        .into_iter()
        .map(|(o, (s, e))| (o, s, e))
        .collect();
    roots.extend(super::user_rows(
        &r.b,
        model,
        r.b.result_exprs.iter(),
        |row| row.0,
    ));
    roots.extend(
        super::user_entries(&r.b, model, r.b.contract_exprs.iter())
            .into_iter()
            .map(|(e, (s, x))| (e, s, x)),
    );
    roots.sort_by_key(|(o, _, e)| (*o, e.span.start));
    let mut out = Vec::new();
    for (owner, scope, expr) in roots {
        let unit = r.b.unit_of_elem(owner);
        let mut expressions = Expressions(Vec::new());
        expressions.visit_expr(&expr);
        for expr in expressions.0 {
            let mut report = |rule: &'static str, message: &str| {
                out.push((unit, super::rule_error(expr.span, rule, message)))
            };
            match &expr.kind {
                ExprKind::ChainStep { .. } => {
                    if let Some(t) = referent(&mut r.b, scope, expr) {
                        if !is(&r.b, t, "Feature") {
                            report(
                                "validateFeatureChainExpressionFeatureConformance",
                                "A feature-chain expression must select a feature",
                            );
                        }
                    }
                }
                ExprKind::Classification {
                    op: ClassificationOp::As,
                    operand: Some(operand),
                    ty,
                } => {
                    if let Some(t) = ty.as_name().and_then(|qn| r.b.resolve(scope, qn, 0)) {
                        let a = types(&mut r.b, g, scope, operand, 0);
                        if super::relationships::incompatible(&mut r.b, g, &a, &[t]) {
                            out.push((
                                unit,
                                super::rule_warning(
                                    expr.span,
                                    "validateOperatorExpressionCastConformance",
                                    "Cast types should conform in at least one direction",
                                ),
                            ));
                        }
                    }
                }
                ExprKind::Ref(name) => {
                    if let Some(t) = r.b.resolve(scope, name, 0) {
                        if !is(&r.b, t, "Feature") {
                            report(
                                "validateFeatureReferenceExpressionReferentIsFeature",
                                "A feature reference expression must name a feature",
                            );
                        }
                    }
                }
                ExprKind::Constructor { ty, args } => {
                    if let TargetRef::Name(name) = &**ty {
                        if let Some(t) = r.b.resolve(scope, name, 0) {
                            if !is(&r.b, t, "Type") {
                                report(
                                    "validateInstantiationExpressionInstantiatedType",
                                    "A constructor must instantiate a type",
                                );
                            }
                        }
                    }
                    let mut names = HashSet::new();
                    for arg in args {
                        if let Some(name) = &arg.name {
                            if !names.insert(name.to_display_string()) {
                                report(
                                    "validateConstructorExpressionNoDuplicateFeatureRedefinition",
                                    "A constructor cannot bind a feature more than once",
                                );
                            }
                        }
                    }
                }
                ExprKind::Invocation { ty, .. } => {
                    if let Some(t) = ty.as_name().and_then(|name| r.b.resolve(scope, name, 0)) {
                        if !is(&r.b, t, "Behavior")
                            && !is(&r.b, t, "Step")
                            && (!is(&r.b, t, "Feature") || !g.typed(&r.b, t).is_empty())
                            && !g.typed(&r.b, t).iter().any(|&t| is(&r.b, t, "Behavior"))
                        {
                            report(
                                "validateInvocationExpressionInstantiatedType",
                                "An invocation must invoke a behavior or behavioral feature",
                            );
                        }
                    }
                }
                ExprKind::Bracket { arg, .. }
                    if matches!(
                        arg.kind,
                        ExprKind::Literal(Literal::Integer(_) | Literal::Real(_))
                    ) =>
                {
                    let (rule, message) =
                        if model.unit(unit).unit.dialect == sysmlv2_syntax::ast::Dialect::Kerml {
                            (
                                "validateOperatorExpressionBracketOperator",
                                "Square brackets do not index a sequence; use #(index)",
                            )
                        } else {
                            (
                                "validateOperatorExpressionQuantity",
                                "A quantity unit must be a measurement reference",
                            )
                        };
                    out.push((unit, super::rule_warning(arg.span, rule, message)));
                }
                _ => {}
            }
        }
    }
    let filters: Vec<_> =
        r.b.filter_exprs
            .iter()
            .filter_map(|(scope, expr)| {
                let unit = r.b.unit_of_elem(r.b.nearest_scope_owner(*scope)?);
                (!model.is_library_unit(unit)).then(|| (unit, *scope, expr.clone()))
            })
            .collect();
    for (unit, scope, expr) in filters {
        if wrong_type(&mut r.b, g, scope, &expr, "ScalarValues::Boolean") {
            out.push((
                unit,
                super::rule_error(
                    expr.span,
                    "validateElementFilterMembershipIsBoolean",
                    "An element filter must have a Boolean result",
                ),
            ));
        }
        if model_level(&mut r.b, g, scope, &expr, 0) == Some(false) {
            out.push((
                unit,
                super::rule_error(
                    expr.span,
                    "validateElementFilterMembershipIsModelLevelEvaluable",
                    "An element filter must be model-level evaluable",
                ),
            ));
        }
    }
    out
}
