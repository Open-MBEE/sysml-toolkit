//! Invocation arity: a user-defined callable invoked with fewer
//! positional arguments than it declares parameters, or with a named
//! binding that names no parameter or names one twice.
use crate::{json::ResolvedModel, model::Model};
use std::collections::HashSet;
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(r: &mut ResolvedModel, model: &Model) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    // --- invocation arity ---
    // A user-defined calculation invoked with fewer positional arguments
    // than its declared `in`/`inout` parameters leaves the trailing
    // parameters unbound — the result can never compute unless they carry
    // defaults. Named bindings must name a parameter exactly once.
    // Warnings are conservatively scoped: lambda bodies skipped, and both
    // caller and callee must be outside the standard library (KFL
    // functions overload their parameter lists).
    let mut value_exprs: Vec<(usize, usize, sysmlv2_syntax::ast::Expr)> =
        r.b.values
            .iter()
            .filter(|(o, _)| !model.is_library_unit(r.b.unit_of_elem(**o)))
            .map(|(o, (s, e))| (*o, *s, e.clone()))
            .collect();
    value_exprs.extend(
        r.b.result_exprs
            .iter()
            .filter(|row| !model.is_library_unit(r.b.unit_of_elem(row.0)))
            .cloned(),
    );
    for (owner, scope, expr) in value_exprs {
        let unit = r.b.unit_of_elem(owner);
        if model.is_library_unit(unit) {
            continue;
        }
        let mut sites = Vec::new();
        collect_invocations(&expr, &mut sites);
        for (qn, args, span) in sites {
            let Some(callee) = r.b.resolve(scope, qn, 0) else {
                continue;
            };
            let Some(params) = r.b.in_params.get(&callee).cloned() else {
                continue;
            };
            if model.is_library_unit(r.b.unit_of_elem(callee)) {
                continue; // Library signatures can overload or use variadics.
            }
            if args.iter().any(|a| a.name.is_some())
                && !matches!(
                    r.b.elements[callee].ty,
                    "CalculationDefinition" | "CalculationUsage" | "Function" | "Expression"
                )
            {
                // Requirements/cases also bind implicit subject parameters;
                // in_params alone is not their complete callable signature.
                continue;
            }
            let mut bound = HashSet::new();
            let mut positional = 0;
            let mut invalid = false;
            for arg in args {
                let name = match &arg.name {
                    Some(name) => name.to_display_string(),
                    None => {
                        let Some(name) = params.get(positional) else {
                            out.push((unit, Diagnostic::warning(span, format!(
                                "invocation of `{}` supplies {} arguments for {} parameter(s)",
                                qn.to_display_string(), args.len(), params.len()
                            ))));
                            invalid = true;
                            break;
                        };
                        positional += 1;
                        name.clone()
                    }
                };
                let message = if !params.contains(&name) {
                    Some(format!(
                        "invocation of `{}` names unknown parameter `{name}`",
                        qn.to_display_string()
                    ))
                } else if !bound.insert(name.clone()) {
                    Some(format!(
                        "invocation of `{}` binds parameter `{name}` more than once",
                        qn.to_display_string()
                    ))
                } else {
                    None
                };
                if let Some(message) = message {
                    out.push((unit, Diagnostic::warning(arg.value.span, message)));
                    invalid = true;
                }
            }
            if invalid {
                continue;
            }
            let fields = r.b.ctor_fields.get(&callee);
            let missing: Vec<_> = params
                .iter()
                .filter(|name| {
                    !bound.contains(*name)
                        && !fields
                            .and_then(|fs| fs.iter().find(|(n, _)| n == *name))
                            .is_some_and(|(_, e)| r.b.values.contains_key(e))
                })
                .cloned()
                .collect();
            if !missing.is_empty() {
                out.push((
                    unit,
                    Diagnostic::warning(
                        span,
                        format!(
                            "invocation of `{}` binds {} of its {} parameters (`{}` never bound)",
                            qn.to_display_string(),
                            bound.len(),
                            params.len(),
                            missing.join("`, `")
                        ),
                    ),
                ));
            }
        }
    }
    out
}

/// Collect every all-positional invocation site in an expression:
/// `(callee, positional-argument count, span)`. Lambda bodies (`Body`,
/// arrow/collect/select bodies) are not entered — their invocations
/// bind through runtime parameters this static pass cannot see.
fn collect_invocations<'a>(
    e: &'a sysmlv2_syntax::ast::Expr,
    out: &mut Vec<(
        &'a sysmlv2_syntax::ast::QualifiedName,
        &'a [sysmlv2_syntax::ast::Arg],
        sysmlv2_syntax::Span,
    )>,
) {
    use sysmlv2_syntax::ast::{ArrowArgs, ExprKind, TargetRef};
    match &e.kind {
        ExprKind::Literal(_)
        | ExprKind::Null
        | ExprKind::Ref(_)
        | ExprKind::Extent { .. }
        | ExprKind::MetadataAccess { .. }
        | ExprKind::Body { .. }
        | ExprKind::BodyTerminator => {}
        ExprKind::Conditional {
            cond,
            then_branch,
            else_branch,
        } => {
            collect_invocations(cond, out);
            collect_invocations(then_branch, out);
            collect_invocations(else_branch, out);
        }
        ExprKind::Binary { lhs, rhs, .. } => {
            collect_invocations(lhs, out);
            collect_invocations(rhs, out);
        }
        ExprKind::Unary { operand, .. } => collect_invocations(operand, out),
        ExprKind::Classification { operand, .. } => {
            if let Some(o) = operand {
                collect_invocations(o, out);
            }
        }
        ExprKind::ChainStep { target, .. } => collect_invocations(target, out),
        ExprKind::Index { target, index } => {
            collect_invocations(target, out);
            collect_invocations(index, out);
        }
        ExprKind::Bracket { target, arg } => {
            collect_invocations(target, out);
            collect_invocations(arg, out);
        }
        ExprKind::Arrow { target, args, .. } => {
            collect_invocations(target, out);
            if let ArrowArgs::List(list) = args {
                for a in list {
                    collect_invocations(&a.value, out);
                }
            }
        }
        ExprKind::Collect { target, .. } | ExprKind::Select { target, .. } => {
            collect_invocations(target, out)
        }
        ExprKind::Invocation { ty, args } => {
            if let TargetRef::Name(qn) = &**ty {
                out.push((qn, args, e.span));
            }
            for a in args {
                collect_invocations(&a.value, out);
            }
        }
        ExprKind::Constructor { args, .. } => {
            for a in args {
                collect_invocations(&a.value, out);
            }
        }
        ExprKind::Sequence(items) => {
            for i in items {
                collect_invocations(i, out);
            }
        }
    }
}
