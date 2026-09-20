//! Declared and implied relationship contracts over resolved graph facts.
use super::{
    expressions,
    facts::{Facts, flag, is},
};
use crate::{
    json::{Builder, ResolvedModel},
    model::Model,
};
use sysmlv2_syntax::{
    Span,
    ast::{Expr, ExprKind, TargetRef},
    diag::Diagnostic,
};

pub(super) fn featured_within(b: &Builder, g: &Facts, feature: usize, context: usize) -> bool {
    let mut featuring = g.relations(b, feature, "TypeFeaturing", "featuringType");
    if let Some(o) = g.featuring(b, feature) {
        featuring.push(o);
    }
    if featuring.is_empty() {
        return true;
    }
    let mut current = Some(context);
    let mut seen = std::collections::HashSet::new();
    while let Some(context) = current {
        if !seen.insert(context) {
            break;
        }
        let contexts = g.context(context);
        if featuring.iter().any(|f| contexts.contains(f)) {
            return true;
        }
        current = g.owner[context];
    }
    false
}

/// Binding is symmetric and permits multiple classification. Unknown types do
/// not prove a mismatch; every known type on either side needs a conforming peer.
pub(super) fn incompatible(b: &mut Builder, g: &Facts, a: &[usize], z: &[usize]) -> bool {
    if a.is_empty() || z.is_empty() {
        return false;
    }
    !a.iter().any(|&x| {
        z.iter().any(|&y| {
            g.context(x).contains(&y)
                || g.context(y).contains(&x)
                || b.conforms_upward_semantic(x, y)
                || b.conforms_upward_semantic(y, x)
        })
    })
}
fn subject(b: &Builder, g: &Facts, e: usize) -> Option<usize> {
    g.effective_members(b, e).into_iter().find(|&m| {
        b.elements[m]
            .owning_relationship
            .is_some_and(|r| is(b, r, "SubjectMembership"))
    })
}
pub(super) fn validate(
    r: &mut ResolvedModel,
    model: &Model,
    g: &Facts,
) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    let mut errors = Vec::new();
    let mut bindings: Vec<(usize, Span, Vec<usize>, Vec<usize>)> = Vec::new();
    for e in 0..r.b.explicit_len() {
        let b = &r.b;
        let unit = b.unit_of_elem(e);
        if model.is_library_unit(unit) {
            continue;
        }
        let span = g.span(b, e);
        let mut report = |rule, msg| errors.push((unit, span, rule, msg));
        let ends: Vec<_> = if is(b, e, "Association") || is(b, e, "Connector") {
            g.effective_members(b, e)
                .into_iter()
                .filter(|&m| flag(b, m, "isEnd"))
                .collect()
        } else {
            Vec::new()
        };
        if is(b, e, "BindingConnector") {
            if !ends.is_empty() && ends.len() != 2 {
                report(
                    "validateBindingConnectorIsBinary",
                    "A binding connector must have exactly two ends",
                );
            }
            if let [a, z] = ends.as_slice() {
                bindings.push((unit, span, g.typed(b, *a), g.typed(b, *z)));
            }
        }
        if is(b, e, "Connector") && !flag(b, e, "isAbstract") && ends.len() == 1 {
            report(
                "validateConnectorRelatedFeatures",
                "A concrete connector must relate at least two features",
            );
        }
        if is(b, e, "Association")
            && ends.len() > 2
            && g.closure(e)
                .iter()
                .any(|&t| g.named(b, t, "Links::BinaryLink"))
        {
            report(
                "validateAssociationBinarySpecialization",
                "An association with more than two ends cannot specialize BinaryLink",
            );
        }
        let inline_cross = b.owned_cross_features.get(&e).copied();
        if let Some(cross) = inline_cross {
            let mut a = g.typed(b, e);
            let mut z = g.typed(b, cross);
            a.sort_unstable();
            a.dedup();
            z.sort_unstable();
            z.dedup();
            if !a.is_empty() && !z.is_empty() && a != z {
                report(
                    "validateFeatureCrossFeatureType",
                    "An inline cross feature must have the same types as its end feature",
                );
            }
            if !g
                .relations(b, e, "CrossSubsetting", "crossedFeature")
                .is_empty()
            {
                report(
                    "feature-cross-feature-single",
                    "An end cannot declare both an inline cross feature and a cross subsetting",
                );
            }
        }
        for crossed in g.relations(b, e, "CrossSubsetting", "crossedFeature") {
            let owner_ends = g
                .featuring(b, e)
                .map(|o| {
                    g.effective_members(b, o)
                        .into_iter()
                        .filter(|&m| flag(b, m, "isEnd"))
                        .count()
                })
                .unwrap_or(0);
            if !flag(b, e, "isEnd") || owner_ends < 2 {
                report(
                    "validateCrossSubsettingCrossingFeature",
                    "A crossing feature must be an end of a type with at least two ends",
                );
            } else {
                let links = g.relations(b, crossed, "FeatureChaining", "chainingFeature");
                let other = g
                    .featuring(b, e)
                    .map(|o| {
                        g.effective_members(b, o)
                            .into_iter()
                            .filter(|&m| flag(b, m, "isEnd") && m != e)
                            .collect::<Vec<_>>()
                    })
                    .unwrap_or_default();
                if links.len() != 2 || (other.len() == 1 && links.first() != other.first()) {
                    report(
                        "validateCrossSubsettingCrossedFeature",
                        "A cross subsetting must chain through an opposite end to a feature",
                    );
                }
                if let Some(&terminal) = links.last() {
                    for redefined in g.redefined(b, e) {
                        for old_cross in
                            g.relations(b, redefined, "CrossSubsetting", "crossedFeature")
                        {
                            if let Some(old_terminal) = g
                                .relations(b, old_cross, "FeatureChaining", "chainingFeature")
                                .last()
                            {
                                if !g.closure(terminal).contains(old_terminal) {
                                    report(
                                        "validateFeatureCrossFeatureSpecialization",
                                        "A cross feature must specialize the cross feature of the redefined end",
                                    );
                                }
                            }
                        }
                    }
                }
                let mut a = g.typed(b, e);
                let mut z = g.typed(b, crossed);
                a.sort_unstable();
                a.dedup();
                z.sort_unstable();
                z.dedup();
                if !a.is_empty() && !z.is_empty() && a != z {
                    report(
                        "validateFeatureCrossFeatureType",
                        "A cross feature must have the same types as its end feature",
                    );
                }
            }
        }
        let chain = g.relations(b, e, "FeatureChaining", "chainingFeature");
        for pair in chain.windows(2) {
            if !is(b, pair[1], "Feature") || !featured_within(b, g, pair[1], pair[0]) {
                report(
                    "validateFeatureChainingFeatureConformance",
                    "Each chain member must be a feature accessible through the preceding feature",
                );
            }
        }
        for original in g.relations(b, e, "Conjugation", "originalType") {
            if is(b, e, "Feature") && is(b, original, "Classifier") && g.typed(b, e).is_empty() {
                report(
                    "validateFeatureHasType",
                    "Conjugating a classifier does not provide a feature type",
                );
            }
            if is(b, e, "Structure") && !g.closure(original).iter().any(|&t| is(b, t, "Structure"))
            {
                report(
                    "validateClassifierDefaultSupertype",
                    "A structure must directly or indirectly specialize Objects::Object",
                );
            }
        }
        if is(b, e, "Specialization") {
            let specific = [
                "specific",
                "subclassifier",
                "subsettingFeature",
                "typedFeature",
                "redefiningFeature",
            ]
            .iter()
            .find_map(|key| g.target(b, e, key));
            if let Some(s) = specific {
                if !g.relations(b, s, "Conjugation", "originalType").is_empty() {
                    report(
                        "validateSpecializationSpecificNotConjugated",
                        "A conjugated type cannot be the specific type of a specialization",
                    );
                }
            }
        }
        if r.b.elements[e].ty == "RequirementUsage" {
            if let (Some(s), Some(parent)) =
                (subject(b, g, e), g.owner[e].and_then(|o| subject(b, g, o)))
            {
                bindings.push((unit, span, g.typed(b, s), g.typed(b, parent)));
            }
        }
    }
    for (i, (e, kind, _, qn)) in r.b.spec_targets.iter().enumerate() {
        if *kind != "Subsetting" {
            continue;
        }
        let Some(t) = r.b.spec_resolved.get(i).copied().flatten() else {
            continue;
        };
        let unit = r.b.unit_of_elem(*e);
        if model.is_library_unit(unit) {
            continue;
        }
        if let Some(context) = g.featuring(&r.b, *e) {
            if !featured_within(&r.b, g, t, context) {
                errors.push((
                    unit,
                    qn.span,
                    "validateSubsettingFeaturingTypes",
                    "A subsetted feature must be accessible in the subsetting feature's context",
                ));
            }
        }
    }
    for end in 0..r.b.explicit_len() {
        let b = &r.b;
        let unit = b.unit_of_elem(end);
        if model.is_library_unit(unit) || !is(b, end, "FlowEnd") {
            continue;
        }
        if !g
            .relations(b, end, "ReferenceSubsetting", "referencedFeature")
            .is_empty()
        {
            continue;
        }
        let Some(flow) = g.owner[end] else {
            continue;
        };
        let Some(context) = g.featuring(b, flow) else {
            continue;
        };
        for &member in &g.members[end] {
            for target in g.relations(b, member, "Redefinition", "redefinedFeature") {
                if let Some(featuring) = g.featuring(b, target) {
                    if featured_within(b, g, target, context) {
                        if !b.payload_flows.contains(&flow) {
                            continue;
                        }
                        errors.push((unit, g.span(b, flow), "validateFlowEndSubsetting", "A flow end must identify a participant's payload feature using dot notation"));
                    } else {
                        let rule = if is(b, featuring, "Classifier") {
                            "validateFlowEndSubsetting"
                        } else {
                            "validateFlowEndImplicitSubsetting"
                        };
                        errors.push((unit, g.span(b, flow), rule, "A nested flow end must identify an accessible feature using dot notation"));
                    }
                }
            }
        }
    }
    for (e, (scope, expr)) in super::user_entries(&r.b, model, r.b.values.iter()) {
        let unit = r.b.unit_of_elem(e);
        if let ExprKind::Ref(_) = &expr.kind {
            if let (Some(context), Some(t)) = (
                g.featuring(&r.b, e),
                expressions::referent(&mut r.b, scope, &expr),
            ) {
                if !featured_within(&r.b, g, t, context) {
                    errors.push((
                        unit,
                        expr.span,
                        "validateConnectorTypeFeaturing",
                        "A bound feature reference must be accessible in the binding's context",
                    ));
                }
            }
        }
    }
    for (e, scope, expr) in super::user_rows(&r.b, model, r.b.result_exprs.iter(), |row| row.0) {
        let unit = r.b.unit_of_elem(e);
        let returns: Vec<_> = g
            .effective_members(&r.b, e)
            .into_iter()
            .filter(|&m| {
                r.b.elements[m]
                    .owning_relationship
                    .is_some_and(|rel| is(&r.b, rel, "ReturnParameterMembership"))
            })
            .collect();
        if let [ret] = returns.as_slice() {
            let a = g.typed(&r.b, *ret);
            let z = expressions::types(&mut r.b, g, scope, &expr, 0);
            bindings.push((unit, expr.span, a, z));
        }
    }
    for (e, scope, target) in super::user_rows(&r.b, model, r.b.satisfy_by.iter(), |row| row.0) {
        let unit = r.b.unit_of_elem(e);
        if let (Some(s), TargetRef::Name(qn)) =
            (subject(&r.b, g, g.feature_target(&r.b, e)), target)
        {
            let span = qn.span;
            let a = g.typed(&r.b, s);
            let z = expressions::types(
                &mut r.b,
                g,
                scope,
                &Expr {
                    kind: ExprKind::Ref(qn),
                    span,
                },
                0,
            );
            bindings.push((unit, span, a, z));
        }
    }
    for (unit, span, a, z) in bindings {
        if incompatible(&mut r.b, g, &a, &z) {
            let names = |ts: &[usize]| {
                ts.iter()
                    .map(|&t| {
                        r.b.elements[t]
                            .props
                            .get("declaredName")
                            .and_then(|v| v.as_str())
                            .unwrap_or("<unnamed>")
                    })
                    .collect::<Vec<_>>()
                    .join(", ")
            };
            out.push((
                unit,
                super::rule_warning(
                    span,
                    "validateBindingConnectorTypeConformance",
                    format!(
                        "Bound feature types ({}) and ({}) should conform",
                        names(&a),
                        names(&z)
                    ),
                ),
            ));
        }
    }
    out.extend(
        errors
            .into_iter()
            .map(|(u, s, rule, msg)| (u, super::rule_error(s, rule, msg))),
    );
    out
}
