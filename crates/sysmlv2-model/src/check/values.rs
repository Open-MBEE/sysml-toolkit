//! Valuation and metadata contracts. Missing types remain undecided.
use super::facts::{Facts, is};
use crate::{
    json::{ElementRef, ResolvedModel},
    model::Model,
};
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(
    r: &mut ResolvedModel,
    model: &Model,
    g: &Facts,
) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    // End features that a connector claims, indexed once for the walk.
    let connected: std::collections::HashSet<usize> =
        r.b.connector_ends.iter().map(|(_, end, _)| *end).collect();
    for e in 0..r.b.explicit_len() {
        let unit = r.b.unit_of_elem(e);
        if model.is_library_unit(unit) {
            continue;
        }
        let span = g.span(&r.b, e);
        if let Some((_, value)) = r.b.values.get(&e) {
            if g.redefined(&r.b, e)
                .iter()
                .any(|t| r.b.values.contains_key(t) && !r.b.default_values.contains(t))
            {
                out.push((unit, super::rule_error(value.span, "validateFeatureValueOverriding",
                    "Cannot override an inherited binding value; the redefined value must be default")));
            }
        }
        if is(&r.b, e, "EnumerationUsage") {
            if let Some((_, expr)) = r.b.values.get(&e) {
                if matches!(expr.kind, sysmlv2_syntax::ast::ExprKind::Body { .. }) {
                    out.push((
                        unit,
                        super::rule_error(
                            expr.span,
                            "validateEnumerationUsageType",
                            "An expression body is not a value of the owning enumeration",
                        ),
                    ));
                }
            }
        }
        if super::facts::flag(&r.b, e, "isEnd") && !connected.contains(&e) {
            if let Some((lo, hi)) = r.declared_multiplicity(ElementRef(e)) {
                if lo != 1.0 || hi != 1.0 {
                    out.push((
                        unit,
                        super::rule_warning(
                            span,
                            "validateFeatureEndFeatureMultiplicity",
                            "An end feature should have multiplicity 1..1",
                        ),
                    ));
                }
            }
        }
        if !is(&r.b, e, "MetadataFeature") || g.typed(&r.b, e).is_empty() {
            continue;
        }
        let offered = g
            .typed(&r.b, e)
            .into_iter()
            .flat_map(|t| g.effective_members(&r.b, t))
            .collect::<Vec<_>>();
        let mut stack = vec![(e, offered)];
        while let Some((owner, offered)) = stack.pop() {
            for &m in &g.members[owner] {
                if !is(&r.b, m, "Feature")
                    || is(&r.b, m, "MetadataFeature")
                    || !r.b.elements[m]
                        .owning_relationship
                        .is_some_and(|rel| is(&r.b, rel, "FeatureMembership"))
                {
                    continue;
                }
                let targets = g.relations(&r.b, m, "Redefinition", "redefinedFeature");
                let name = r.b.elements[m].props.get("declaredName");
                let implicit: Vec<_> = offered
                    .iter()
                    .copied()
                    .filter(|&t| {
                        name.is_some_and(|n| n.is_string())
                            && name == r.b.elements[t].props.get("declaredName")
                    })
                    .collect();
                let target = if targets.is_empty() {
                    (implicit.len() == 1).then(|| implicit[0])
                } else {
                    (targets.len() == 1 && offered.contains(&targets[0])).then(|| targets[0])
                };
                if let Some(t) = target {
                    stack.push((m, g.effective_members(&r.b, t)));
                } else {
                    out.push((unit, super::rule_error(g.span(&r.b, m), "validateMetadataFeatureBody",
                        "A metadata body feature must redefine one feature of its metadata type")));
                }
                if let Some((scope, expr)) = r.b.values.get(&m).cloned() {
                    if super::expressions::model_level(&mut r.b, g, scope, &expr, 0) == Some(false)
                    {
                        out.push((
                            unit,
                            super::rule_error(
                                expr.span,
                                "validateMetadataFeatureBody",
                                "A metadata body value must be model-level evaluable",
                            ),
                        ));
                    }
                }
            }
        }
    }
    for (e, scope, mult) in super::user_rows(&r.b, model, r.b.multiplicities.iter(), |row| row.0) {
        let unit = r.b.unit_of_elem(e);
        for expr in mult.lower.iter().chain(std::iter::once(&mult.upper)) {
            let ts = super::expressions::types(&mut r.b, g, scope, expr, 0);
            if !ts.is_empty() && ts.iter().all(|&t| !is(&r.b, t, "DataType")) {
                out.push((
                    unit,
                    super::rule_error(
                        expr.span,
                        "validateMultiplicityRangeResultTypes",
                        "A multiplicity bound must have a Natural result",
                    ),
                ));
            }
        }
    }
    for (annotated, metas) in super::user_entries(&r.b, model, r.b.metadata_of.iter()) {
        let unit = r.b.unit_of_elem(annotated);
        for meta in metas {
            let candidates: Vec<_> = g
                .effective_members(&r.b, meta)
                .into_iter()
                .filter(|&member| {
                    g.closure(member)
                        .iter()
                        .any(|&f| g.named(&r.b, f, "Metaobjects::Metaobject::annotatedElement"))
                })
                .collect();
            // Separate subsetting features specify alternative permitted
            // metaclasses; a single feature's multiple types are conjunctive.
            let specific: Vec<_> = candidates
                .iter()
                .copied()
                .filter(|t| {
                    !candidates
                        .iter()
                        .any(|other| other != t && g.closure(*other).contains(t))
                })
                .collect();
            if let Some(reflection) = r.b.reflection_metaclass(r.b.elements[annotated].ty) {
                let actual = g.context(reflection);
                let allowed: Vec<_> = specific.iter().map(|&m| g.typed(&r.b, m)).collect();
                if !allowed.is_empty()
                    && allowed.iter().all(|ts| !ts.is_empty())
                    && !allowed
                        .iter()
                        .any(|ts| ts.iter().all(|t| actual.contains(t)))
                {
                    out.push((unit, super::rule_error(g.span(&r.b, meta), "validateMetadataFeatureAnnotatedElement",
                        "The annotated element's metaclass does not conform to annotatedElement's type")));
                }
            }
        }
    }
    out
}
