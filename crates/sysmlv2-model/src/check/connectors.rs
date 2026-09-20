//! Featuring accessibility of a connector's related features: some
//! candidate context — a lexical ancestor of the connector, or a
//! featuring type of one of the related features — must admit every one
//! of them.
use super::facts::Facts;
use crate::{json::ResolvedModel, model::Model};
use std::collections::HashMap;
use sysmlv2_syntax::diag::Diagnostic;

pub(super) fn validate(
    r: &mut ResolvedModel,
    model: &Model,
    facts: &Facts,
) -> Vec<(usize, Diagnostic)> {
    let mut out = Vec::new();
    // --- connector-end featuring accessibility (KerML canAccess /
    // checkConnectorTypeFeaturing) ---
    // A connector's related features must share a featuring context the
    // connector can be featured within. Statically: some candidate type T
    // — a lexical ancestor of the connector, or a featuring type of one of
    // the related features (or its ancestors) — must *admit* every
    // featured related feature, where T admits a feature featured in F
    // when T conforms to F or T (or a supertype) owns a member typed by /
    // referencing something conforming to F (the one-hop featuring lift:
    // a part that performs/exhibits a behavior gives access to the
    // behavior's features). Package-owned targets have no featuringTypes
    // and are accessible from anywhere — that is what makes the corpus's
    // sibling-namespace binds legal. Lenient by construction: unresolved
    // targets, library featuring, explicit `featured by`, and unresolved
    // chain roots all pass silently.
    {
        let is_featuring_membership = |ty: &str| {
            ty.ends_with("Membership")
                && !matches!(ty, "OwningMembership" | "Membership" | "VariantMembership")
        };
        let rel_target = |b: &crate::json::Builder, e: usize, rel_ty: &str, key: &str| {
            b.elements[e]
                .owned_relationships
                .iter()
                .find(|&&rel| b.elements[rel].ty == rel_ty)
                .and_then(|&rel| facts.target(b, rel, key))
        };
        let has_type_featuring = |b: &crate::json::Builder, e: usize| {
            b.elements[e]
                .owned_relationships
                .iter()
                .any(|&rel| b.elements[rel].ty == "TypeFeaturing")
        };
        // Group ends by connector.
        let mut per_connector: HashMap<usize, Vec<(usize, sysmlv2_syntax::span::Span)>> =
            HashMap::new();
        let mut order: Vec<usize> = Vec::new();
        for &(connector, end_elem, span) in
            r.b.connector_ends
                .iter()
                .filter(|row| !model.is_library_unit(r.b.unit_of_elem(row.0)))
        {
            per_connector
                .entry(connector)
                .or_insert_with(|| {
                    order.push(connector);
                    Vec::new()
                })
                .push((end_elem, span));
        }
        for connector in order {
            let unit = r.b.unit_of_elem(connector);
            if model.is_library_unit(unit) {
                continue;
            }
            let ends = &per_connector[&connector];
            // Featured related features: (target, its featuring type, span).
            let mut featured: Vec<(usize, usize, sysmlv2_syntax::span::Span)> = Vec::new();
            let mut lenient = false;
            for &(end_elem, span) in ends {
                let Some(mut target) =
                    rel_target(&r.b, end_elem, "ReferenceSubsetting", "referencedFeature")
                else {
                    continue; // empty or unresolved end
                };
                // A chain end's featuring is the first link's.
                if let Some(&rel) = r.b.elements[target]
                    .owned_relationships
                    .iter()
                    .find(|&&rel| r.b.elements[rel].ty == "FeatureChaining")
                    .filter(|&&rel| r.b.elements[rel].props.get("chainingFeature").is_some())
                {
                    let Some(link) = facts.target(&r.b, rel, "chainingFeature") else {
                        lenient = true;
                        break;
                    };
                    target = link;
                }
                if model.is_library_unit(r.b.unit_of_elem(target)) {
                    continue;
                }
                if has_type_featuring(&r.b, target) {
                    lenient = true;
                    break;
                }
                let f = match r.b.elements[target].owning_relationship {
                    Some(rel) if is_featuring_membership(r.b.elements[rel].ty) => facts.owner[rel],
                    _ => None, // namespace-owned: featured by Anything
                };
                let Some(f) = f else { continue };
                if model.is_library_unit(r.b.unit_of_elem(f)) {
                    continue;
                }
                featured.push((target, f, span));
            }
            if lenient || featured.is_empty() {
                continue;
            }
            // Candidate contexts: lexical ancestors of the connector
            // (through any membership) plus each featuring type and its
            // lexical ancestors.
            let mut candidates: Vec<usize> = Vec::new();
            let push_chain = |b: &crate::json::Builder, start: usize, out: &mut Vec<usize>| {
                let mut cur = start;
                for _ in 0..64 {
                    if !out.contains(&cur) {
                        out.push(cur);
                    }
                    let Some(rel) = b.elements[cur].owning_relationship else {
                        break;
                    };
                    let Some(owner) = facts.owner[rel] else { break };
                    cur = owner;
                }
            };
            push_chain(&r.b, connector, &mut candidates);
            for &(_, f, _) in &featured {
                push_chain(&r.b, f, &mut candidates);
            }
            // T admits a feature featured in F when T conforms to F, or a
            // member of T (or of a type T explicitly specializes) is typed
            // by / references something conforming to F.
            let mut admits_cache: HashMap<(usize, usize), bool> = HashMap::new();
            let mut admits = |r: &mut crate::json::ResolvedModel, t: usize, f: usize| -> bool {
                if let Some(&hit) = admits_cache.get(&(t, f)) {
                    return hit;
                }
                let mut ok = t == f || r.b.conforms_upward(t, f);
                if !ok {
                    // One-hop featuring lift over T's own supertype closure.
                    let mut types: Vec<usize> = vec![t];
                    let mut qi = 0;
                    while qi < types.len() && types.len() <= 64 {
                        let cur = types[qi];
                        qi += 1;
                        for s in r.b.explicit_supertype_elems(cur) {
                            if !types.contains(&s) {
                                types.push(s);
                            }
                        }
                    }
                    'outer: for &ty_el in &types {
                        for ri in 0..r.b.elements[ty_el].owned_relationships.len() {
                            let rel = r.b.elements[ty_el].owned_relationships[ri];
                            for mi in 0..r.b.elements[rel].children.len() {
                                let m = r.b.elements[rel].children[mi];
                                for key in ["type", "referencedFeature"] {
                                    let rel_ty = if key == "type" {
                                        "FeatureTyping"
                                    } else {
                                        "ReferenceSubsetting"
                                    };
                                    if let Some(g) = rel_target(&r.b, m, rel_ty, key) {
                                        if g == f || r.b.conforms_upward(g, f) {
                                            ok = true;
                                            break 'outer;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
                admits_cache.insert((t, f), ok);
                ok
            };
            // Pick the candidate that admits the most related features;
            // the finding names the first feature it cannot reach.
            let mut best: Option<(usize, usize)> = None; // (admitted, cand idx)
            for (i, &t) in candidates.iter().enumerate() {
                let admitted = featured
                    .iter()
                    .filter(|&&(_, f, _)| admits(r, t, f))
                    .count();
                if best.is_none_or(|(b, _)| admitted > b) {
                    best = Some((admitted, i));
                }
            }
            let accessible = best.is_some_and(|(a, _)| a == featured.len());
            if !accessible {
                let best_t = candidates[best.map_or(0, |(_, i)| i)];
                let (target, f, span) = *featured
                    .iter()
                    .find(|&&(_, f, _)| !admits(r, best_t, f))
                    .unwrap_or(&featured[0]);
                let name = |e: usize| {
                    r.b.elements[e]
                        .props
                        .get("declaredName")
                        .and_then(|v| v.as_str())
                        .unwrap_or("<unnamed>")
                        .to_string()
                };
                out.push((
                    unit,
                    Diagnostic::warning(
                        span,
                        format!(
                            "connector end references `{}`, which is featured in \
                             `{}` — no featuring context of the connector reaches \
                             it",
                            name(target),
                            name(f),
                        ),
                    ),
                ));
            }
        }
    }
    out
}
