//! Lexical succession endpoints, projected into the shared implied graph.
use super::{Builder, membership_evidence, structural_index::StoredStructure};
use crate::metaclass::conforms;
use std::collections::{HashMap, hash_map::Entry};

fn charge(steps: &mut usize, amount: usize) -> Option<()> {
    *steps = steps.saturating_add(amount);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}

/// Missing shorthand ends are resolved from the ordered owning Memberships.
/// No source rows are changed, and the static publisher owns the new identities.
pub(super) fn endpoints(b: &mut Builder, steps: &mut usize) -> Option<Vec<(usize, usize)>> {
    let limit = b.explicit_len();
    // Gather the small succession slice once. Scanning the whole graph again
    // after proving existence wastes the cold query's shared work allowance.
    charge(steps, limit)?;
    let mut successions = Vec::new();
    for i in 0..limit {
        if b.elements[i].ty == "SuccessionAsUsage" {
            charge(steps, 1)?;
            successions.push(i);
        }
    }
    if successions.is_empty() {
        return Some(Vec::new());
    }
    let raw = StoredStructure::for_query(b, steps)?;
    let domains = raw.membership_domains(b, steps)?;
    let inverse = raw.typing(b, steps)?;
    if inverse.sources_incomplete {
        return Some(Vec::new());
    }
    type Neighbors = HashMap<(usize, usize), (Option<usize>, Option<usize>)>;
    let mut bodies: HashMap<usize, Neighbors> = HashMap::new();
    let mut out = Vec::new();
    for succession in successions {
        charge(steps, 1)?;
        let Some(membership) = b.elements[succession].owning_relationship else {
            continue;
        };
        let Some(Some(owner)) = raw.carrier(b, membership) else {
            continue;
        };
        if !domains.owner_complete(owner)
            || membership_evidence::member(b, &raw, owner, membership, steps) != Some(succession)
        {
            continue;
        }
        // Transition-owned successions use the transition's explicit source.
        // Implicit transition-source Membership establishment is a distinct rule.
        let explicit_transition = b.elements[owner].ty == "TransitionUsage";
        if let Entry::Vacant(entry) = bodies.entry(owner) {
            let mut members = Vec::new();
            let mut complete = true;
            charge(steps, b.elements[owner].owned_relationships.len())?;
            for &rel in &b.elements[owner].owned_relationships {
                let Some(relation) = b.elements.get(rel) else {
                    complete = false;
                    break;
                };
                if !conforms(relation.ty, "Membership") {
                    continue;
                }
                if let Some(member) = membership_evidence::member(b, &raw, owner, rel, steps) {
                    members.push((rel, member));
                } else {
                    complete = false;
                    break;
                }
            }
            charge(steps, 0)?;
            let mut neighbors = HashMap::new();
            if complete {
                // Compute lexical neighbors once per owning body. Repeated
                // shorthand successions must not rescan the whole body.
                charge(steps, members.len().saturating_mul(3))?;
                // A chained transition source needs featureTarget evidence.
                // Do not skip an uncertain earlier candidate to pick a later one.
                let mut chained_source = false;
                if explicit_transition {
                    for &(rel, member) in &members {
                        charge(steps, 1)?;
                        if conforms(b.elements[rel].ty, "FeatureMembership")
                            || !conforms(b.elements[member].ty, "Feature")
                        {
                            continue;
                        }
                        if super::type_relations::checked_feature_target(
                            b,
                            &raw,
                            member,
                            &b.elements[member].owned_relationships,
                            limit,
                            steps,
                        ) != Some(None)
                        {
                            chained_source = true;
                            break;
                        }
                    }
                }
                let transition_source = (explicit_transition && !chained_source)
                    .then(|| {
                        members.iter().find_map(|&(rel, member)| {
                            (!conforms(b.elements[rel].ty, "FeatureMembership")
                                && conforms(b.elements[member].ty, "ActionUsage"))
                            .then_some(member)
                        })
                    })
                    .flatten();
                let occurrence = |rel: usize, member: usize| {
                    conforms(b.elements[rel].ty, "FeatureMembership")
                        && conforms(b.elements[member].ty, "OccurrenceUsage")
                };
                let mut previous = None;
                for &(rel, member) in &members {
                    neighbors.insert(
                        (rel, member),
                        (
                            if explicit_transition {
                                transition_source
                            } else {
                                previous
                            },
                            None,
                        ),
                    );
                    if occurrence(rel, member) {
                        previous = Some(member);
                    }
                }
                let mut next = None;
                for &(rel, member) in members.iter().rev() {
                    neighbors.get_mut(&(rel, member)).expect("checked member").1 = next;
                    if occurrence(rel, member) {
                        next = Some(member);
                    }
                }
            }
            entry.insert(neighbors);
        }
        let Some(&(source, next)) = bodies[&owner].get(&(membership, succession)) else {
            continue;
        };
        let target = b.elements[succession]
            .path
            .ends_with("emptySuccession")
            .then_some(next)
            .flatten();
        let mut ends = Vec::new();
        let mut complete = domains.owner_complete(succession);
        charge(steps, b.elements[succession].owned_relationships.len())?;
        for &rel in &b.elements[succession].owned_relationships {
            let Some(relation) = b.elements.get(rel) else {
                complete = false;
                break;
            };
            if relation.ty != "EndFeatureMembership" {
                continue;
            }
            if let Some(end) = membership_evidence::member(b, &raw, succession, rel, steps) {
                ends.push(end);
            } else {
                complete = false;
                break;
            }
        }
        charge(steps, 0)?;
        if !complete || ends.len() != 2 {
            continue;
        }
        for (end, target) in ends.into_iter().zip([source, target]) {
            let Some(target) = target else { continue };
            charge(steps, b.elements[end].owned_relationships.len())?;
            let incoming = inverse
                .relationships
                .get(&end)
                .map(Vec::as_slice)
                .unwrap_or_default();
            charge(steps, incoming.len())?;
            if incoming.iter().any(|&r| r < limit) {
                continue;
            }
            // An unknown row or authored specialization prevents inventing
            // a replacement endpoint, including an existing reference subset.
            if b.elements[end].owned_relationships.iter().any(|&r| {
                b.elements
                    .get(r)
                    .is_none_or(|r| conforms(r.ty, "Specialization"))
            }) {
                continue;
            }
            if conforms(b.elements[end].ty, "Feature") && end != target {
                out.push((end, target));
            }
        }
    }
    Some(out)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    fn build(count: usize) -> ResolvedModel {
        let mut source = String::from("action owner {");
        for n in 0..count {
            source.push_str(&format!("action a{n}; then a{n};"));
        }
        source.push('}');
        let mut model = Model::new();
        assert!(
            model
                .add_source("successions.sysml", &source)
                .diagnostics
                .is_empty()
        );
        ResolvedModel::build(&model)
    }
    #[test]
    fn lexical_projection_scales_linearly_and_budget_failure_is_retryable() {
        let mut r = build(2000);
        let mut steps = 0;
        let edges = endpoints(&mut r.b, &mut steps).unwrap();
        assert_eq!(edges.len(), 2000);
        assert!(steps < 2_000_000, "{steps}");
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(endpoints(&mut r.b, &mut exhausted).is_none());
        assert_eq!(endpoints(&mut r.b, &mut 0).unwrap(), edges);
    }
    #[test]
    fn standalone_specialization_of_empty_source_prevents_inference() {
        let mut r = build(1);
        let edges = endpoints(&mut r.b, &mut 0).unwrap();
        let (end, target) = edges[0];
        let owner = r.b.new_element("Namespace", None, "extra".into());
        let relation = r.b.new_relationship("ReferenceSubsetting", owner, "source");
        r.b.set(
            relation,
            "subsettingFeature",
            serde_json::json!({"@id": r.b.elements[end].id.to_string()}),
        );
        r.b.set(
            relation,
            "referencedFeature",
            serde_json::json!({"@id": r.b.elements[target].id.to_string()}),
        );
        assert!(endpoints(&mut r.b, &mut 0).unwrap().is_empty());
    }
}
