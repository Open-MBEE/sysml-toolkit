//! Lexical succession endpoints, projected into the shared implied graph.
use super::{Builder, membership_evidence, structural_index::StoredStructure};
use crate::metaclass::is_a;
use std::collections::{HashMap, hash_map::Entry};

fn charge(steps: &mut usize, amount: usize) -> Option<()> {
    *steps = steps.saturating_add(amount);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}

/// Missing shorthand ends are resolved from the ordered owning Memberships.
/// No source rows are changed, and the static publisher owns the new identities.
pub(super) fn endpoints(b: &mut Builder, steps: &mut usize) -> Option<Vec<(usize, usize)>> {
    endpoints_from(b, 0, steps)
}

/// [`endpoints`] of the successions from row `start` on: a build extending a
/// prepared library's plans reads the library's own successions' endpoints
/// from them.
pub(super) fn endpoints_from(
    b: &mut Builder,
    start: usize,
    steps: &mut usize,
) -> Option<Vec<(usize, usize)>> {
    let limit = b.explicit_len();
    // Gather the small succession slice once. Scanning the whole graph again
    // after proving existence wastes the cold query's shared work allowance.
    charge(steps, limit.saturating_sub(start))?;
    let mut successions = Vec::new();
    for i in (start..limit).filter(|&i| b.is_authored(i)) {
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
        // Transition-owned successions use the transition's source, written
        // or, for a target transition, implicit.
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
                if !is_a!(relation, "Membership") {
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
                        if is_a!(b.elements[rel], "FeatureMembership")
                            || !is_a!(b.elements[member], "Feature")
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
                            (!is_a!(b.elements[rel], "FeatureMembership")
                                && is_a!(b.elements[member], "ActionUsage"))
                            .then_some(member)
                        })
                    })
                    .flatten()
                    // A target transition's source is the last action
                    // before it in its owner's body (SysML 8.2.2.21).
                    .or_else(|| {
                        if !explicit_transition || chained_source {
                            return None;
                        }
                        let membership = b.elements[owner].owning_relationship?;
                        let Some(Some(carrier)) = raw.carrier(b, membership) else {
                            return None;
                        };
                        super::implied::implicit_transition_source(b, owner, carrier)
                    });
                let occurrence = |rel: usize, member: usize| {
                    is_a!(b.elements[rel], "FeatureMembership")
                        && is_a!(b.elements[member], "OccurrenceUsage")
                };
                // A `then` leaves the last occurrence before it that can
                // stand as a predecessor: no parameter, no transition, no
                // connector but a flow or message (`decide d; if g then b;
                // then c;` leaves `c` from `d`, not from the guarded
                // transition). It reaches the next occurrence whatever it is.
                let predecessor = |rel: usize, member: usize| {
                    occurrence(rel, member)
                        && super::implied::is_previous_candidate(b, owner, rel, member)
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
                    if predecessor(rel, member) {
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
            if b.elements[end]
                .owned_relationships
                .iter()
                .any(|&r| b.elements.get(r).is_none_or(|r| is_a!(r, "Specialization")))
            {
                continue;
            }
            if is_a!(b.elements[end], "Feature") && end != target {
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
    /// A target transition's succession leaves the transition's implicit
    /// source, the last action before the transition in its owner's body.
    #[test]
    fn target_transition_successions_take_the_implicit_source() {
        let mut model = Model::new();
        assert!(
            model
                .add_source(
                    "targets.sysml",
                    "state def T { state a; state b; if true then b; else a; }"
                )
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let b_state = r.resolve_qualified("T::b").unwrap().0;
        let transitions = r.elements_of_metaclass("TransitionUsage");
        assert_eq!(transitions.len(), 2);
        let edges = endpoints(&mut r.b, &mut 0).unwrap();
        for transition in transitions {
            let succession = r.b.elements[transition.0]
                .owned_relationships
                .iter()
                .filter_map(|&rel| r.b.elements[rel].children.first().copied())
                .find(|&e| r.b.elements[e].ty == "SuccessionAsUsage")
                .expect("the transition succession");
            let source_end = r.b.elements[succession]
                .owned_relationships
                .iter()
                .filter(|&&rel| r.b.elements[rel].ty == "EndFeatureMembership")
                .filter_map(|&rel| r.b.elements[rel].children.first().copied())
                .next()
                .expect("the source end");
            assert!(edges.contains(&(source_end, b_state)), "{edges:?}");
        }
    }

    /// A `then` after a guarded branch of a decision leaves the decision
    /// node: the transition before it stands as no predecessor.
    #[test]
    fn a_then_after_a_guarded_branch_leaves_the_decision_node() {
        let mut model = Model::new();
        assert!(
            model
                .add_source(
                    "related.sysml",
                    "action def Basic { action b; action c; action e; decide d; if true then b; then c; else e; }"
                )
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let basic = r.resolve_qualified("Basic").unwrap().0;
        let d = r.resolve_qualified("Basic::d").unwrap().0;
        let plain = r.b.elements[basic]
            .owned_relationships
            .iter()
            .filter_map(|&rel| r.b.elements[rel].children.first().copied())
            .find(|&e| r.b.elements[e].ty == "SuccessionAsUsage")
            .expect("the plain succession");
        let source_end = r.b.elements[plain]
            .owned_relationships
            .iter()
            .filter(|&&rel| r.b.elements[rel].ty == "EndFeatureMembership")
            .filter_map(|&rel| r.b.elements[rel].children.first().copied())
            .next()
            .expect("the source end");
        let edges = endpoints(&mut r.b, &mut 0).unwrap();
        assert!(edges.contains(&(source_end, d)), "{edges:?}");
    }
    /// Parameters and connectors other than flows and messages stand as no
    /// predecessor of a `then`: after an `in` parameter it leaves the
    /// action before the parameter, after a connection the action before
    /// the connection.
    #[test]
    fn parameters_and_connectors_are_no_predecessors() {
        let mut model = Model::new();
        assert!(
            model
                .add_source(
                    "skipped.sysml",
                    "action def Skipped {
                        action a; in item p; then b;
                        action b; action c;
                        connect b to c; then e; action e;
                    }"
                )
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let skipped = r.resolve_qualified("Skipped").unwrap().0;
        let a = r.resolve_qualified("Skipped::a").unwrap().0;
        let c = r.resolve_qualified("Skipped::c").unwrap().0;
        let plain: Vec<usize> = r.b.elements[skipped]
            .owned_relationships
            .iter()
            .filter_map(|&rel| r.b.elements[rel].children.first().copied())
            .filter(|&e| r.b.elements[e].ty == "SuccessionAsUsage")
            .collect();
        assert_eq!(plain.len(), 2);
        let source_end = |r: &ResolvedModel, succession: usize| {
            r.b.elements[succession]
                .owned_relationships
                .iter()
                .filter(|&&rel| r.b.elements[rel].ty == "EndFeatureMembership")
                .filter_map(|&rel| r.b.elements[rel].children.first().copied())
                .next()
                .expect("the source end")
        };
        let (then_b, then_e) = (source_end(&r, plain[0]), source_end(&r, plain[1]));
        let edges = endpoints(&mut r.b, &mut 0).unwrap();
        assert!(edges.contains(&(then_b, a)), "{edges:?}");
        assert!(edges.contains(&(then_e, c)), "{edges:?}");
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
