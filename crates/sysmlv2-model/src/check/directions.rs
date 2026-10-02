//! Shared conformance policy for validation and proposed redefinition repairs.
use super::facts::{Facts, is};
use crate::json::{Builder, DirectionFact, DirectionProof, authored_direction};
use std::collections::HashMap;

#[derive(Default)]
pub(super) struct RedefinitionDirections {
    proof: DirectionProof,
    ownership: OwnershipProof,
    steps: usize,
}

// Query-local ownership validation. Wide types index their relationship counts
// once instead of rescanning the whole owner for every directed feature.
#[derive(Default)]
struct OwnershipProof {
    owners: HashMap<usize, HashMap<usize, usize>>,
    features: HashMap<usize, Option<Option<usize>>>,
}
impl OwnershipProof {
    fn relationship_counts(
        &mut self,
        b: &Builder,
        owner: usize,
        steps: &mut usize,
    ) -> Option<&HashMap<usize, usize>> {
        if let std::collections::hash_map::Entry::Vacant(entry) = self.owners.entry(owner) {
            let relationships = &b.elements.get(owner)?.owned_relationships;
            *steps = steps.saturating_add(relationships.len());
            if *steps > crate::eval::MAX_STEPS {
                return None;
            }
            let mut counts = HashMap::new();
            for &relationship in relationships {
                *counts.entry(relationship).or_insert(0) += 1;
            }
            entry.insert(counts);
        }
        self.owners.get(&owner)
    }
    // Nested Option distinguishes proven absence from broken ownership.
    fn owning_type(
        &mut self,
        b: &Builder,
        g: &Facts,
        e: usize,
        steps: &mut usize,
    ) -> Option<Option<usize>> {
        *steps = steps.saturating_add(1);
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
        if let Some(&value) = self.features.get(&e) {
            return value;
        }
        let result = self.inspect(b, g, e, steps);
        if *steps <= crate::eval::MAX_STEPS {
            self.features.insert(e, result);
        }
        result
    }
    fn inspect(
        &mut self,
        b: &Builder,
        g: &Facts,
        e: usize,
        steps: &mut usize,
    ) -> Option<Option<usize>> {
        let feature = b.elements.get(e)?;
        if !is(b, e, "Feature") {
            return None;
        }
        let Some(rel) = feature.owning_relationship else {
            return Some(None);
        };
        b.elements.get(rel)?;
        if !is(b, rel, "OwningMembership") {
            return None;
        }
        let membership = b.elements.get(rel)?;
        let owner = g.owner.get(e).copied().flatten()?;
        b.elements.get(owner)?;
        if *membership.children != [e]
            || self.relationship_counts(b, owner, steps)?.get(&rel) != Some(&1)
        {
            return None;
        }
        for key in ["memberElement", "ownedMemberElement", "ownedMemberFeature"] {
            if membership
                .props
                .get(key)
                .is_some_and(|value| value.as_reference() != Some(b.elem_id(e)))
            {
                return None;
            }
        }
        for key in [
            "owningRelatedElement",
            "membershipOwningNamespace",
            "owningType",
        ] {
            if membership
                .props
                .get(key)
                .is_some_and(|value| value.as_reference() != Some(b.elem_id(owner)))
            {
                return None;
            }
        }
        if is(b, rel, "FeatureMembership") {
            is(b, owner, "Type").then_some(Some(owner))
        } else {
            Some(None)
        }
    }
}

impl RedefinitionDirections {
    /// Some(false) is a proven violation; None is incomplete, never absence.
    /// A validator reports false; a repair requires true.
    pub(super) fn conformance(
        &mut self,
        b: &mut Builder,
        g: &Facts,
        element: usize,
        target: usize,
    ) -> Option<bool> {
        // A large earlier declaration must not suppress independent later checks.
        // Completed graph proofs stay memoized, but every query and memo hit pays.
        self.steps = 1;
        if self.steps > crate::eval::MAX_STEPS {
            return None;
        }
        let own = authored_direction(b, element);
        if own == DirectionFact::Unknown {
            return None;
        }
        let raw = authored_direction(b, target);
        if raw == DirectionFact::Unknown {
            return None;
        }
        if raw == DirectionFact::Known(None) {
            return Some(true);
        }
        let target_owner = self.ownership.owning_type(b, g, target, &mut self.steps)?;
        let owner = self.ownership.owning_type(b, g, element, &mut self.steps);
        // Usage::mayTimeVary is derived from library specialization, portions
        // and action/link exclusions. The static occurrence heuristic is not
        // an identity proof. Unknown variability must satisfy both the owner-
        // only and all-featuring interpretations before a repair is offered.
        let variable = if is(b, element, "Usage") {
            if owner == Some(None)
                || b.elements[element]
                    .props
                    .get("isPortion")
                    .and_then(|v| v.as_bool())
                    == Some(true)
            {
                Some(false)
            } else {
                None
            }
        } else {
            match b.elements[element].props.get("isVariable") {
                None => Some(false),
                Some(value) => Some(value.as_bool()?),
            }
        };
        let mut complete = owner.is_some();
        let mut contexts: Vec<usize> = owner.flatten().into_iter().collect();
        let mut seen_contexts: std::collections::HashSet<_> = contexts.iter().copied().collect();
        if variable == Some(true) {
            // Invalid/missing variable ownership is not a vacuous proof.
            complete &= !contexts.is_empty();
        } else {
            let relations = g.outgoing_relationships(element);
            self.steps = self.steps.saturating_add(relations.len());
            if self.steps > crate::eval::MAX_STEPS {
                return None;
            }
            for &rel in relations {
                if is(b, rel, "FeatureChaining") {
                    // Its first feature contributes further featuring contexts.
                    complete = false;
                } else if is(b, rel, "TypeFeaturing") {
                    let relation = &b.elements[rel];
                    if relation
                        .props
                        .get("featureOfType")
                        .is_some_and(|source| source.as_reference() != Some(b.elem_id(element)))
                    {
                        complete = false;
                        continue;
                    }
                    match g.target(b, rel, "featuringType") {
                        Some(t) if is(b, t, "Type") => {
                            if seen_contexts.insert(t) {
                                contexts.push(t);
                            }
                        }
                        _ => complete = false,
                    }
                }
            }
        }
        for context in contexts {
            match self
                .proof
                .through(
                    b,
                    context,
                    target,
                    target_owner,
                    &|b, node, steps| {
                        let relationships = g.outgoing_relationships(node);
                        *steps = steps.saturating_add(relationships.len());
                        if *steps > crate::eval::MAX_STEPS {
                            return None;
                        }
                        Some(relationships.iter().any(|&r| is(b, r, "FeatureChaining")))
                    },
                    &mut self.steps,
                )
                .compatible(own)
            {
                Some(false) if variable.is_none() && owner != Some(Some(context)) => {
                    // The all-featuring branch fails, but an actually variable
                    // Usage may ignore this additional context.
                    complete = false;
                }
                Some(false) => return Some(false),
                None => complete = false,
                Some(true) => {}
            }
        }
        complete.then_some(true)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    use serde_json::json;
    fn fixture() -> ResolvedModel {
        let mut m = Model::new();
        let u=m.add_source("direction.kerml","package P {classifier A {in feature p;} classifier C specializes A {in feature p;} classifier Wrong specializes A {out feature p;} feature link chains A::p;}");
        assert!(u.diagnostics.is_empty(), "{:?}", u.diagnostics);
        ResolvedModel::build(&m)
    }

    #[test]
    fn package_ownership_absence_requires_reciprocal_membership() {
        let mut m = Model::new();
        m.add_source(
            "ownership.kerml",
            "package P {in feature p; feature unrelated; classifier A {out feature q;}}",
        );
        let mut r = ResolvedModel::build(&m);
        let target = r.resolve_qualified("P::p").unwrap().0;
        let unrelated = r.resolve_qualified("P::unrelated").unwrap().0;
        let g = Facts::new(&mut r.b);
        assert_eq!(
            OwnershipProof::default().owning_type(&r.b, &g, target, &mut 0),
            Some(None)
        );
        r.b.elements[target].owning_relationship = r.b.elements[unrelated].owning_relationship;
        let g = Facts::new(&mut r.b);
        assert_eq!(
            OwnershipProof::default().owning_type(&r.b, &g, target, &mut 0),
            None
        );
    }
    #[test]
    fn malformed_owning_membership_is_not_a_direction_proof() {
        for defect in 0..5 {
            let mut r = fixture();
            let target = r.resolve_qualified("P::A::p").unwrap().0;
            let own = r.resolve_qualified("P::Wrong::p").unwrap().0;
            let owner = r.resolve_qualified("P::A").unwrap().0;
            let unrelated = r.resolve_qualified("P::C").unwrap().0;
            let rel = r.b.elements[target].owning_relationship.unwrap();
            let wrong_id = r.b.elem_id(unrelated);
            match defect {
                0 => r.b.elements[rel]
                    .props
                    .insert("memberElement", json!({"@id":wrong_id})),
                1 => r.b.elements[rel].children.make_mut().clear(),
                2 => r.b.elements[owner]
                    .owned_relationships
                    .make_mut()
                    .retain(|&e| e != rel),
                3 => r.b.elements[rel]
                    .props
                    .insert("owningRelatedElement", json!({"@id":wrong_id})),
                4 => r.b.elements[owner].owned_relationships.push(rel),
                _ => unreachable!(),
            }
            let g = Facts::new(&mut r.b);
            let mut proof = RedefinitionDirections::default();
            assert_eq!(
                proof.conformance(&mut r.b, &g, own, target),
                None,
                "defect {defect}"
            );
        }
    }
    #[test]
    fn standalone_chaining_prevents_unsafe_context_completion() {
        let mut r = fixture();
        let target = r.resolve_qualified("P::A::p").unwrap().0;
        let own = r.resolve_qualified("P::C::p").unwrap().0;
        let link = r.resolve_qualified("P::link").unwrap();
        let rel = r
            .owned_relationships(link)
            .into_iter()
            .find(|&e| r.element_type(e) == "FeatureChaining")
            .unwrap()
            .0;
        let own_id = r.b.elem_id(own);
        // The relation is owned elsewhere, but explicitly names this feature.
        // Facts must index its source; owning-only scans lose this uncertainty.
        r.b.elements[rel]
            .props
            .insert("featureChained", json!({"@id":own_id}));
        let g = Facts::new(&mut r.b);
        let mut proof = RedefinitionDirections::default();
        assert!(g.outgoing_relationships(own).contains(&rel));
        assert_eq!(proof.conformance(&mut r.b, &g, own, target), None);
    }
    #[test]
    fn explicit_null_target_direction_and_query_budget_recovery() {
        let mut r = fixture();
        let target = r.resolve_qualified("P::A::p").unwrap().0;
        let own = r.resolve_qualified("P::C::p").unwrap().0;
        let g = Facts::new(&mut r.b);
        let mut proof = RedefinitionDirections {
            steps: crate::eval::MAX_STEPS,
            ..Default::default()
        };
        assert_eq!(proof.conformance(&mut r.b, &g, own, target), Some(true));
        r.b.elements[target].props.insert("direction", json!(null));
        let mut fresh = RedefinitionDirections::default();
        assert_eq!(fresh.conformance(&mut r.b, &g, own, target), Some(true));
    }
    #[test]
    fn conflicting_general_endpoint_and_wrong_source_are_unknown() {
        for key in ["general", "specific"] {
            let mut r = fixture();
            let target = r.resolve_qualified("P::A::p").unwrap().0;
            let own = r.resolve_qualified("P::C::p").unwrap().0;
            let current = r.resolve_qualified("P::C").unwrap();
            let other = r.resolve_qualified("P::Wrong").unwrap();
            let edge = r
                .owned_relationships(current)
                .into_iter()
                .find(|&e| r.element_type(e) == "Subclassification")
                .unwrap()
                .0;
            let id = r.element_id(other);
            r.b.elements[edge].props.insert(key, json!({"@id":id}));
            let g = Facts::new(&mut r.b);
            let mut proof = RedefinitionDirections::default();
            assert_eq!(proof.conformance(&mut r.b, &g, own, target), None, "{key}");
        }
    }
    fn variable_fixture() -> ResolvedModel {
        let mut m = Model::new();
        let u = m.add_source(
            "variable-directions.kerml",
            r#"
        class A {in feature p;}
        class Flip conjugates A;
        package Actions {behavior Action;}
        class C specializes A {
            in feature p : Actions::Action featured by Flip;
        }
        class Bad specializes A {
            out feature p : Actions::Action featured by missing;
        }
    "#,
        );
        assert!(u.diagnostics.is_empty(), "{:?}", u.diagnostics);
        ResolvedModel::build(&m)
    }

    #[test]
    fn derived_usage_variability_does_not_drop_additional_contexts() {
        let mut r = variable_fixture();
        let target = r.resolve_qualified("A::p").unwrap().0;
        let good_owner = r.resolve_qualified("C::p").unwrap().0;
        let bad_owner = r.resolve_qualified("Bad::p").unwrap().0;
        for e in [good_owner, bad_owner] {
            // Graph-level SysML Usage: textual SysML does not admit the KerML
            // `featured by` spelling, but TypeFeaturing is a metamodel relation.
            r.b.elements[e].ty = "ActionUsage";
            r.b.elements[e].props.insert("isComposite", json!(true));
        }
        let g = Facts::new(&mut r.b);
        // This witnesses the old approximation. Composite Action usages have
        // normative variability exclusions requiring a library identity proof;
        // treating every owning Class as sufficient evidence is unsound.
        assert!(super::super::structural::variable(&r.b, &g, good_owner));
        assert_eq!(
            RedefinitionDirections::default().conformance(&mut r.b, &g, good_owner, target),
            None
        );
        // An owning-context mismatch violates both variability interpretations;
        // unknown additional contexts must not erase this known violation.
        assert_eq!(
            RedefinitionDirections::default().conformance(&mut r.b, &g, bad_owner, target),
            Some(false)
        );
        // A proven portion cannot vary and therefore must check the extra context.
        r.b.elements[good_owner]
            .props
            .insert("isPortion", json!(true));
        assert_eq!(
            RedefinitionDirections::default().conformance(&mut r.b, &g, good_owner, target),
            Some(false)
        );
    }

    #[test]
    fn kerml_stored_variability_selects_the_exact_context_branch() {
        for (value, expected) in [
            (json!(true), Some(true)),
            (json!(false), Some(false)),
            (json!("bad"), None),
            (json!(null), None),
        ] {
            let mut r = variable_fixture();
            let target = r.resolve_qualified("A::p").unwrap().0;
            let own = r.resolve_qualified("C::p").unwrap().0;
            r.b.elements[own].props.insert("isVariable", value);
            let g = Facts::new(&mut r.b);
            assert_eq!(
                RedefinitionDirections::default().conformance(&mut r.b, &g, own, target),
                expected
            );
        }
    }
}
