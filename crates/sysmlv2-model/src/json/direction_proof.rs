//! Bounded direction facts for stored feature identities.
use super::{Builder, provider_completeness::ProviderCompleteness};
use crate::metaclass::conforms;
use std::collections::{HashMap, HashSet};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Direction {
    In,
    Out,
    InOut,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum DirectionFact {
    Known(Option<Direction>),
    Unknown,
}
impl DirectionFact {
    pub(crate) fn compatible(self, own: Self) -> Option<bool> {
        let Self::Known(own) = own else { return None };
        match self {
            Self::Known(None) => Some(true),
            Self::Known(Some(Direction::InOut)) => Some(own.is_some()),
            Self::Known(Some(required)) => Some(own == Some(required)),
            Self::Unknown => None,
        }
    }
}
fn charge(steps: &mut usize, count: usize) -> Option<()> {
    *steps = steps.saturating_add(count);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}
pub(crate) fn authored_direction(b: &Builder, feature: usize) -> DirectionFact {
    let Some(e) = b.elements.get(feature) else {
        return DirectionFact::Unknown;
    };
    if !conforms(e.ty, "Feature") {
        return DirectionFact::Unknown;
    }
    match e.props.get("direction") {
        None => DirectionFact::Known(None),
        Some(v) if v.is_null() => DirectionFact::Known(None),
        Some(v) => match v.as_str() {
            Some("in") => DirectionFact::Known(Some(Direction::In)),
            Some("out") => DirectionFact::Known(Some(Direction::Out)),
            Some("inout") => DirectionFact::Known(Some(Direction::InOut)),
            _ => DirectionFact::Unknown,
        },
    }
}
/// Query-local only. Graph/identity mutation requires a fresh proof.
#[derive(Default)]
pub(crate) struct DirectionProof {
    providers: ProviderCompleteness,
    known: HashMap<(usize, usize, usize), Option<Direction>>,
}
impl DirectionProof {
    pub(crate) fn through(
        &mut self,
        b: &mut Builder,
        current: usize,
        target: usize,
        target_owner: Option<usize>,
        is_chained: &dyn Fn(&Builder, usize, &mut usize) -> Option<bool>,
        steps: &mut usize,
    ) -> DirectionFact {
        // A genuinely undirected feature cannot acquire direction by inheritance.
        if charge(steps, 1).is_none() {
            return DirectionFact::Unknown;
        }
        let raw = authored_direction(b, target);
        match raw {
            DirectionFact::Unknown | DirectionFact::Known(None) => raw,
            DirectionFact::Known(Some(direction)) => {
                let Some(owner) = target_owner else {
                    // directionOf only returns a direction upon reaching owningType.
                    // Caller must establish absence of owningType, not lose an endpoint.
                    return DirectionFact::Known(None);
                };
                match self.walk(
                    b,
                    current,
                    target,
                    owner,
                    direction,
                    0,
                    &mut HashSet::new(),
                    is_chained,
                    steps,
                ) {
                    Some(value) => DirectionFact::Known(value),
                    None => DirectionFact::Unknown,
                }
            }
        }
    }
    // The generic base helper chooses the first stored general endpoint. For a
    // proof, redundant superclass/subsetting slots must agree, not hide corruption.
    fn validate_endpoints(&self, b: &mut Builder, current: usize, steps: &mut usize) -> Option<()> {
        let relationships = b.elements[current].owned_relationships.clone();
        charge(steps, relationships.len())?;
        for rel in relationships {
            let relation = b.elements.get(rel)?;
            if !conforms(relation.ty, "Specialization") {
                continue;
            }
            let expected = if conforms(relation.ty, "Subsetting") {
                "Feature"
            } else if conforms(relation.ty, "Subclassification") {
                "Classifier"
            } else {
                "Type"
            };
            let source_kind =
                if conforms(relation.ty, "Subsetting") || conforms(relation.ty, "FeatureTyping") {
                    "Feature"
                } else if conforms(relation.ty, "Subclassification") {
                    "Classifier"
                } else {
                    "Type"
                };
            if !conforms(b.elements[current].ty, source_kind) {
                return None;
            }
            if relation
                .props
                .get("owningRelatedElement")
                .is_some_and(|value| value.as_reference() != Some(b.elements[current].id))
            {
                return None;
            }
            let mut endpoint = None;
            for key in [
                "general",
                "superclassifier",
                "type",
                "subsettedFeature",
                "redefinedFeature",
                "referencedFeature",
                "crossedFeature",
            ] {
                if let Some(value) = relation.props.get(key) {
                    let id = value.as_reference()?;
                    if endpoint.is_some_and(|previous| previous != id) {
                        return None;
                    }
                    endpoint = Some(id);
                }
            }
            let target = b.element_index_of_uuid(endpoint?)?;
            if !conforms(b.elements.get(target)?.ty, expected) {
                return None;
            }
        }
        Some(())
    }

    #[allow(clippy::too_many_arguments)]
    fn walk(
        &mut self,
        b: &mut Builder,
        current: usize,
        target: usize,
        target_owner: usize,
        direction: Direction,
        depth: usize,
        active: &mut HashSet<usize>,
        is_chained: &dyn Fn(&Builder, usize, &mut usize) -> Option<bool>,
        steps: &mut usize,
    ) -> Option<Option<Direction>> {
        charge(steps, 1)?;
        if depth > super::MAX_RESOLUTION_DEPTH || !conforms(b.elements.get(current)?.ty, "Type") {
            return None;
        }
        // Normative terminal comes before conjugation or supertypes.
        if current == target_owner {
            return Some(Some(direction));
        }
        if active.contains(&current) {
            return None;
        }
        let key = (current, target, depth);
        if let Some(&known) = self.known.get(&key) {
            return Some(known);
        }
        active.insert(current);
        let result = (|| {
            let relations = &b.elements[current].owned_relationships;
            charge(steps, relations.len())?;
            // Feature::supertypes adds its chain target; do not silently omit it.
            if is_chained(b, current, steps)?
                || relations
                    .iter()
                    .any(|&r| conforms(b.elements[r].ty, "FeatureChaining"))
            {
                return None;
            }
            let conjugated = relations
                .iter()
                .any(|&r| conforms(b.elements[r].ty, "Conjugation"));
            // The provider validates uniqueness/endpoints and gives conjugation
            // precedence. Invalid mixed declarations remain unsupported here.
            if conjugated
                && relations
                    .iter()
                    .any(|&r| conforms(b.elements[r].ty, "Specialization"))
            {
                return None;
            }
            self.validate_endpoints(b, current, steps)?;
            let scope = *b.elem_scope.get(&current)?;
            if !self.providers.scope(b, scope, steps) {
                return None;
            }
            let mut result = None;
            // Uniform non-null paths are independent of the provider's ordering.
            // Mixed paths are unknown rather than guessing the normative first.
            for parent in b.value_context_bases(current, steps)? {
                if let Some(found) = self.walk(
                    b,
                    parent,
                    target,
                    target_owner,
                    direction,
                    depth + 1,
                    active,
                    is_chained,
                    steps,
                )? {
                    if result.is_some_and(|previous| previous != found) {
                        return None;
                    }
                    result = Some(found);
                }
            }
            Some(match (result, conjugated) {
                (Some(Direction::In), true) => Some(Direction::Out),
                (Some(Direction::Out), true) => Some(Direction::In),
                _ => result,
            })
        })();
        active.remove(&current);
        if let Some(value) = result {
            self.known.insert(key, value);
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    #[test]
    fn compatibility_includes_missing_direction() {
        let dirs = [
            None,
            Some(Direction::In),
            Some(Direction::Out),
            Some(Direction::InOut),
        ];
        for target in dirs {
            for own in dirs {
                let expected = match target {
                    None => true,
                    Some(Direction::InOut) => own.is_some(),
                    Some(d) => own == Some(d),
                };
                assert_eq!(
                    DirectionFact::Known(target).compatible(DirectionFact::Known(own)),
                    Some(expected)
                );
            }
        }
        assert_eq!(
            DirectionFact::Unknown.compatible(DirectionFact::Known(None)),
            None
        );
    }
    #[test]
    fn exhausted_provider_walk_does_not_poison_a_later_direction_query() {
        let mut m = Model::new();
        m.add_source(
            "retry.kerml",
            "classifier A {in feature p;} classifier B specializes A;",
        );
        let mut r = ResolvedModel::build(&m);
        let owner = r.resolve_qualified("A").unwrap().0;
        let target = r.resolve_qualified("A::p").unwrap().0;
        let current = r.resolve_qualified("B").unwrap().0;
        let mut proof = DirectionProof::default();
        // through + walk + relationship/endpoint scans leave one provider step;
        // its dependency enumeration exhausts the remaining budget.
        let count = r.b.elements[current].owned_relationships.len();
        let mut steps = crate::eval::MAX_STEPS - (3 + 2 * count);
        assert_eq!(
            proof.through(
                &mut r.b,
                current,
                target,
                Some(owner),
                &|_, _, _| Some(false),
                &mut steps
            ),
            DirectionFact::Unknown
        );
        assert!(steps > crate::eval::MAX_STEPS);
        steps = 0;
        assert_eq!(
            proof.through(
                &mut r.b,
                current,
                target,
                Some(owner),
                &|_, _, _| Some(false),
                &mut steps
            ),
            DirectionFact::Known(Some(Direction::In))
        );
    }

    #[test]
    fn conjugation_terminal_and_unknown_paths() {
        let mut m = Model::new();
        let u=m.add_source("directions.kerml", "classifier A {in feature p;} classifier B conjugates A; classifier C conjugates B; classifier D specializes A; classifier Broken specializes A, missing; classifier Cycle specializes A, Cycle;");
        assert!(u.diagnostics.is_empty(), "{:?}", u.diagnostics);
        let mut r = ResolvedModel::build(&m);
        let p = r.resolve_qualified("A::p").unwrap().0;
        let owner = r.resolve_qualified("A").unwrap().0;
        let mut proof = DirectionProof::default();
        let mut steps = 0;
        for (name, expected) in [
            ("A", DirectionFact::Known(Some(Direction::In))),
            ("B", DirectionFact::Known(Some(Direction::Out))),
            ("C", DirectionFact::Known(Some(Direction::In))),
            ("D", DirectionFact::Known(Some(Direction::In))),
            ("Broken", DirectionFact::Unknown),
            ("Cycle", DirectionFact::Unknown),
        ] {
            let e = r.resolve_qualified(name).unwrap().0;
            assert_eq!(
                proof.through(
                    &mut r.b,
                    e,
                    p,
                    Some(owner),
                    &|_, _, _| Some(false),
                    &mut steps
                ),
                expected,
                "{name}"
            );
        }
        let mut exhausted = crate::eval::MAX_STEPS;
        assert_eq!(
            proof.through(
                &mut r.b,
                owner,
                p,
                Some(owner),
                &|_, _, _| Some(false),
                &mut exhausted
            ),
            DirectionFact::Unknown
        );
    }
}
