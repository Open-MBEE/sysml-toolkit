//! Bounded identity evidence for reciprocal owned and unowned Membership selectors.
//! This is shared by required-edge planners; it does not resolve names, invent
//! owned members, materialize a semantic graph, or certify a complete family.
use super::{Builder, structural_index::StoredStructure};
use crate::metaclass::conforms;
use std::collections::HashSet;

fn charge(steps: &mut usize, amount: usize) -> Option<()> {
    *steps = steps.saturating_add(amount);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}

/// A reciprocal owned or unowned Membership endpoint from the shared semantic
/// carrier view. This selector proves one membership identity, not completeness
/// of the owner's members or applicability of any generated family.
pub(super) fn member(
    b: &Builder,
    raw: &StoredStructure,
    owner: usize,
    membership: usize,
    steps: &mut usize,
) -> Option<usize> {
    charge(steps, 1)?;
    if !raw.ids_unique || !raw.is_current(b) {
        return None;
    }
    let owner_id = b.elements.get(owner)?.id;
    let relation = b.elements.get(membership)?;
    if !conforms(relation.ty, "Membership")
        || super::semantic_ownership::checked_relationship_carrier(b, raw, membership, steps)?
            != Some(owner)
    {
        return None;
    }
    for key in [
        "owningRelatedElement",
        "membershipOwningNamespace",
        "owningType",
        "featureWithValue",
    ] {
        if relation
            .props
            .get(key)
            .is_some_and(|v| v.as_reference() != Some(owner_id))
        {
            return None;
        }
    }
    let owned = conforms(relation.ty, "OwningMembership");
    let member = if owned {
        if relation.children.len() != 1 {
            return None;
        }
        let member = relation.children[0];
        if b.elements.get(member)?.owning_relationship != Some(membership) {
            return None;
        }
        member
    } else {
        raw.element_for_uuid(b, relation.props.get("memberElement")?.as_reference()?)?
    };
    let element = b.elements.get(member)?;
    for key in [
        "memberElement",
        "ownedMemberElement",
        "ownedMemberFeature",
        "memberFeature",
        "ownedResultExpression",
        "value",
    ] {
        if relation
            .props
            .get(key)
            .is_some_and(|v| v.as_reference() != Some(element.id))
        {
            return None;
        }
    }
    // Check the actual metaclass narrowings; unrelated optional properties are
    // not assumed to be aliases of a membership that does not declare them.
    if conforms(relation.ty, "ParameterMembership")
        && relation
            .props
            .get("ownedMemberParameter")
            .is_some_and(|v| v.as_reference() != Some(element.id))
    {
        return None;
    }
    let member_ids = [element.id];
    for (key, expected) in [
        ("source", &[owner_id][..]),
        ("target", &[element.id][..]),
        ("relatedElement", &[owner_id, element.id][..]),
        (
            "ownedRelatedElement",
            if owned { &member_ids[..] } else { &[][..] },
        ),
    ] {
        if let Some(value) = relation.props.get(key) {
            let values = value.as_array()?;
            charge(steps, values.len())?;
            if values.len() != expected.len()
                || values
                    .iter()
                    .zip(expected)
                    .any(|(v, id)| v.as_reference() != Some(*id))
            {
                return None;
            }
        }
    }
    if owned {
        for (key, applicable) in [
            ("owningRelationship", true),
            ("owningMembership", true),
            (
                "owningFeatureMembership",
                conforms(relation.ty, "FeatureMembership"),
            ),
            (
                "owningParameterMembership",
                conforms(relation.ty, "ParameterMembership"),
            ),
        ] {
            if applicable
                && element
                    .props
                    .get(key)
                    .is_some_and(|v| v.as_reference() != Some(relation.id))
            {
                return None;
            }
        }
    } else if !relation.children.is_empty() {
        return None;
    }
    Some(member)
}

/// Complete local FeatureValue selection, including inverse ownership claims.
/// The outer None means malformed/incomplete evidence; Some(None) proves absence.
/// Value flags are structurally checked but their semantic applicability belongs
/// to the caller. This does not inherit values or select defaults.
pub(super) fn valuation(
    b: &Builder,
    raw: &StoredStructure,
    feature: usize,
    steps: &mut usize,
) -> Option<Option<(usize, usize)>> {
    charge(steps, 1)?;
    if !raw.ids_unique
        || !raw.is_current(b)
        || !conforms(b.elements.get(feature)?.ty, "Feature")
        || !raw.membership_domains(b, steps)?.owner_complete(feature)
    {
        return None;
    }
    let relationships = super::semantic_ownership::owned_relationships(b, feature)?;
    charge(steps, relationships.len())?;
    let mut seen = HashSet::new();
    let mut value = None;
    for relationship in relationships.iter() {
        if !seen.insert(relationship)
            || super::semantic_ownership::checked_relationship_carrier(b, raw, relationship, steps)?
                != Some(feature)
        {
            return None;
        }
        let relation = b.elements.get(relationship)?;
        if !conforms(relation.ty, "FeatureValue") {
            continue;
        }
        if value.is_some() {
            return None;
        }
        for key in ["isInitial", "isDefault"] {
            if relation
                .props
                .get(key)
                .is_some_and(|v| v.as_bool().is_none())
            {
                return None;
            }
        }
        let expression = member(b, raw, feature, relationship, steps)?;
        if !conforms(b.elements.get(expression)?.ty, "Expression") {
            return None;
        }
        value = Some((relationship, expression));
    }
    Some(value)
}

/// Exact non-conjugated parameter direction. A membership default needs its
/// reciprocal member witness; malformed present values never become defaults.
/// Ordinary FeatureMemberships permit explicit null (no direction); parameter
/// memberships cannot use null to bypass their required direction.
/// The caller establishes the owning-type context and excludes conjugation.
pub(super) fn parameter_direction<'a>(
    b: &'a Builder,
    raw: &StoredStructure,
    feature: usize,
    steps: &mut usize,
) -> Option<Option<&'a str>> {
    charge(steps, 1)?;
    let element = b.elements.get(feature)?;
    if !conforms(element.ty, "Feature") {
        return None;
    }
    let membership = element.owning_relationship?;
    let relation = b.elements.get(membership)?;
    if !conforms(relation.ty, "FeatureMembership") {
        return None;
    }
    let owner =
        super::semantic_ownership::checked_relationship_carrier(b, raw, membership, steps)??;
    if member(b, raw, owner, membership, steps)? != feature {
        return None;
    }
    if let Some(value) = element.props.get("direction") {
        if value.is_null() && !conforms(relation.ty, "ParameterMembership") {
            return Some(None);
        }
        return match value.as_str() {
            Some(direction @ ("in" | "out" | "inout")) => Some(Some(direction)),
            _ => None,
        };
    }
    if element.ty == "TriggerInvocationExpression" {
        return Some(None);
    }
    Some(super::behavior::parameter_direction_default(relation.ty))
}

/// The first authored Membership outside `excluded_kind` must itself admit the
/// requested endpoint. A malformed or wrong-kind first member is never skipped.
/// `reject_owned_kind` lets additive owned-result planning preserve an existing
/// result rather than generating another one. Invocation typing passes None.
pub(super) fn first_unowned_member(
    b: &mut Builder,
    raw: &StoredStructure,
    owner: usize,
    excluded_kind: &str,
    required_target_kind: &str,
    reject_owned_kind: Option<&str>,
    steps: &mut usize,
) -> Option<usize> {
    charge(steps, 1)?;
    if !raw.ids_unique || !raw.is_current(b) || owner >= b.explicit_len() {
        return None;
    }
    let relationships = &b.elements.get(owner)?.owned_relationships;
    charge(steps, relationships.len())?;
    let mut seen = HashSet::new();
    let mut first = None;
    for &relationship in relationships {
        let relation = b.elements.get(relationship)?;
        if relationship >= b.explicit_len()
            || !conforms(relation.ty, "Relationship")
            || !seen.insert(relationship)
            || raw.carrier(b, relationship)? != Some(owner)
            || reject_owned_kind.is_some_and(|kind| conforms(relation.ty, kind))
        {
            return None;
        }
        if first.is_none()
            && conforms(relation.ty, "Membership")
            && !conforms(relation.ty, excluded_kind)
        {
            first = Some(relationship);
        }
    }
    let relation = b.elements.get(first?)?;
    if conforms(relation.ty, "OwningMembership")
        || !relation.children.is_empty()
        || !relation.owned_relationships.is_empty()
        || relation.owning_relationship.is_some()
    {
        return None;
    }
    let target_id = relation.props.get("memberElement")?.as_reference()?;
    let source_id = b.elements[owner].id;
    for key in ["membershipOwningNamespace", "owningRelatedElement"] {
        if relation
            .props
            .get(key)
            .is_some_and(|value| value.as_reference() != Some(source_id))
        {
            return None;
        }
    }
    for key in ["ownedMemberElement", "ownedMemberFeature"] {
        if relation.props.get(key).is_some() {
            return None;
        }
    }
    if relation
        .props
        .get("memberFeature")
        .is_some_and(|value| value.as_reference() != Some(target_id))
        || relation.props.get("visibility").is_some_and(|value| {
            !matches!(value.as_str(), Some("public" | "protected" | "private"))
        })
    {
        return None;
    }
    for (key, expected) in [
        ("source", &[source_id][..]),
        ("target", &[target_id][..]),
        ("relatedElement", &[source_id, target_id][..]),
        ("ownedRelatedElement", &[][..]),
    ] {
        if let Some(value) = relation.props.get(key) {
            let values = value.as_array()?;
            charge(steps, values.len())?;
            if values.len() != expected.len()
                || values
                    .iter()
                    .zip(expected)
                    .any(|(value, id)| value.as_reference() != Some(*id))
            {
                return None;
            }
        }
    }
    charge(steps, 1)?;
    // No ambient lookup cache or whole-model scan participates in a per-owner
    // membership selector; the endpoint comes from this exact checked snapshot.
    let target = raw.element_for_uuid(b, target_id)?;
    conforms(b.elements.get(target)?.ty, required_target_kind).then_some(target)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};

    fn fixture() -> (ResolvedModel, usize, usize, usize) {
        let mut model = Model::new();
        let parsed = model.add_source(
            "membership-evidence.kerml",
            "function F {in x; return r;} package P; feature call=F(1);",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let function = r.resolve_qualified("F").unwrap().0;
        let package = r.resolve_qualified("P").unwrap().0;
        let call =
            r.b.elements
                .iter()
                .position(|e| e.ty == "InvocationExpression")
                .unwrap();
        (r, call, function, package)
    }
    #[test]
    fn shared_owned_parameter_selector_preserves_reciprocal_narrowed_aliases() {
        for (key, on_child) in [
            ("ownedMemberParameter", false),
            ("owningFeatureMembership", true),
            ("owningParameterMembership", true),
        ] {
            for bad in 0..4 {
                let (mut r, function, _, package) = fixture();
                let membership = r.b.elements[function]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&rel| r.b.elements[rel].ty == "ParameterMembership")
                    .unwrap();
                let x = r.b.elements[membership].children[0];
                let row = if on_child { x } else { membership };
                let expected = r.b.elements[if on_child { membership } else { x }].id;
                let wrong = r.b.elements[package].id;
                let value = match bad {
                    0 => serde_json::json!({"@id":expected.to_string()}),
                    1 => serde_json::json!({"@id":wrong.to_string()}),
                    2 => serde_json::Value::Null,
                    _ => serde_json::json!([]),
                };
                r.b.elements[row].props.insert(key, value);
                let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
                assert_eq!(
                    member(&r.b, &raw, function, membership, &mut 0),
                    (bad == 0).then_some(x),
                    "{key}, {bad}"
                );
            }
        }
    }

    #[test]
    fn shared_member_selector_refuses_stale_rows_and_exhaustion_without_poisoning_retry() {
        let (mut r, _, function, _) = fixture();
        let x = r.resolve_qualified("F::x").unwrap().0;
        let membership = r.b.elements[x].owning_relationship.unwrap();
        let raw = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        let mut exhausted = crate::eval::MAX_STEPS;
        assert_eq!(
            member(&r.b, &raw, function, membership, &mut exhausted),
            None
        );
        assert_eq!(member(&r.b, &raw, function, membership, &mut 0), Some(x));
        r.b.elements[membership]
            .props
            .insert("memberElement", serde_json::Value::Null);
        assert_eq!(member(&r.b, &raw, function, membership, &mut 0), None);
        let fresh = StoredStructure::for_query(&mut r.b, &mut 0).unwrap();
        assert_eq!(member(&r.b, &fresh, function, membership, &mut 0), None);
    }

    #[test]
    fn local_callee_is_identity_checked_and_budget_retry_is_fresh() {
        let (mut r, call, function, _) = fixture();
        let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert_eq!(
            first_unowned_member(
                &mut r.b,
                &raw,
                call,
                "FeatureMembership",
                "Type",
                None,
                &mut 0
            ),
            Some(function)
        );
        let mut exhausted = crate::eval::MAX_STEPS;
        assert_eq!(
            first_unowned_member(
                &mut r.b,
                &raw,
                call,
                "FeatureMembership",
                "Type",
                None,
                &mut exhausted
            ),
            None
        );
        assert_eq!(
            first_unowned_member(
                &mut r.b,
                &raw,
                call,
                "FeatureMembership",
                "Type",
                None,
                &mut 0
            ),
            Some(function)
        );
    }
    #[test]
    fn wrong_kind_first_membership_is_never_skipped_for_a_later_valid_callee() {
        let (mut r, call, _, package) = fixture();
        let first = r.b.elements[call]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| {
                conforms(r.b.elements[rel].ty, "Membership")
                    && !conforms(r.b.elements[rel].ty, "FeatureMembership")
            })
            .unwrap();
        let mut later = r.b.elements[first].clone();
        later.id = uuid::Uuid::from_u128(0x87d46f5c964140528cf7c042c0505155);
        let later_index = r.b.elements.len();
        r.b.elements.push(later);
        r.b.elements[call].owned_relationships.push(later_index);
        let package_id = r.b.elements[package].id;
        r.b.elements[first].props.insert(
            "memberElement",
            serde_json::json!({"@id":package_id.to_string()}),
        );
        let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
        assert_eq!(
            first_unowned_member(
                &mut r.b,
                &raw,
                call,
                "FeatureMembership",
                "Type",
                None,
                &mut 0
            ),
            None
        );
    }
    #[test]
    fn contradictory_membership_source_target_and_carrier_refuse_local_edges() {
        for key in ["source", "target", "membershipOwningNamespace"] {
            let (mut r, call, _, package) = fixture();
            let membership = r.b.elements[call]
                .owned_relationships
                .iter()
                .copied()
                .find(|&rel| {
                    conforms(r.b.elements[rel].ty, "Membership")
                        && !conforms(r.b.elements[rel].ty, "FeatureMembership")
                })
                .unwrap();
            let wrong = r.b.elements[package].id;
            let value = if key == "membershipOwningNamespace" {
                serde_json::json!({"@id":wrong.to_string()})
            } else {
                serde_json::json!([{"@id":wrong.to_string()}])
            };
            r.b.elements[membership].props.insert(key, value);
            let raw = StoredStructure::get(&mut r.b, &mut 0).unwrap();
            assert_eq!(
                first_unowned_member(
                    &mut r.b,
                    &raw,
                    call,
                    "FeatureMembership",
                    "Type",
                    None,
                    &mut 0
                ),
                None,
                "{key}"
            );
        }
    }
}
