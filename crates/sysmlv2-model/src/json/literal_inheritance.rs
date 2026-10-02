//! Supported fixed-base expression heritage without allocating textual declaration scopes.
use super::{Builder, MembershipContext, MembershipProjection, implied};
use crate::metaclass::conforms;
use uuid::Uuid;

/// Present generic endpoint arrays must describe the same local carrier as
/// its named ends. relatedElement is a nonunique Sequence: preserve both
/// occurrences when source and target are the same identity.
fn consistent_relation_arrays(
    b: &Builder,
    relationship: usize,
    source: Uuid,
    target: Uuid,
    context: &mut MembershipContext,
) -> bool {
    let relation = &b.elements[relationship];
    if !context.charge(relation.children.len()) || relation.children.len() > 2 {
        return false;
    }
    let mut children = [Uuid::nil(); 2];
    for (index, &child) in relation.children.iter().enumerate() {
        let Some(element) = b.elements.get(child) else {
            return false;
        };
        if children[..index].contains(&element.id)
            || element.owning_relationship != Some(relationship)
            || ![source, target].contains(&element.id)
        {
            return false;
        }
        children[index] = element.id;
    }
    for (key, expected) in [
        ("source", &[source][..]),
        ("target", &[target][..]),
        ("relatedElement", &[source, target][..]),
        ("ownedRelatedElement", &children[..relation.children.len()]),
    ] {
        let Some(value) = relation.props.get(key) else {
            continue;
        };
        let Some(values) = value.as_array() else {
            return false;
        };
        if !context.charge(values.len().saturating_add(1))
            || values.len() != expected.len()
            || !values
                .iter()
                .zip(expected)
                .all(|(value, id)| value.as_reference() == Some(*id))
        {
            return false;
        }
    }
    true
}

impl Builder {
    /// Preserve the existing empty result for other scope-less elements.
    /// Supported fixed-base results require a loaded, typed library feature and exactly one
    /// surviving typed return Membership. Missing/external library fragments
    /// remain incomplete; no result or type is invented from the expression value.
    pub(super) fn literal_inherited_memberships(
        &mut self,
        element: usize,
        include_implied: bool,
    ) -> MembershipProjection {
        let Some(owner) = self.elements.get(element) else {
            return MembershipProjection::default();
        };
        let ty = owner.ty;
        if implied::literal_implied_base(ty).is_none() {
            return MembershipProjection::default();
        }
        if include_implied && self.semantic_ready {
            self.ensure_positional_redefinitions();
        }
        let mut context = MembershipContext::default();
        if self.literal_identities_unique(Some(&mut context.steps)) != Some(true) {
            return MembershipProjection {
                incomplete: true,
                truncated: context.steps > crate::eval::MAX_STEPS,
                ..MembershipProjection::default()
            };
        }
        let family = context.new_type_family();
        let inherited = self.contextual_inherited_bindings(
            element,
            include_implied,
            &[],
            &[],
            family,
            &mut context,
            0,
        );
        let mut result = MembershipProjection {
            membership_order: inherited.membership_order.clone(),
            truncated: inherited.truncated,
            incomplete: inherited.incomplete,
            implicit_redefinitions: inherited.implicit_redefinitions.clone(),
        };
        if !include_implied {
            return result;
        }
        let required = self
            .planned_literal_target(ty)
            .and_then(|id| self.element_index_of_uuid(id));
        let required_ready = required.is_some_and(|required| {
            conforms(self.elements[required].ty, "Feature")
                && self.literal_has_typing(required, "Function", &mut context)
        });
        let result_ready = self
            .literal_inherited_result(&result, &mut context)
            .is_some_and(|member| self.literal_has_typing(member, "Type", &mut context));
        if !required_ready || !result_ready {
            result.incomplete = true;
        }
        result.incomplete |= self.recorded_lookup_incomplete;
        result.truncated |= context.steps > crate::eval::MAX_STEPS;
        result
    }

    /// Result identity belongs to the library, through the inherited return
    /// Membership. Distinct surviving returns are indeterminate, not first-wins.
    pub(super) fn literal_inherited_result(
        &mut self,
        inherited: &MembershipProjection,
        context: &mut MembershipContext,
    ) -> Option<usize> {
        if !self.literal_identities_unique(Some(&mut context.steps))? {
            return None;
        }
        if !context.charge(inherited.membership_order.len()) {
            return None;
        }
        let mut found = None;
        for &membership in &inherited.membership_order {
            if !conforms(self.elements[membership].ty, "ReturnParameterMembership") {
                continue;
            }
            let member = self.stored_membership_member(membership)?;
            if !conforms(self.elements[member].ty, "Feature")
                || self.elements[member].owning_relationship != Some(membership)
                || self.elements[membership].children.len() != 1
                || self.elements[membership].children.first().copied() != Some(member)
                || found.is_some_and(|(previous, _)| previous != membership)
            {
                return None;
            }
            let relation = &self.elements[membership];
            let owner_id = relation.props.get("owningRelatedElement")?.as_reference()?;
            for key in ["membershipOwningNamespace", "owningType"] {
                if relation
                    .props
                    .get(key)
                    .is_some_and(|v| v.as_reference() != Some(owner_id))
                {
                    return None;
                }
            }
            for key in [
                "memberElement",
                "ownedMemberElement",
                "ownedMemberFeature",
                "memberFeature",
            ] {
                if relation
                    .props
                    .get(key)
                    .is_some_and(|v| v.as_reference() != Some(self.elements[member].id))
                {
                    return None;
                }
            }
            if !consistent_relation_arrays(
                self,
                membership,
                owner_id,
                self.elements[member].id,
                context,
            ) {
                return None;
            }
            let owner = self.element_index_of_uuid(owner_id)?;
            if !conforms(self.elements[owner].ty, "Type")
                || !context.charge(self.elements[owner].owned_relationships.len())
                || self.elements[owner]
                    .owned_relationships
                    .iter()
                    .filter(|&&r| r == membership)
                    .count()
                    != 1
            {
                return None;
            }
            found = Some((membership, member));
        }
        found.map(|(_, member)| member)
    }

    fn literal_has_typing(
        &mut self,
        feature: usize,
        target_kind: &str,
        context: &mut MembershipContext,
    ) -> bool {
        let relationships = self.elements[feature].owned_relationships.clone();
        if !context.charge(relationships.len()) {
            return false;
        }
        let mut found = false;
        let mut seen = std::collections::HashSet::new();
        for relationship in relationships {
            let relation = &self.elements[relationship];
            if !conforms(relation.ty, "FeatureTyping") {
                continue;
            }
            if !seen.insert(relationship)
                || relation
                    .props
                    .get("owningRelatedElement")
                    .and_then(|v| v.as_reference())
                    != Some(self.elements[feature].id)
            {
                return false;
            }
            let Some(id) = implied::specialization_target(relation) else {
                return false;
            };
            for key in ["type", "general"] {
                if relation
                    .props
                    .get(key)
                    .is_some_and(|value| value.as_reference() != Some(id))
                {
                    return false;
                }
            }
            for key in ["typedFeature", "specific"] {
                if relation
                    .props
                    .get(key)
                    .is_some_and(|value| value.as_reference() != Some(self.elements[feature].id))
                {
                    return false;
                }
            }
            if !consistent_relation_arrays(
                self,
                relationship,
                self.elements[feature].id,
                id,
                context,
            ) {
                return false;
            }
            let Some(target) = self.element_index_of_uuid(id) else {
                return false;
            };
            if !conforms(self.elements[target].ty, target_kind) {
                return false;
            }
            found = true;
        }
        found
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    use serde_json::json;
    fn model() -> (ResolvedModel, usize, usize) {
        let mut m = Model::new();
        m.add_library_source("literal.kerml", "standard library package Values {datatype Integer;} standard library package Performances {function F {return result:Values::Integer;} expr literalIntegerEvaluations:F;}");
        m.add_source("use.kerml", "feature x=1;");
        assert!(!m.has_errors());
        let mut r = ResolvedModel::build(&m);
        let e = r
            .user_elements()
            .find(|&e| r.element_type(e) == "LiteralInteger")
            .unwrap()
            .0;
        let role = r
            .resolve_qualified("Performances::literalIntegerEvaluations")
            .unwrap();
        assert!(
            r.b.lib_qnames
                .iter()
                .any(|(id, name)| *id == r.element_id(role)
                    && name
                        == &[
                            "Performances".to_owned(),
                            "literalIntegerEvaluations".to_owned()
                        ])
        );
        let result = r.resolve_qualified("Performances::F::result").unwrap().0;
        (r, e, result)
    }
    #[test]
    fn malformed_result_typing_aliases_are_incomplete_without_scope_creation() {
        let (mut r, e, result) = model();
        let scopes = r.b.scopes.len();
        r.b.identity_origin_unit = Some(1);
        let good = r.b.literal_inherited_memberships(e, true);
        assert!(!good.incomplete);
        assert_eq!(r.b.identity_origin_unit, Some(1));
        let relation = r.b.elements[result]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| r.b.elements[rel].ty == "FeatureTyping")
            .unwrap();
        let conflict = r.b.elements[e].id;
        r.b.elements[relation]
            .props
            .insert("general", json!({"@id":conflict.to_string()}));
        let bad = r.b.literal_inherited_memberships(e, true);
        assert!(bad.incomplete);
        assert_eq!(r.b.scopes.len(), scopes);
        assert!(!r.b.elem_scope.contains_key(&e));
    }
    #[test]
    fn nonreciprocal_return_membership_is_not_a_result() {
        let (mut r, e, result) = model();
        let membership = r.b.elements[result].owning_relationship.unwrap();
        r.b.elements[result].owning_relationship = None;
        let inherited = r.b.literal_inherited_memberships(e, true);
        assert!(inherited.incomplete);
        assert!(
            r.b.literal_inherited_result(&inherited, &mut MembershipContext::default())
                .is_none()
        );
        assert!(r.b.elements[membership].children.contains(&result));
    }
    #[test]
    fn conflicting_required_library_names_do_not_emit_an_arbitrary_edge() {
        let (mut r, e, _) = model();
        let other = r.resolve_qualified("Values::Integer").unwrap();
        let other_id = r.element_id(other);
        r.b.lib_qnames.push((
            other_id,
            vec![
                "Performances".to_owned(),
                "literalIntegerEvaluations".to_owned(),
            ],
        ));
        r.b.reset_lookup_caches();
        let projection = r.b.literal_inherited_memberships(e, true);
        assert!(projection.incomplete);
        assert!(projection.membership_order.is_empty());
        assert!(
            r.implied_relationships(crate::json::ElementRef(e))
                .is_empty()
        );
    }

    #[test]
    fn conflicting_return_owner_or_typing_carrier_is_incomplete() {
        for return_owner in [false, true] {
            let (mut r, e, result) = model();
            let relationship = if return_owner {
                r.b.elements[result].owning_relationship.unwrap()
            } else {
                r.b.elements[result]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&rel| r.b.elements[rel].ty == "FeatureTyping")
                    .unwrap()
            };
            let wrong = r.b.elements[e].id;
            r.b.elements[relationship]
                .props
                .insert("owningRelatedElement", json!({"@id":wrong.to_string()}));
            let projection = r.b.literal_inherited_memberships(e, true);
            assert!(projection.incomplete);
        }
    }
    #[test]
    fn contradictory_generic_arrays_refuse_literal_result_readiness() {
        for membership in [false, true] {
            for key in ["source", "target", "relatedElement", "ownedRelatedElement"] {
                for invalid_kind in [false, true] {
                    let (mut r, e, result) = model();
                    let relationship = if membership {
                        r.b.elements[result].owning_relationship.unwrap()
                    } else {
                        r.b.elements[result]
                            .owned_relationships
                            .iter()
                            .copied()
                            .find(|&rel| r.b.elements[rel].ty == "FeatureTyping")
                            .unwrap()
                    };
                    r.b.identity_origin_unit = Some(1);
                    let before = r.b.literal_inherited_memberships(e, true);
                    assert!(!before.incomplete);
                    let wrong = r.b.elements[e].id;
                    let value = if invalid_kind {
                        json!({"@id":wrong.to_string()})
                    } else {
                        json!([{"@id":wrong.to_string()}])
                    };
                    r.b.elements[relationship].props.insert(key, value);
                    let after = r.b.literal_inherited_memberships(e, true);
                    assert_eq!(r.b.identity_origin_unit, Some(1));
                    assert!(
                        after.incomplete,
                        "membership={membership} key={key} invalid_kind={invalid_kind}"
                    );
                }
            }
        }
    }

    #[test]
    fn consistent_generic_arrays_preserve_returns_and_charge_shared_budget() {
        let (mut r, e, result) = model();
        let membership = r.b.elements[result].owning_relationship.unwrap();
        let owner = r.b.elements[membership]
            .props
            .get("owningRelatedElement")
            .unwrap()
            .as_reference()
            .unwrap();
        let member = r.b.elements[result].id;
        for (key, value) in [
            ("source", json!([{"@id":owner.to_string()}])),
            ("target", json!([{"@id":member.to_string()}])),
            (
                "relatedElement",
                json!([{"@id":owner.to_string()},{"@id":member.to_string()}]),
            ),
            ("ownedRelatedElement", json!([{"@id":member.to_string()}])),
        ] {
            r.b.elements[membership].props.insert(key, value);
        }
        assert!(!r.b.literal_inherited_memberships(e, true).incomplete);
        let mut context = MembershipContext::default();
        context.steps = crate::eval::MAX_STEPS - 1;
        assert!(!consistent_relation_arrays(
            &r.b,
            membership,
            owner,
            member,
            &mut context
        ));
        assert!(context.steps > crate::eval::MAX_STEPS);
        assert!(consistent_relation_arrays(
            &r.b,
            membership,
            owner,
            member,
            &mut MembershipContext::default()
        ));
        r.b.elements[membership].props.insert(
            "relatedElement",
            json!([{"@id":member.to_string()},{"@id":owner.to_string()}]),
        );
        assert!(r.b.literal_inherited_memberships(e, true).incomplete);
    }

    #[test]
    fn related_elements_preserve_reflexive_endpoint_occurrences() {
        let (mut r, _, result) = model();
        let relationship = r.b.elements[result]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| r.b.elements[rel].ty == "FeatureTyping")
            .unwrap();
        let id = r.b.elements[result].id;
        for key in ["source", "target"] {
            r.b.elements[relationship]
                .props
                .insert(key, json!([{"@id":id.to_string()}]));
        }
        r.b.elements[relationship].props.insert(
            "relatedElement",
            json!([{"@id":id.to_string()},{"@id":id.to_string()}]),
        );
        assert!(consistent_relation_arrays(
            &r.b,
            relationship,
            id,
            id,
            &mut MembershipContext::default()
        ));
        r.b.elements[relationship]
            .props
            .insert("relatedElement", json!([{"@id":id.to_string()}]));
        assert!(!consistent_relation_arrays(
            &r.b,
            relationship,
            id,
            id,
            &mut MembershipContext::default()
        ));
    }
}
