//! Bounded owned-result additions over stored expression identities.
//!
//! Planning runs over the unchanged source graph and shared carrier index.
//! Publication happens only after all endpoints and generated IDs are admitted.
//! This implements the result/Subsetting obligation of FeatureReferenceExpression;
//! It also supplies the owned binary BindingConnector obligation. Required
//! connector library ancestry/featuring and broader expression rules remain qualified.
use super::{
    Builder, Elem, semantic_ownership::SemanticOwnership, structural_index::StoredStructure,
};
use crate::properties::Properties;
use serde_json::json;
use std::collections::HashSet;
use uuid::Uuid;

fn charge(steps: &mut usize, amount: usize) -> Option<()> {
    *steps = steps.saturating_add(amount);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}

/// The only plan admitted by the first result increment. Existing owned results
/// are left unchanged; absence from this plan is never a completeness claim.
pub(super) struct OwnedResultPlan {
    expression: usize,
    referent: usize,
    membership_id: Uuid,
    result_id: Uuid,
    specialization_id: Uuid,
    binding_ids: [Uuid; 8],
    relationship_type: &'static str,
    source_key: &'static str,
    target_key: &'static str,
}

impl OwnedResultPlan {
    pub(super) fn ids(&self) -> impl Iterator<Item = Uuid> + '_ {
        [self.membership_id, self.result_id, self.specialization_id]
            .into_iter()
            .chain(self.binding_ids)
    }
}

/// Read once before appending any semantic nodes. The shared structural index
/// supplies UUID uniqueness and carrier facts; it does not duplicate ownership.
/// None is an interrupted proof: discard every prepared plan, so budget order
/// cannot publish a prefix of this family. Some does not certify unsupported
/// expressions; only each returned plan is a positive admission.
pub(super) fn plan_reference_results(
    b: &mut Builder,
    steps: &mut usize,
) -> Option<Vec<OwnedResultPlan>> {
    let mut plans = Vec::new();
    let raw = StoredStructure::get(b, steps)?;
    // UUID uniqueness is independent of unrelated source-edge anomalies.
    // This local positive proof validates its own complete carrier path.
    if !raw.ids_unique {
        return Some(plans);
    }
    let from = b.explicit_len();
    charge(steps, from)?;
    let mut assigned_ids = HashSet::new();
    for expression in 0..from {
        if b.elements[expression].ty != "FeatureReferenceExpression" {
            continue;
        }
        let Some(referent) = reference_referent(b, &raw, expression, steps) else {
            if *steps > crate::eval::MAX_STEPS {
                return None;
            }
            continue;
        };
        let expression_id = b.elements[expression].id;
        let referent_id = b.elements[referent].id;
        let result_id = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{expression_id}/implied/ownedResult").as_bytes(),
        );
        let membership_id = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{expression_id}/implied/returnMembership").as_bytes(),
        );
        let subsetting_id = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{result_id}/implied/Subsetting/{referent_id}").as_bytes(),
        );
        let binding_id = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{expression_id}/implied/referenceBinding").as_bytes(),
        );
        let binding_member = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{expression_id}/implied/referenceBindingMembership").as_bytes(),
        );
        let end_id = |position: usize| {
            Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{binding_id}/implied/end/{position}").as_bytes(),
            )
        };
        let end_member = |position: usize| {
            Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{binding_id}/implied/endMembership/{position}").as_bytes(),
            )
        };
        let reference_id = |end: Uuid, target: Uuid| {
            Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{end}/implied/ReferenceSubsetting/{target}").as_bytes(),
            )
        };
        let binding_ids = [
            binding_member,
            binding_id,
            end_member(0),
            end_id(0),
            reference_id(end_id(0), referent_id),
            end_member(1),
            end_id(1),
            reference_id(end_id(1), result_id),
        ];
        let ids = [
            membership_id,
            result_id,
            subsetting_id,
            binding_ids[0],
            binding_ids[1],
            binding_ids[2],
            binding_ids[3],
            binding_ids[4],
            binding_ids[5],
            binding_ids[6],
            binding_ids[7],
        ];
        charge(steps, ids.len())?;
        let unique: HashSet<_> = ids.iter().copied().collect();
        if unique.len() != ids.len() {
            continue;
        }
        if ids
            .iter()
            .any(|id| b.element_index_of_uuid(*id).is_some() || assigned_ids.contains(id))
        {
            continue;
        }
        assigned_ids.extend(ids);
        plans.push(OwnedResultPlan {
            expression,
            referent,
            membership_id,
            result_id,
            specialization_id: subsetting_id,
            binding_ids,
            relationship_type: "Subsetting",
            source_key: "subsettingFeature",
            target_key: "subsettedFeature",
        });
        if *steps > crate::eval::MAX_STEPS {
            return None;
        }
    }
    Some(plans)
}

fn reference_referent(
    b: &mut Builder,
    raw: &StoredStructure,
    expression: usize,
    steps: &mut usize,
) -> Option<usize> {
    super::membership_evidence::first_unowned_member(
        b,
        raw,
        expression,
        "ParameterMembership",
        "Feature",
        Some("ReturnParameterMembership"),
        steps,
    )
}

pub(super) struct StagedResult {
    pub specializations: [(Uuid, Uuid); 3],
    pub featuring: [super::local_featuring::Role; 3],
}

/// Called after generic implied relationships have been registered. Only new
/// rows are mutated; all source relationships, children and UUIDs remain intact.
pub(super) fn stage_owned_result(
    b: &Builder,
    ownership: &mut SemanticOwnership,
    plan: OwnedResultPlan,
    start: usize,
    output: &mut Vec<Elem>,
) -> StagedResult {
    let membership = start;
    let result = membership + 1;
    let subsetting = membership + 2;
    let source_id = b.elements[plan.expression].id;
    let target_id = b.elements[plan.referent].id;
    let mut member_props = Properties::new();
    member_props.insert("isImplied", json!(true));
    member_props.insert("owningRelatedElement", json!({"@id":source_id.to_string()}));
    member_props.insert("visibility", json!("public"));
    let mut result_props = Properties::new();
    result_props.insert("direction", json!("out"));
    let mut subsetting_props = Properties::new();
    subsetting_props.insert("isImplied", json!(true));
    subsetting_props.insert(
        "owningRelatedElement",
        json!({"@id":plan.result_id.to_string()}),
    );
    subsetting_props.insert(plan.source_key, json!({"@id":plan.result_id.to_string()}));
    subsetting_props.insert(plan.target_key, json!({"@id":target_id.to_string()}));
    let rows = [
        Elem {
            ty: "ReturnParameterMembership",
            id: plan.membership_id,
            path: String::new(),
            path_parent: None,
            props: member_props,
            owned_relationships: Default::default(),
            children: vec![result].into(),
            owning_relationship: None,
        },
        Elem {
            ty: "Feature",
            id: plan.result_id,
            path: String::new(),
            path_parent: None,
            props: result_props,
            owned_relationships: vec![subsetting].into(),
            children: Default::default(),
            owning_relationship: Some(membership),
        },
        Elem {
            ty: plan.relationship_type,
            id: plan.specialization_id,
            path: String::new(),
            path_parent: None,
            props: subsetting_props,
            owned_relationships: Default::default(),
            children: Default::default(),
            owning_relationship: None,
        },
    ];
    // The plan and sequential materializer establish these invariants before
    // publication. No user payload can invoke an arbitrary owner override.
    ownership
        .register(membership, Some(plan.expression), plan.expression, true)
        .expect("ordered result membership");
    ownership
        .register(result, None, plan.expression, false)
        .expect("ordered result feature");
    ownership
        .register(subsetting, Some(result), plan.expression, false)
        .expect("ordered result specialization");
    output.extend(rows);
    ownership
        .record_result(plan.expression, membership, result)
        .expect("unique admitted result projection");
    let (binding, first, second) = stage_binding(
        b,
        ownership,
        plan.expression,
        plan.expression,
        plan.referent,
        plan.result_id,
        &plan.binding_ids,
        start + 3,
        output,
    );
    StagedResult {
        specializations: [
            (plan.result_id, target_id),
            (plan.binding_ids[3], target_id),
            (plan.binding_ids[6], plan.result_id),
        ],
        featuring: [
            super::local_featuring::Role {
                source: result,
                target: plan.expression,
                anchor: plan.expression,
            },
            super::local_featuring::Role {
                source: first,
                target: binding,
                anchor: plan.expression,
            },
            super::local_featuring::Role {
                source: second,
                target: binding,
                anchor: plan.expression,
            },
        ],
    }
}

/// The BindingConnector is both Feature and Relationship, owned as a child of
/// an OwningMembership. This deliberately does not assert that the expression
/// is its featuring Type: the required rule says ownedMember, and the connector
/// relates an outer referent to the result. It has no direct relationship carrier;
/// its two EndFeatureMemberships and ReferenceSubsettings do. Do not conflate
/// that legitimate dual metaclass with a malformed membership child backlink.
#[allow(clippy::too_many_arguments)]
fn stage_binding(
    b: &Builder,
    ownership: &mut SemanticOwnership,
    owner: usize,
    anchor: usize,
    referent: usize,
    target_id: Uuid,
    binding_ids: &[Uuid; 8],
    start: usize,
    output: &mut Vec<Elem>,
) -> (usize, usize, usize) {
    let binding = start + 1;
    let first = start + 3;
    let second = start + 6;
    let owner_id = b.elements[owner].id;
    let referent_id = b.elements[referent].id;
    let mut rows = Vec::with_capacity(8);
    let membership_props = |owner: Uuid| {
        let mut props = Properties::new();
        props.insert("isImplied", json!(true));
        props.insert("visibility", json!("public"));
        props.insert("owningRelatedElement", json!({"@id":owner.to_string()}));
        props
    };
    let node = |ty: &'static str,
                id: Uuid,
                owning_relationship: Option<usize>,
                children: Vec<usize>,
                owned_relationships: Vec<usize>,
                props: Properties| Elem {
        ty,
        id,
        path: String::new(),
        path_parent: None,
        props,
        children: children.into(),
        owned_relationships: owned_relationships.into(),
        owning_relationship,
    };
    rows.push(node(
        "OwningMembership",
        binding_ids[0],
        None,
        vec![binding],
        vec![],
        membership_props(owner_id),
    ));
    let mut binding_props = Properties::new();
    binding_props.insert("isImplied", json!(true));
    rows.push(node(
        "BindingConnector",
        binding_ids[1],
        Some(start),
        vec![],
        vec![start + 2, start + 5],
        binding_props,
    ));
    for (offset, end, target_id) in [(2, first, referent_id), (5, second, target_id)] {
        rows.push(node(
            "EndFeatureMembership",
            binding_ids[offset],
            None,
            vec![end],
            vec![],
            membership_props(binding_ids[1]),
        ));
        let mut props = Properties::new();
        props.insert("isEnd", json!(true));
        props.insert("isComposite", json!(false));
        rows.push(node(
            "Feature",
            binding_ids[offset + 1],
            Some(start + offset),
            vec![],
            vec![start + offset + 2],
            props,
        ));
        let mut props = Properties::new();
        props.insert("isImplied", json!(true));
        props.insert(
            "owningRelatedElement",
            json!({"@id":binding_ids[offset+1].to_string()}),
        );
        props.insert(
            "subsettingFeature",
            json!({"@id":binding_ids[offset+1].to_string()}),
        );
        props.insert("referencedFeature", json!({"@id":target_id.to_string()}));
        rows.push(node(
            "ReferenceSubsetting",
            binding_ids[offset + 2],
            None,
            vec![],
            vec![],
            props,
        ));
    }
    for (offset, row) in rows.into_iter().enumerate() {
        let carrier = match offset {
            0 => Some(owner),
            2 | 5 => Some(binding),
            4 => Some(first),
            7 => Some(second),
            _ => None,
        };
        output.push(row);
        ownership
            .register(start + offset, carrier, anchor, offset == 0)
            .expect("prevalidated generated binding subtree");
    }
    (binding, first, second)
}

pub(super) struct ConstructorDefaultPlan {
    expression: usize,
    result: usize,
    feature: usize,
    value: usize,
    ids: [Uuid; 8],
}
impl ConstructorDefaultPlan {
    pub(super) fn ids(&self) -> impl Iterator<Item = Uuid> + '_ {
        self.ids.iter().copied()
    }
}
/// Omitted defaults share constructor argument selection and the checked
/// redefinition provider. Incomplete constructors contribute no partial family.
pub(super) fn plan_constructor_defaults(
    b: &mut Builder,
    reserved: &HashSet<Uuid>,
    steps: &mut usize,
) -> Option<Vec<ConstructorDefaultPlan>> {
    if b.graph_format != crate::model::GraphFormat::CanonicalV3 {
        return Some(Vec::new());
    }
    let mut batch = super::constructor_bindings::ConstructorBatchEvidence::default();
    let mut plans = Vec::new();
    charge(steps, reserved.len())?;
    let mut assigned = reserved.clone();
    for expression in 0..b.explicit_len() {
        charge(steps, 1)?;
        if b.elements[expression].ty != "ConstructorExpression" {
            continue;
        }
        let Ok(arguments) = b.checked_constructor_bindings_in_batch(
            expression,
            steps,
            Some(&mut Default::default()),
            &mut batch,
        ) else {
            charge(steps, 0)?;
            continue;
        };
        let Ok(defaults) = b.checked_constructor_defaults_in_batch(&arguments, steps, &mut batch)
        else {
            charge(steps, 0)?;
            continue;
        };
        let mut candidate = Vec::new();
        let mut candidate_ids = HashSet::new();
        let mut valid = true;
        for default in defaults {
            charge(steps, 8)?;
            let owner_id = b.elements[arguments.result.0].id;
            let valuation_id = b.elements[default.valuation.0].id;
            let binding = Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{owner_id}/implied/defaultBinding/{valuation_id}").as_bytes(),
            );
            let id = |suffix: &str| {
                Uuid::new_v5(
                    &Uuid::NAMESPACE_OID,
                    format!("{binding}/{suffix}").as_bytes(),
                )
            };
            let ids = [
                id("membership"),
                binding,
                id("endMembership/0"),
                id("end/0"),
                id("reference/0"),
                id("endMembership/1"),
                id("end/1"),
                id("reference/1"),
            ];
            for generated in ids {
                if b.element_index_of_uuid(generated).is_some()
                    || assigned.contains(&generated)
                    || !candidate_ids.insert(generated)
                {
                    valid = false;
                }
            }
            candidate.push(ConstructorDefaultPlan {
                expression,
                result: arguments.result.0,
                feature: default.feature_with_value.0,
                value: default.value.0,
                ids,
            });
        }
        if valid {
            assigned.extend(candidate_ids);
            plans.extend(candidate);
        }
    }
    Some(plans)
}
pub(super) fn stage_constructor_default(
    b: &Builder,
    ownership: &mut SemanticOwnership,
    plan: ConstructorDefaultPlan,
    start: usize,
    output: &mut Vec<Elem>,
) -> ([(Uuid, Uuid); 2], [super::local_featuring::Role; 2]) {
    let feature_id = b.elements[plan.feature].id;
    let value_id = b.elements[plan.value].id;
    let (binding, first, second) = stage_binding(
        b,
        ownership,
        plan.result,
        plan.expression,
        plan.feature,
        value_id,
        &plan.ids,
        start,
        output,
    );
    (
        [(plan.ids[3], feature_id), (plan.ids[6], value_id)],
        [
            super::local_featuring::Role {
                source: first,
                target: binding,
                anchor: plan.expression,
            },
            super::local_featuring::Role {
                source: second,
                target: binding,
                anchor: plan.expression,
            },
        ],
    )
}

/// Verify the published subtree by reciprocal membership and typed endpoint
/// evidence. Source isImplied flags cannot stand in for a generated owner.
pub(super) fn constructor_default_present(
    b: &mut Builder,
    owner: usize,
    default: &super::constructor_bindings::ConstructorDefaultBinding,
    steps: &mut usize,
) -> bool {
    let checked = (|| {
        let raw = StoredStructure::for_query(b, steps)?;
        let owner_id = b.elements[owner].id;
        let valuation_id = b.elements[default.valuation.0].id;
        let binding_id = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{owner_id}/implied/defaultBinding/{valuation_id}").as_bytes(),
        );
        let binding = raw.element_for_uuid(b, binding_id)?;
        if b.elements[binding].ty != "BindingConnector" || binding < b.explicit_len() {
            return None;
        }
        let membership = b.elements[binding].owning_relationship?;
        let view = b.semantic_ownership.as_ref()?;
        if !view.matches_suffix(b)
            || view.generated_relationship_owner(membership) != Some(owner)
            || super::membership_evidence::member(b, &raw, owner, membership, steps)? != binding
        {
            return None;
        }
        let members = super::semantic_ownership::owned_relationships(b, binding)?;
        charge(steps, members.len())?;
        let members: Vec<_> = members
            .iter()
            .filter(|&rel| b.elements[rel].ty == "EndFeatureMembership")
            .collect();
        if members.len() != 2 {
            return None;
        }
        for (membership, expected) in members
            .into_iter()
            .zip([default.feature_with_value.0, default.value.0])
        {
            let end = super::membership_evidence::member(b, &raw, binding, membership, steps)?;
            if b.elements[end].ty != "Feature"
                || b.elements[end].props.get("isEnd").and_then(|v| v.as_bool()) != Some(true)
                || !raw.membership_domains(b, steps)?.owner_complete(binding)
            {
                return None;
            }
            let relationships = super::semantic_ownership::owned_relationships(b, end)?;
            charge(steps, relationships.len())?;
            let references: Vec<_> = relationships
                .iter()
                .filter(|&rel| b.elements[rel].ty == "ReferenceSubsetting")
                .collect();
            if references.len() != 1
                || super::semantic_ownership::checked_relationship_carrier(
                    b,
                    &raw,
                    references[0],
                    steps,
                ) != Some(Some(end))
            {
                return None;
            }
            let typing = raw.typing(b, steps)?;
            if typing.sources_incomplete {
                return None;
            }
            let incoming = typing
                .relationships
                .get(&end)
                .map_or(&[][..], Vec::as_slice);
            charge(steps, incoming.len())?;
            if incoming.iter().any(|&relationship| {
                b.elements[relationship].ty == "ReferenceSubsetting"
                    && relationship != references[0]
            }) {
                return None;
            }
            let target = super::type_relations::endpoint_with_carrier(
                b,
                end,
                Some(end),
                references[0],
                &["specific", "subsettingFeature", "referencingFeature"],
                &["general", "subsettedFeature", "referencedFeature"],
                "Feature",
                steps,
            )?;
            if target != expected {
                return None;
            }
        }
        Some(())
    })();
    checked.is_some()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};

    fn model() -> (ResolvedModel, usize) {
        let mut model = Model::new();
        model.add_source(
            "owned-results.kerml",
            "feature n; feature x=n; feature y=n;",
        );
        assert!(!model.has_errors());
        let r = ResolvedModel::build(&model);
        let expression = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap()
            .0;
        (r, expression)
    }

    #[test]
    fn owning_referent_without_owned_child_is_not_admitted() {
        let (mut r, expression) = model();
        let membership = r.b.elements[expression].owned_relationships[0];
        assert_eq!(r.b.elements[membership].ty, "Membership");
        for bad_kind in ["OwningMembership", "FeatureMembership"] {
            r.b.elements[membership].ty = bad_kind;
            let plans = plan_reference_results(&mut r.b, &mut 0).unwrap();
            assert!(!plans.iter().any(|p| p.expression == expression));
        }
    }

    #[test]
    fn exhausted_planning_drops_all_earlier_positive_plans() {
        let (r, _) = model();
        let mut measured = r.b.clone();
        let mut used = 0;
        let plans = plan_reference_results(&mut measured, &mut used).unwrap();
        assert_eq!(plans.len(), 2);
        assert!(used > 1 && used < crate::eval::MAX_STEPS);
        let mut limited = r.b.clone();
        let count = limited.elements.len();
        let mut steps = crate::eval::MAX_STEPS - used + 1;
        assert!(plan_reference_results(&mut limited, &mut steps).is_none());
        assert!(steps > crate::eval::MAX_STEPS);
        assert_eq!(
            limited.elements.len(),
            count,
            "planning never appends a prefix"
        );
    }

    #[test]
    fn certified_generated_carriers_still_refuse_raw_contradictions_and_duplicate_ids() {
        let (mut r, expression) = model();
        r.ensure_implied();
        let view = r.b.semantic_ownership.as_ref().unwrap().clone();
        let result = view.result(expression).unwrap();
        let mut steps = 0;
        let raw = StoredStructure::get(&mut r.b, &mut steps).unwrap();
        assert_eq!(
            view.effective_carrier(&r.b, &raw, result.membership, &mut steps),
            Some(Some(expression))
        );
        let wrong_id = r.b.elements[result.feature].id;
        r.b.elements[result.membership]
            .props
            .insert("owningRelatedElement", json!({"@id":wrong_id.to_string()}));
        let raw = StoredStructure::get(&mut r.b, &mut steps).unwrap();
        assert_eq!(
            view.effective_carrier(&r.b, &raw, result.membership, &mut steps),
            None
        );
        let owner_id = r.b.elements[expression].id;
        r.b.elements[result.membership]
            .props
            .insert("owningRelatedElement", json!({"@id":owner_id.to_string()}));
        r.b.elements[result.membership].owning_relationship = Some(result.membership);
        let raw = StoredStructure::get(&mut r.b, &mut steps).unwrap();
        assert_eq!(
            view.effective_carrier(&r.b, &raw, result.membership, &mut steps),
            None
        );
        r.b.elements[result.membership].owning_relationship = None;
        r.b.elements[result.feature].id = owner_id;
        r.b.id_index = None;
        let raw = StoredStructure::get(&mut r.b, &mut steps).unwrap();
        assert!(!raw.ids_unique);
        assert_eq!(
            view.effective_carrier(&r.b, &raw, result.membership, &mut steps),
            None
        );
    }
    #[test]
    fn owned_binding_has_membership_backlink_but_no_direct_relationship_carrier() {
        let (mut r, expression) = model();
        r.ensure_implied();
        let view = r.b.semantic_ownership.clone().unwrap();
        let binding_member = view
            .relationships(&r.b, expression)
            .unwrap()
            .iter()
            .find(|&rel| r.b.elements[rel].ty == "OwningMembership")
            .unwrap();
        let binding = r.b.elements[binding_member].children[0];
        assert_eq!(r.b.elements[binding].ty, "BindingConnector");
        assert_eq!(
            r.b.elements[binding].owning_relationship,
            Some(binding_member)
        );
        let mut steps = 0;
        let raw = StoredStructure::for_query(&mut r.b, &mut steps).unwrap();
        assert_eq!(raw.carrier(&r.b, binding), Some(None));
        assert_eq!(
            super::super::semantic_ownership::checked_relationship_carrier(
                &r.b, &raw, binding, &mut steps
            ),
            Some(None)
        );
        assert_eq!(
            super::super::semantic_ownership::checked_relationship_carrier(
                &r.b,
                &raw,
                binding_member,
                &mut steps
            ),
            Some(Some(expression))
        );
        assert_eq!(
            r.owner(super::super::ElementRef(binding)),
            Some(super::super::ElementRef(expression))
        );
    }
}
