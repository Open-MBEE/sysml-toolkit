//! Optional local featuring rows over already staged, certified result groups.
//! Failure never mutates or rejects those groups or the dynamic Invocation tail.
use super::{Builder, Elem, dynamic_invocations::Refusal, semantic_ownership::SemanticOwnership};
use crate::properties::Properties;
use std::collections::HashSet;
use uuid::Uuid;

#[derive(Clone, Copy)]
pub(super) struct Role {
    pub source: usize,
    pub target: usize,
    pub anchor: usize,
}
pub(super) struct Plan {
    from: usize,
    before: usize,
    rows: Vec<Elem>,
    replacements: Vec<(usize, Vec<usize>)>,
    roles: Vec<Role>,
    sources: HashSet<usize>,
}
fn charge(steps: &mut usize, n: usize) -> Result<(), Refusal> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(Refusal::WorkLimit)
    } else {
        Ok(())
    }
}
fn staged<'a>(b: &'a Builder, rows: &'a [Elem], index: usize) -> Option<&'a Elem> {
    if index < b.elements.len() {
        b.elements.get(index)
    } else {
        rows.get(index - b.elements.len())
    }
}
fn ref_is(row: &Elem, key: &str, id: Uuid) -> bool {
    row.props.get(key).and_then(|v| v.as_reference()) == Some(id)
}
/// The recipe factory supplies roles; this gate validates their complete local
/// membership path and the nonvariable defaults that justify owned featuring.
pub(super) fn valid(b: &Builder, rows: &[Elem], role: Role) -> bool {
    b.elements
        .get(role.anchor)
        .is_some_and(|anchor| anchor.ty == "FeatureReferenceExpression")
        && valid_path(b, rows, role, role.anchor, true)
}

/// The result factory's BindingConnector is owned by the referenced expression
/// or by the constructor's checked result. Ends remain featured by that exact
/// connector, independently of its own featuring or specialization obligations.
fn valid_path(
    b: &Builder,
    rows: &[Elem],
    role: Role,
    binding_owner: usize,
    allow_result: bool,
) -> bool {
    let Some(source) = staged(b, rows, role.source) else {
        return false;
    };
    let Some(target) = staged(b, rows, role.target) else {
        return false;
    };
    if role.source < b.elements.len()
        || role.target >= role.source
        || role.anchor >= b.explicit_len()
        || source.ty != "Feature"
        || source.props.get("isVariable").is_some()
            && source.props.get("isVariable").and_then(|v| v.as_bool()) != Some(false)
    {
        return false;
    }
    let Some(member_index) = source
        .owning_relationship
        .filter(|&i| i >= b.elements.len() && i < role.source)
    else {
        return false;
    };
    let Some(member) = staged(b, rows, member_index) else {
        return false;
    };
    if member.children.len() != 1
        || member.children[0] != role.source
        || member.owning_relationship.is_some()
        || !ref_is(member, "owningRelatedElement", target.id)
    {
        return false;
    }
    if role.target == role.anchor {
        allow_result
            && member.ty == "ReturnParameterMembership"
            && source.props.get("direction").and_then(|v| v.as_str()) == Some("out")
    } else {
        if target.ty != "BindingConnector"
            || member.ty != "EndFeatureMembership"
            || source.props.get("isEnd").and_then(|v| v.as_bool()) != Some(true)
            || !target
                .owned_relationships
                .iter()
                .any(|&r| Some(r) == source.owning_relationship)
        {
            return false;
        }
        let Some(binding_member) = target.owning_relationship.and_then(|i| staged(b, rows, i))
        else {
            return false;
        };
        binding_member.ty == "OwningMembership"
            && binding_member.owning_relationship.is_none()
            && binding_member.children.len() == 1
            && binding_member.children[0] == role.target
            && ref_is(
                binding_member,
                "owningRelatedElement",
                b.elements[binding_owner].id,
            )
    }
}
pub(super) fn prepare(
    b: &Builder,
    rows: &[Elem],
    roles: &[Role],
    steps: &mut usize,
) -> Result<Plan, Refusal> {
    charge(
        steps,
        1_usize
            .saturating_add(rows.len().saturating_mul(2))
            .saturating_add(roles.len().saturating_mul(20)),
    )?;
    // Reuse the exact immutable UUID projection already admitted by result
    // planning. No extra whole-source map or scan is needed for this family.
    let raw = b
        .stored_structure
        .as_ref()
        .filter(|raw| raw.is_current(b))
        .ok_or(Refusal::Stale)?;
    if !raw.ids_unique {
        return Err(Refusal::Collision);
    }
    let mut ids = HashSet::new();
    for row in rows {
        if raw.element_for_uuid(b, row.id).is_some() || !ids.insert(row.id) {
            return Err(Refusal::Collision);
        }
    }
    let mut plan = Plan {
        from: b.elements.len(),
        before: rows.len(),
        rows: Vec::new(),
        replacements: Vec::new(),
        roles: Vec::new(),
        sources: HashSet::new(),
    };
    for &role in roles {
        let source = staged(b, rows, role.source).ok_or(Refusal::Stale)?;
        let target = staged(b, rows, role.target).ok_or(Refusal::Stale)?;
        // Charge traversal before allocating or validating membership lists.
        let member = source.owning_relationship.and_then(|i| staged(b, rows, i));
        let binding_member = target.owning_relationship.and_then(|i| staged(b, rows, i));
        charge(
            steps,
            source
                .owned_relationships
                .len()
                .saturating_add(target.owned_relationships.len())
                .saturating_add(member.map_or(0, |m| m.children.len()))
                .saturating_add(binding_member.map_or(0, |m| m.children.len())),
        )?;
        let valid_role = if b
            .elements
            .get(role.anchor)
            .is_some_and(|anchor| anchor.ty == "ConstructorExpression")
        {
            let result = super::constructor_bindings::owned_result(b, raw, role.anchor, steps)
                .ok_or({
                    if *steps > crate::eval::MAX_STEPS {
                        Refusal::WorkLimit
                    } else {
                        Refusal::Stale
                    }
                })?;
            valid_path(b, rows, role, result, false)
        } else {
            valid(b, rows, role)
        };
        if !valid_role || !plan.sources.insert(role.source) {
            return Err(Refusal::Stale);
        }
        let id = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{}/implied/TypeFeaturing/{}", source.id, target.id).as_bytes(),
        );
        if raw.element_for_uuid(b, id).is_some() || !ids.insert(id) {
            return Err(Refusal::Collision);
        }
        let index = b.elements.len() + rows.len() + plan.rows.len();
        let mut relationships: Vec<_> = source.owned_relationships.iter().copied().collect();
        relationships.push(index);
        plan.replacements
            .push((role.source - b.elements.len(), relationships));
        plan.roles.push(role);
        let mut props = Properties::new();
        props.insert("isImplied", serde_json::json!(true));
        props.insert(
            "owningRelatedElement",
            serde_json::json!({"@id":source.id.to_string()}),
        );
        props.insert(
            "featureOfType",
            serde_json::json!({"@id":source.id.to_string()}),
        );
        props.insert(
            "featuringType",
            serde_json::json!({"@id":target.id.to_string()}),
        );
        plan.rows.push(Elem {
            ty: "TypeFeaturing",
            id,
            path: String::new(),
            path_parent: None,
            props,
            owned_relationships: Default::default(),
            children: Default::default(),
            owning_relationship: None,
        });
    }
    Ok(plan)
}
impl Plan {
    /// No fallible semantic work remains. These vectors are still private to
    /// the one publisher; old physical rows are not modified or relocated.
    pub(super) fn append(
        self,
        rows: &mut Vec<Elem>,
        ownership: &mut SemanticOwnership,
    ) -> HashSet<usize> {
        assert_eq!(rows.len(), self.before);
        for (owner, relationships) in self.replacements {
            rows[owner].owned_relationships = relationships.into();
        }
        for (row, role) in self.rows.into_iter().zip(self.roles) {
            ownership
                .register(
                    self.from + rows.len(),
                    Some(role.source),
                    role.anchor,
                    false,
                )
                .expect("prevalidated local featuring carrier");
            rows.push(row);
        }
        self.sources
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        json::{ElementRef, ResolvedModel, dynamic_graph::Outcome, type_relations::TypeRelations},
        model::Model,
    };
    fn fixture(source: &str) -> ResolvedModel {
        let mut m = Model::new();
        m.add_source("local.kerml", source);
        assert!(!m.has_errors());
        ResolvedModel::build(&m)
    }
    fn staging(r: &mut ResolvedModel) -> (Vec<Elem>, Vec<Role>, SemanticOwnership) {
        let plans = super::super::owned_results::plan_reference_results(&mut r.b, &mut 0).unwrap();
        let mut rows = Vec::new();
        let mut roles = Vec::new();
        let mut view = SemanticOwnership::new(r.b.elements.len());
        for plan in plans {
            let start = r.b.elements.len() + rows.len();
            let staged = super::super::owned_results::stage_owned_result(
                &r.b, &mut view, plan, start, &mut rows,
            );
            roles.extend(staged.featuring);
        }
        (rows, roles, view)
    }
    #[test]
    fn constructor_ends_preserve_reference_result_featuring_in_one_transaction() {
        let mut model = Model::with_graph_format(crate::model::GraphFormat::CanonicalV3);
        model.add_library_source("local-bases.kerml", "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}");
        model.add_source("mixed-local.kerml", "feature n; feature read=n; class C {feature a; feature b default=2;} feature made=new C(1);");
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let (mut rows, mut roles, mut view) = staging(&mut r);
        assert_eq!(roles.len(), 3);
        let reserved = rows.iter().map(|row| row.id).collect();
        let defaults =
            super::super::owned_results::plan_constructor_defaults(&mut r.b, &reserved, &mut 0)
                .unwrap();
        assert_eq!(defaults.len(), 1);
        for plan in defaults {
            let start = r.b.elements.len() + rows.len();
            let (_, featuring) = super::super::owned_results::stage_constructor_default(
                &r.b, &mut view, plan, start, &mut rows,
            );
            roles.extend(featuring);
        }
        assert_eq!(roles.len(), 5);
        let constructor_role = roles[3];
        let binding_member = rows[constructor_role.target - r.b.elements.len()]
            .owning_relationship
            .unwrap()
            - r.b.elements.len();
        let original = rows[binding_member].props.clone();
        // A constructor binding is owned by its result, never the expression.
        rows[binding_member].props.insert(
            "owningRelatedElement",
            serde_json::json!({"@id":r.b.elements[constructor_role.anchor].id.to_string()}),
        );
        assert!(matches!(
            prepare(&r.b, &rows, &roles, &mut 0),
            Err(Refusal::Stale)
        ));
        rows[binding_member].props = original;
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(matches!(
            prepare(&r.b, &rows, &roles, &mut exhausted),
            Err(Refusal::WorkLimit)
        ));
        let initial = rows.len();
        let plan = prepare(&r.b, &rows, &roles, &mut 0).unwrap();
        let owners = plan.append(&mut rows, &mut view);
        assert_eq!(owners.len(), 5);
        assert_eq!(rows.len() - initial, 5);
        for (row, role) in rows[initial..].iter().zip(&roles) {
            assert_eq!(row.ty, "TypeFeaturing");
            assert!(ref_is(
                row,
                "featureOfType",
                rows[role.source - r.b.elements.len()].id
            ));
            assert!(ref_is(
                row,
                "featuringType",
                staged(&r.b, &rows, role.target).unwrap().id
            ));
        }
        let call = ElementRef(constructor_role.anchor);
        r.implied_relationships(call);
        let snapshot = r.b.dynamic_graph.as_ref().unwrap();
        assert_eq!(snapshot.local_featuring_outcome, Outcome::Accepted);
        assert_eq!(snapshot.local_featuring.as_ref().unwrap().len(), 5);
    }

    #[test]
    fn local_rows_append_after_every_old_group_and_dynamic_row() {
        let mut r = fixture(
            "function F {in p;return result;} feature n;feature x=n;feature y=n;feature call=F(1);",
        );
        let calls: Vec<_> = r
            .user_elements()
            .filter(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .collect();
        assert_eq!(calls.len(), 2);
        let (old, _, _) = staging(&mut r);
        let call = r
            .user_elements()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .unwrap();
        r.implied_relationships(call);
        let boundary = r.b.implied.as_ref().unwrap().owned_results_from;
        let dynamic = r.b.dynamic_graph.as_ref().unwrap();
        assert_eq!(dynamic.outcome, Outcome::Accepted);
        assert_eq!(dynamic.local_featuring_outcome, Outcome::Accepted);
        let dynamic_len = dynamic.plan.as_ref().unwrap().tail.len();
        let auxiliary = boundary + old.len() + dynamic_len;
        assert_eq!(r.b.elements.len(), auxiliary + 6);
        for (offset, prior) in old.iter().enumerate() {
            let row = &r.b.elements[boundary + offset];
            assert_eq!(row.id, prior.id);
            assert_eq!(row.ty, prior.ty);
            assert_eq!(row.props.to_json(), prior.props.to_json());
            assert_eq!(row.owning_relationship, prior.owning_relationship);
            assert!(
                row.owned_relationships
                    .iter()
                    .copied()
                    .collect::<Vec<_>>()
                    .starts_with(
                        &prior
                            .owned_relationships
                            .iter()
                            .copied()
                            .collect::<Vec<_>>()
                    )
            );
        }
        for row in r.b.elements.iter().skip(auxiliary) {
            assert_eq!(row.ty, "TypeFeaturing");
        }
        for expr in calls {
            let result =
                r.b.semantic_ownership
                    .as_ref()
                    .unwrap()
                    .result(expr.0)
                    .unwrap()
                    .feature;
            assert_eq!(
                TypeRelations::default().featuring_types(&mut r.b, result, &mut 0),
                Some(vec![expr.0])
            );
            assert!(
                !super::super::semantic_ownership::owned_feature_projection_complete(&r.b, expr.0)
            );
        }
        let ids: Vec<_> = r.b.elements.iter().map(|e| e.id).collect();
        r.implied_relationships(call);
        assert_eq!(ids, r.b.elements.iter().map(|e| e.id).collect::<Vec<_>>());
    }
    #[test]
    fn local_admission_survives_dynamic_refusal_and_no_library() {
        let mut r = fixture("feature n;feature x=n;feature bad=Missing();");
        let expr = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        r.implied_relationships(expr);
        let snapshot = r.b.dynamic_graph.as_ref().unwrap();
        assert!(matches!(snapshot.outcome, Outcome::Declined(_)));
        assert_eq!(snapshot.local_featuring_outcome, Outcome::Accepted);
        assert_eq!(snapshot.local_featuring.as_ref().unwrap().len(), 3);
        assert_eq!(
            r.b.elements.len() - r.b.implied.as_ref().unwrap().owned_results_from,
            14
        );
        let result =
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(expr.0)
                .unwrap()
                .feature;
        assert_eq!(
            TypeRelations::default().featuring_types(&mut r.b, result, &mut 0),
            Some(vec![expr.0])
        );
    }
    #[test]
    fn refusal_has_no_private_or_physical_effect_and_can_retry() {
        let mut r = fixture("feature n;feature x=n;");
        let (mut rows, roles, mut view) = staging(&mut r);
        let ids: Vec<_> = rows.iter().map(|e| e.id).collect();
        let before = r.b.elements.len();
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(matches!(
            prepare(&r.b, &rows, &roles, &mut exhausted),
            Err(Refusal::WorkLimit)
        ));
        assert_eq!(ids, rows.iter().map(|e| e.id).collect::<Vec<_>>());
        assert_eq!(before, r.b.elements.len());
        let first = roles[0].source - before;
        let original = rows[first].props.clone();
        rows[first]
            .props
            .insert("isVariable", serde_json::json!(true));
        assert!(matches!(
            prepare(&r.b, &rows, &roles, &mut 0),
            Err(Refusal::Stale)
        ));
        rows[first].props = original;
        let accepted = prepare(&r.b, &rows, &roles, &mut 0)
            .unwrap()
            .append(&mut rows, &mut view);
        assert_eq!(accepted.len(), 3);
        assert_eq!(rows.len(), 14);
        assert_eq!(ids, rows[..11].iter().map(|e| e.id).collect::<Vec<_>>());
    }
    #[test]
    fn auxiliary_collision_keeps_result_binding_and_dynamic_family() {
        let mut r = fixture(
            "function F {return result;} feature spare;feature n;feature x=n;feature call=F();",
        );
        let expr = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        let spare = r.resolve_qualified("spare").unwrap();
        let result = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{}/implied/ownedResult", r.element_id(expr)).as_bytes(),
        );
        let collision = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{result}/implied/TypeFeaturing/{}", r.element_id(expr)).as_bytes(),
        );
        r.override_ids(&std::collections::HashMap::from([(
            r.element_id(spare),
            collision,
        )]));
        r.implied_relationships(expr);
        let snapshot = r.b.dynamic_graph.as_ref().unwrap();
        assert_eq!(snapshot.outcome, Outcome::Accepted);
        assert!(matches!(
            snapshot.local_featuring_outcome,
            Outcome::Declined(Refusal::Collision)
        ));
        assert!(snapshot.local_featuring.is_none());
        assert!(
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(expr.0)
                .is_some()
        );
        assert_eq!(
            r.b.elements
                .iter()
                .filter(|e| e.ty == "BindingConnector")
                .count(),
            1
        );
    }
    #[test]
    fn id_override_preserves_auxiliary_handles_and_metadata_is_not_local_dependency() {
        let mut r = fixture("feature n;feature x=n;");
        let expr = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        r.implied_relationships(expr);
        let result =
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(expr.0)
                .unwrap()
                .feature;
        let rel = r.b.elements[result]
            .owned_relationships
            .iter()
            .copied()
            .find(|&i| r.b.elements[i].ty == "TypeFeaturing")
            .unwrap();
        let id = r.element_id(ElementRef(rel));
        let next = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"explicit local featuring");
        let count = r.b.elements.len();
        r.override_ids(&std::collections::HashMap::from([(id, next)]));
        assert_eq!(r.b.elements.len(), count);
        assert_eq!(r.element_id(ElementRef(rel)), next);
        assert!(r.b.dynamic_graph.as_ref().unwrap().local_current(&r.b));
        let mut held = TypeRelations::default();
        assert_eq!(
            held.featuring_types(&mut r.b, result, &mut 0),
            Some(vec![expr.0])
        );
        r.b.metadata_association_generation = Some(std::sync::Arc::new(()));
        assert!(held.featuring_types(&mut r.b, result, &mut 0).is_none());
        assert_eq!(
            TypeRelations::default().featuring_types(&mut r.b, result, &mut 0),
            Some(vec![expr.0])
        );
        r.b.elements[result]
            .props
            .insert("isVariable", serde_json::json!(true));
        assert!(
            TypeRelations::default()
                .featuring_types(&mut r.b, result, &mut 0)
                .is_none()
        );
        let old = r.element_id(expr);
        r.override_ids(&std::collections::HashMap::from([(
            old,
            Uuid::new_v5(&Uuid::NAMESPACE_OID, b"stale local owner"),
        )]));
        assert!(
            TypeRelations::default()
                .featuring_types(&mut r.b, result, &mut 0)
                .is_none()
        );
        assert_eq!(r.element_id(ElementRef(rel)), next);
    }
    #[test]
    fn auxiliary_work_reuses_uuid_snapshot_without_unrelated_source_scan() {
        let mut work = Vec::new();
        for unrelated in [0, 1000] {
            let mut source = "feature n;feature x=n;".to_string();
            for i in 0..unrelated {
                source.push_str(&format!("feature unused{i};"));
            }
            let mut r = fixture(&source);
            let (rows, roles, _) = staging(&mut r);
            let mut steps = 0;
            prepare(&r.b, &rows, &roles, &mut steps).unwrap();
            work.push(steps);
        }
        assert_eq!(work[0], work[1]);
    }
}
