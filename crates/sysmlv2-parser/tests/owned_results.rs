#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, ElementRef, ResolvedModel},
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};
fn models(library: &str, user: &str) -> Vec<(Model, ResolvedModel)> {
    models_named(library, user, "calls.kerml")
}
fn models_named(library: &str, user: &str, user_name: &str) -> Vec<(Model, ResolvedModel)> {
    let mut base = Model::new();
    assert!(
        base.add_library_source("functions.kerml", library)
            .diagnostics
            .is_empty()
    );
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(71).unwrap(), 71).unwrap());
    (0..4)
        .map(|mode| {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("functions.kerml", library);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            assert!(model.add_source(user_name, user).diagnostics.is_empty());
            let resolved = ResolvedModel::build(&model);
            (model, resolved)
        })
        .collect()
}

const LIBRARY: &str = "standard library package Values { datatype Integer; feature n:Integer[2]; alias a for n; feature libraryReference=n; }";
fn value(r: &mut ResolvedModel, name: &str) -> ElementRef {
    let owner = r.resolve_qualified(name).unwrap();
    let rel = r
        .owned_relationships(owner)
        .into_iter()
        .find(|&e| r.element_type(e) == "FeatureValue")
        .unwrap();
    one(r, rel, "value").unwrap()
}
fn one(r: &mut ResolvedModel, e: ElementRef, p: &str) -> Option<ElementRef> {
    match r.derived(e, p) {
        Derived::Value(v) => v.element(),
        v => panic!("{p}: {v:?}"),
    }
}
fn many(r: &mut ResolvedModel, e: ElementRef, p: &str) -> Vec<ElementRef> {
    match r.derived(e, p) {
        Derived::Value(sysmlv2_parser::json::DerivedValue::Elements(v)) => v,
        v => panic!("{p}: {v:?}"),
    }
}

#[test]
fn reference_owned_results_share_identity_projections_under_every_closure_policy() {
    for materialize_first in [false, true] {
        for (model, mut r) in models(LIBRARY, "feature x=Values::n; feature y=Values::a;") {
            let loaded = model.loaded_library_unit_count();
            let before: Vec<_> = r
                .elements()
                .map(|e| {
                    (
                        r.element_id(e),
                        r.element_properties(e),
                        r.owned_relationships(e),
                    )
                })
                .collect();
            let n = r.resolve_qualified("Values::n").unwrap();
            let integer = r.resolve_qualified("Values::Integer").unwrap();
            let mut identities = std::collections::HashMap::new();
            for policy in [
                ClosurePolicy::Passthrough,
                ClosurePolicy::Closure {
                    include_implied: false,
                },
                ClosurePolicy::Closure {
                    include_implied: true,
                },
            ] {
                r.set_closure_policy(policy);
                for name in ["x", "y", "Values::libraryReference"] {
                    let expression = value(&mut r, name);
                    assert_eq!(r.element_type(expression), "FeatureReferenceExpression");
                    let source_members = r.owned_relationships(expression);
                    assert_eq!(source_members.len(), 1);
                    if materialize_first {
                        r.implied_relationships(expression);
                    }
                    let result = one(&mut r, expression, "result")
                        .expect("admitted reference owns its result");
                    if let Some(previous) = identities.insert(expression, r.element_id(result)) {
                        assert_eq!(previous, r.element_id(result));
                    }
                    let member = one(&mut r, result, "owningMembership").unwrap();
                    assert_eq!(r.element_type(member), "ReturnParameterMembership");
                    assert!(r.is_implied(member));
                    assert!(!r.is_implied(result));
                    assert!(r.element_scope(result).is_none());
                    assert_eq!(
                        r.is_library_element(result),
                        r.is_library_element(expression)
                    );
                    assert_eq!(r.owner(result), Some(expression));
                    assert_eq!(r.owner(member), Some(expression));
                    assert_eq!(one(&mut r, member, "owningType"), Some(expression));
                    assert_eq!(one(&mut r, result, "owningType"), Some(expression));
                    assert_eq!(one(&mut r, expression, "referent"), Some(n));
                    assert_eq!(
                        many(&mut r, expression, "ownedFeatureMembership"),
                        vec![member]
                    );
                    assert_eq!(many(&mut r, expression, "ownedFeature"), vec![result]);
                    let owned_members = many(&mut r, expression, "ownedMember");
                    assert_eq!(owned_members.len(), 2);
                    assert_eq!(owned_members[0], result);
                    assert_eq!(r.element_type(owned_members[1]), "BindingConnector");
                    assert_eq!(many(&mut r, expression, "ownedElement"), owned_members);
                    for property in [
                        "ownedElement",
                        "ownedMember",
                        "ownedFeature",
                        "ownedFeatureMembership",
                        "ownedMembership",
                    ] {
                        assert_eq!(
                            r.derived_exact(expression, property),
                            Err(sysmlv2_parser::json::PropertyError::Approximate),
                            "required library ancestry and the remaining expression rules stay qualified"
                        );
                    }

                    let implied = r.implied_relationships(expression);
                    let relationships: Vec<_> = source_members
                        .iter()
                        .copied()
                        .chain(implied)
                        .map(|e| serde_json::json!({"@id": r.element_id(e).to_string()}))
                        .collect();
                    assert_eq!(
                        r.property(expression, "ownedRelationship"),
                        Ok(serde_json::json!(relationships)),
                        "structural inventory includes authored and published relationships"
                    );
                    assert_eq!(
                        r.property(expression, "isImpliedIncluded"),
                        Err(sysmlv2_parser::json::PropertyError::Approximate),
                        "listing published relationships does not certify every implied family"
                    );

                    assert!(
                        r.owned_members(expression).is_empty(),
                        "source navigation stays explicit"
                    );
                    assert_eq!(r.owned_relationships(expression), source_members);
                    let subsets = many(&mut r, result, "ownedSubsetting");
                    assert_eq!(subsets.len(), 1);
                    assert_eq!(
                        r.relationship_ends(subsets[0]),
                        (
                            vec![sysmlv2_parser::json::Reference::Element(result)],
                            vec![sysmlv2_parser::json::Reference::Element(n)]
                        )
                    );
                    assert!(r.conforms_with_implied(result, n));
                    match r.derived(result, "type") {
                        Derived::Value(sysmlv2_parser::json::DerivedValue::References(v)) => {
                            assert!(v.contains(&sysmlv2_parser::json::Reference::Element(integer)))
                        }
                        v => panic!("{v:?}"),
                    };
                }
            }
            assert_eq!(
                before,
                r.elements()
                    .map(|e| (
                        r.element_id(e),
                        r.element_properties(e),
                        r.owned_relationships(e)
                    ))
                    .collect::<Vec<_>>()
            );
            assert_eq!(loaded, model.loaded_library_unit_count());
        }
    }
}

#[test]
fn full_reference_subtrees_are_reciprocal_and_lift_to_the_original_source_graph() {
    use sysmlv2_parser::{
        full::{EmissionPolicy, UnresolvedReferencePolicy, resolved_to_full_json},
        json::model_to_compact_json,
        lift::{from_compact_json, from_compact_json_with_names},
        print::print_source,
    };
    for (model, mut r) in models(LIBRARY, "feature x=Values::a;") {
        let compact = model_to_compact_json(&model);
        let names = sysmlv2_parser::json::library_element_name_map(&model);
        let compact_lifted = from_compact_json_with_names(&compact, &names).unwrap();
        assert!(
            compact_lifted.errors.is_empty(),
            "{:?}",
            compact_lifted.errors
        );
        let expected = print_source(&compact_lifted.unit);
        for policy in [
            ClosurePolicy::Passthrough,
            ClosurePolicy::Closure {
                include_implied: false,
            },
            ClosurePolicy::Closure {
                include_implied: true,
            },
        ] {
            let expression = value(&mut r, "x");
            let result = one(&mut r, expression, "result").unwrap();
            let membership = one(&mut r, result, "owningMembership").unwrap();
            let subset = many(&mut r, result, "ownedSubsetting")[0];
            let full = resolved_to_full_json(
                &mut r,
                &model,
                EmissionPolicy {
                    unresolved: UnresolvedReferencePolicy::Reject,
                    closures: policy,
                },
            )
            .unwrap();
            let rows = full.as_array().unwrap();
            for element in [membership, result, subset] {
                assert_eq!(
                    rows.iter()
                        .filter(|row| row["@id"] == r.element_id(element).to_string())
                        .count(),
                    1
                );
            }
            let result_row = rows
                .iter()
                .find(|row| row["@id"] == r.element_id(result).to_string())
                .unwrap();
            assert_eq!(result_row["@type"], "Feature");
            assert!(result_row.get("isImplied").is_none());
            assert_eq!(
                result_row["owningRelationship"]["@id"],
                r.element_id(membership).to_string()
            );
            let member_row = rows
                .iter()
                .find(|row| row["@id"] == r.element_id(membership).to_string())
                .unwrap();
            assert_eq!(
                member_row["ownedRelatedElement"],
                serde_json::json!([{"@id":r.element_id(result).to_string()}])
            );
            assert_eq!(
                member_row["owningRelatedElement"]["@id"],
                r.element_id(expression).to_string()
            );
            let lifted = from_compact_json_with_names(&full, &names).unwrap();
            assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
            assert_eq!(print_source(&lifted.unit), expected);
            assert_eq!(model_to_compact_json(&model), compact);
        }
        assert!(from_compact_json(&compact).is_ok());
    }
}

#[test]
fn missing_or_non_feature_referents_do_not_get_fabricated_owned_results() {
    for (_, mut r) in models("class A;", "feature missing=Absent; feature classRef=A;") {
        for name in ["missing", "classRef"] {
            let expression = value(&mut r, name);
            assert_eq!(one(&mut r, expression, "result"), None);
            assert!(many(&mut r, expression, "ownedFeatureMembership").is_empty());
        }
    }
}

#[test]
fn predicted_generated_identity_collision_refuses_the_whole_subtree() {
    use std::collections::HashMap;
    use uuid::Uuid;
    for collision in 0..3 {
        for (_, mut r) in models("feature n; feature occupant;", "feature x=n;") {
            let expression = value(&mut r, "x");
            let referent = r.resolve_qualified("n").unwrap();
            let occupant = r.resolve_qualified("occupant").unwrap();
            let expression_id = r.element_id(expression);
            let result_id = Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{expression_id}/implied/ownedResult").as_bytes(),
            );
            let membership_id = Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{expression_id}/implied/returnMembership").as_bytes(),
            );
            let subset_id = Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{result_id}/implied/Subsetting/{}", r.element_id(referent)).as_bytes(),
            );
            let collision_id = [membership_id, result_id, subset_id][collision];
            assert!(r.element_by_id(&collision_id.to_string()).is_none());
            r.override_ids(&HashMap::from([(r.element_id(occupant), collision_id)]));
            let before: Vec<_> = r.elements().map(|e| r.element_id(e)).collect();
            assert_eq!(
                before
                    .iter()
                    .collect::<std::collections::HashSet<_>>()
                    .len(),
                before.len()
            );
            assert_eq!(one(&mut r, expression, "result"), None);
            assert!(r.implied_relationships(expression).is_empty());
            assert_eq!(r.element_by_id(&collision_id.to_string()), Some(occupant));
            for (index, id) in [membership_id, result_id, subset_id]
                .into_iter()
                .enumerate()
            {
                if index != collision {
                    assert!(
                        r.element_by_id(&id.to_string()).is_none(),
                        "no orphan generated rows"
                    );
                }
            }
            assert_eq!(
                before,
                r.elements().map(|e| r.element_id(e)).collect::<Vec<_>>()
            );
        }
    }
}

#[test]
fn source_identity_binding_rebuilds_reference_results_including_an_empty_plan() {
    use std::collections::HashMap;
    use uuid::Uuid;
    let target_id = Uuid::parse_str("a280c39c-62f7-4c26-9793-fcdd9d5ad340").unwrap();
    for lexical_exists in [false, true] {
        let source = format!(
            "{} feature actual; feature x='{}';",
            if lexical_exists {
                format!("feature '{}';", target_id)
            } else {
                String::new()
            },
            target_id
        );
        for (_, mut r) in models("", &source) {
            let expression = value(&mut r, "x");
            let actual = r.resolve_qualified("actual").unwrap();
            let membership = r.owned_relationships(expression)[0];
            let old_referent = one(&mut r, expression, "referent");
            let old_result = one(&mut r, expression, "result");
            assert_eq!(old_result.is_some(), lexical_exists);
            // Capture IDs only: generated handles must be reacquired after the
            // following source-identity binding mutation.
            let old_subset_id = old_result.map(|result| {
                let subset = many(&mut r, result, "ownedSubsetting")[0];
                r.element_id(subset)
            });
            r.override_ids(&HashMap::from([(r.element_id(actual), target_id)]));
            let mut hints = HashMap::from([(
                (r.element_id(membership), "memberElement".to_owned()),
                target_id,
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&target_id)
            );
            assert_eq!(one(&mut r, expression, "referent"), Some(actual));
            let result = one(&mut r, expression, "result").unwrap();
            let subset = many(&mut r, result, "ownedSubsetting")[0];
            let ends = r.relationship_ends(subset);
            assert_eq!(
                ends.1,
                vec![sysmlv2_parser::json::Reference::Element(actual)]
            );
            if let Some(old) = old_subset_id {
                assert!(r.element_by_id(&old.to_string()).is_none());
            }
            if let Some(old) = old_referent {
                assert!(!r.conforms_with_implied(result, old));
            }
            let result_id = r.element_id(result);
            let subset_id = r.element_id(subset);
            r.bind_id_spelled_references_with(&mut hints);
            let reacquired = one(&mut r, expression, "result").unwrap();
            let reacquired_subset = many(&mut r, reacquired, "ownedSubsetting")[0];
            assert_eq!(r.element_id(reacquired), result_id);
            assert_eq!(r.element_id(reacquired_subset), subset_id);
        }
    }
}

#[test]
fn rebinding_loss_keeps_source_and_generic_implied_handles_stable() {
    use std::collections::HashMap;
    use uuid::Uuid;
    let target_id = Uuid::parse_str("6893e10d-a292-4725-8295-a4656f0f5b23").unwrap();
    let library = "standard library package Performances {function Evaluation; function Marker;}";
    for target_in_model in [false, true] {
        let source = format!(
            "feature '{}'; class wrongKind; feature x='{}';",
            target_id, target_id
        );
        for (_, mut r) in models(library, &source) {
            let expression = value(&mut r, "x");
            let expression_id = r.element_id(expression);
            let membership = r.owned_relationships(expression)[0];
            let old_result = one(&mut r, expression, "result").unwrap();
            let old_result_id = r.element_id(old_result);
            let marker = r.resolve_qualified("Performances::Marker").unwrap();
            let generic = r.implied_relationships(marker);
            assert_eq!(generic.len(), 1);
            let generic_ids: Vec<_> = generic.iter().map(|&e| r.element_id(e)).collect();
            if target_in_model {
                let wrong = r.resolve_qualified("wrongKind").unwrap();
                r.override_ids(&HashMap::from([(r.element_id(wrong), target_id)]));
            }
            let mut hints = HashMap::from([(
                (r.element_id(membership), "memberElement".to_owned()),
                target_id,
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&target_id)
            );
            assert_eq!(r.element_id(expression), expression_id);
            assert_eq!(r.implied_relationships(marker), generic);
            assert_eq!(
                generic.iter().map(|&e| r.element_id(e)).collect::<Vec<_>>(),
                generic_ids
            );
            assert_eq!(one(&mut r, expression, "result"), None);
            assert!(r.element_by_id(&old_result_id.to_string()).is_none());
            assert_eq!(
                r.derived_exact(expression, "ownedFeature"),
                Err(sysmlv2_parser::json::PropertyError::Approximate)
            );
            assert!(r.implied_relationships(expression).is_empty());
        }
    }
}

#[test]
fn standard_library_referent_keeps_result_identity_type_and_qualified_family_status() {
    let library = sysmlv2_testkit::library_dir();
    if !library.exists() {
        eprintln!("skipping: library not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&library).expect("library loads");
    assert!(
        model
            .add_source("reference-use.kerml", "feature x=Base::naturals;")
            .diagnostics
            .is_empty()
    );
    let mut r = ResolvedModel::build(&model);
    let expression = value(&mut r, "x");
    let referent = r.resolve_qualified("Base::naturals").unwrap();
    let natural = r.resolve_qualified("ScalarValues::Natural").unwrap();
    let original_id = r.element_id(expression);
    for policy in [
        ClosurePolicy::Passthrough,
        ClosurePolicy::Closure {
            include_implied: false,
        },
        ClosurePolicy::Closure {
            include_implied: true,
        },
    ] {
        r.set_closure_policy(policy);
        let result =
            one(&mut r, expression, "result").expect("stored canonical referent admits a result");
        assert_eq!(r.element_id(expression), original_id);
        assert_eq!(r.owner(result), Some(expression));
        assert!(r.element_scope(result).is_none());
        assert!(r.conforms_with_implied(result, referent));
        match r.derived(result, "type") {
            Derived::Value(sysmlv2_parser::json::DerivedValue::References(types)) => {
                assert!(types.contains(&sysmlv2_parser::json::Reference::Element(natural)))
            }
            other => panic!("{other:?}"),
        }
        assert_eq!(
            r.derived_exact(expression, "ownedFeature"),
            Err(sysmlv2_parser::json::PropertyError::Approximate)
        );
    }
}
