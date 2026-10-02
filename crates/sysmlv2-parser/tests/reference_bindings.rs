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
fn reference_binding_is_an_owned_binary_connector_over_stored_identities() {
    for (_, mut r) in models(LIBRARY, "feature x=Values::n;") {
        let expression = value(&mut r, "x");
        let referent = r.resolve_qualified("Values::n").unwrap();
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
            let result = one(&mut r, expression, "result").unwrap();
            let members = many(&mut r, expression, "ownedMember");
            let bindings: Vec<_> = members
                .into_iter()
                .filter(|&e| r.element_type(e) == "BindingConnector")
                .collect();
            assert_eq!(bindings.len(), 1);
            let binding = bindings[0];
            assert_eq!(r.owner(binding), Some(expression));
            assert_eq!(
                one(&mut r, binding, "owningType"),
                None,
                "ownedMember does not invent expression featuring for an outer referent"
            );
            assert!(r.element_scope(binding).is_none());
            assert!(r.is_implied(binding), "Connector is also a Relationship");
            match r.derived(binding, "relatedFeature") {
                Derived::Value(sysmlv2_parser::json::DerivedValue::References(ends)) => assert_eq!(
                    ends,
                    vec![
                        sysmlv2_parser::json::Reference::Element(referent),
                        sysmlv2_parser::json::Reference::Element(result)
                    ]
                ),
                other => panic!("{other:?}"),
            }
            let ends = many(&mut r, binding, "connectorEnd");
            assert_eq!(ends.len(), 2);
            for (end, target) in ends.into_iter().zip([referent, result]) {
                assert_eq!(one(&mut r, end, "owningType"), Some(binding));
                let reference = one(&mut r, end, "ownedReferenceSubsetting").unwrap();
                assert_eq!(
                    r.relationship_ends(reference).1,
                    vec![sysmlv2_parser::json::Reference::Element(target)]
                );
                assert!(r.conforms_with_implied(end, target));
            }
            assert_eq!(many(&mut r, expression, "ownedFeature"), vec![result]);
            assert_eq!(
                r.derived_exact(expression, "ownedFeature"),
                Err(sysmlv2_parser::json::PropertyError::Approximate)
            );
        }
    }
}

#[test]
fn binding_node_id_collision_never_publishes_a_partial_expression_subtree() {
    use std::collections::HashMap;
    use uuid::Uuid;
    for collision in 0..8 {
        for (_, mut r) in models("", "feature n; feature victim; feature x=n;") {
            let expression = value(&mut r, "x");
            let n = r.resolve_qualified("n").unwrap();
            let victim = r.resolve_qualified("victim").unwrap();
            let expr_id = r.element_id(expression);
            let result = Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{expr_id}/implied/ownedResult").as_bytes(),
            );
            let binding = Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{expr_id}/implied/referenceBinding").as_bytes(),
            );
            let seed = |s: String| Uuid::new_v5(&Uuid::NAMESPACE_OID, s.as_bytes());
            let end0 = seed(format!("{binding}/implied/end/0"));
            let end1 = seed(format!("{binding}/implied/end/1"));
            let ids = [
                seed(format!("{expr_id}/implied/referenceBindingMembership")),
                binding,
                seed(format!("{binding}/implied/endMembership/0")),
                end0,
                seed(format!(
                    "{end0}/implied/ReferenceSubsetting/{}",
                    r.element_id(n)
                )),
                seed(format!("{binding}/implied/endMembership/1")),
                end1,
                seed(format!("{end1}/implied/ReferenceSubsetting/{result}")),
            ];
            r.override_ids(&HashMap::from([(r.element_id(victim), ids[collision])]));
            assert_eq!(one(&mut r, expression, "result"), None);
            assert!(r.implied_relationships(expression).is_empty());
            assert!(many(&mut r, expression, "ownedMember").is_empty());
        }
    }
}

fn binding(r: &mut ResolvedModel, expression: ElementRef) -> Option<ElementRef> {
    many(r, expression, "ownedMember")
        .into_iter()
        .find(|&e| r.element_type(e) == "BindingConnector")
}

#[test]
fn binding_tail_retargets_atomically_and_survives_bound_identity_remapping() {
    use std::collections::HashMap;
    use uuid::Uuid;
    let target_id = Uuid::parse_str("8cc9369e-e07e-453e-9aaa-79e5014b1885").unwrap();
    for lexical in [false, true] {
        let source = format!(
            "{} feature actual; feature x='{}';",
            if lexical {
                format!("feature '{}';", target_id)
            } else {
                String::new()
            },
            target_id
        );
        for (_, mut r) in models("", &source) {
            let expression = value(&mut r, "x");
            let expression_id = r.element_id(expression);
            let membership = r.owned_relationships(expression)[0];
            let actual = r.resolve_qualified("actual").unwrap();
            let original = binding(&mut r, expression);
            assert_eq!(original.is_some(), lexical);
            let old_reference_id = original.map(|connector| {
                let end = many(&mut r, connector, "connectorEnd")[0];
                let reference = one(&mut r, end, "ownedReferenceSubsetting").unwrap();
                r.element_id(reference)
            });
            r.override_ids(&HashMap::from([(r.element_id(actual), target_id)]));
            let mut hints = HashMap::from([(
                (r.element_id(membership), "memberElement".into()),
                target_id,
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&target_id)
            );
            let connector = binding(&mut r, expression).unwrap();
            let result = one(&mut r, expression, "result").unwrap();
            assert_eq!(
                r.relationship_ends(connector),
                (
                    vec![sysmlv2_parser::json::Reference::Element(actual)],
                    vec![sysmlv2_parser::json::Reference::Element(result)]
                )
            );
            if let Some(old) = old_reference_id {
                assert!(r.element_by_id(&old.to_string()).is_none());
            }
            let connector_id = r.element_id(connector);
            let result_id = r.element_id(result);
            r.bind_id_spelled_references_with(&mut hints);
            let current = binding(&mut r, expression).unwrap();
            assert_eq!(r.element_id(current), connector_id);
            let current_result = one(&mut r, expression, "result").unwrap();
            assert_eq!(r.element_id(current_result), result_id);
            // ID override remaps an already bound target; a repeated bind
            // has no pending site and must preserve the generated handles.
            let moved = Uuid::parse_str("bef446bc-013e-4a7d-ad44-0545804ab972").unwrap();
            r.override_ids(&HashMap::from([(target_id, moved)]));
            let mut stale_hint = HashMap::from([(
                (r.element_id(membership), "memberElement".into()),
                target_id,
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut stale_hint)
                    .is_empty()
            );
            assert_eq!(binding(&mut r, expression), Some(current));
            assert_eq!(one(&mut r, expression, "result"), Some(current_result));
            assert_eq!(
                r.relationship_ends(current),
                (
                    vec![sysmlv2_parser::json::Reference::Element(actual)],
                    vec![sysmlv2_parser::json::Reference::Element(current_result)]
                )
            );
            let end = many(&mut r, current, "connectorEnd")[0];
            let reference = one(&mut r, end, "ownedReferenceSubsetting").unwrap();
            assert_eq!(
                r.element_properties(reference)["referencedFeature"],
                serde_json::json!({"@id": moved.to_string()})
            );
            assert_eq!(r.element_id(expression), expression_id);
            assert_eq!(r.element_id(actual), moved);
        }
    }
}

#[test]
fn pending_identity_binding_loss_discards_both_result_and_binding() {
    use std::collections::HashMap;
    use uuid::Uuid;
    let target_id = Uuid::parse_str("79c36d19-0f87-4e62-9b15-25b6d331d355").unwrap();
    let source = format!("feature '{target_id}'; class wrongKind; feature x='{target_id}';");
    for wrong_kind in [false, true] {
        for (_, mut r) in models("", &source) {
            let expression = value(&mut r, "x");
            let expression_id = r.element_id(expression);
            let membership = r.owned_relationships(expression)[0];
            let old_binding = binding(&mut r, expression).unwrap();
            let old_binding_id = r.element_id(old_binding);
            let old_result = one(&mut r, expression, "result").unwrap();
            let old_result_id = r.element_id(old_result);
            if wrong_kind {
                let target = r.resolve_qualified("wrongKind").unwrap();
                r.override_ids(&HashMap::from([(r.element_id(target), target_id)]));
            }
            let mut hints = HashMap::from([(
                (r.element_id(membership), "memberElement".into()),
                target_id,
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&target_id)
            );
            assert_eq!(binding(&mut r, expression), None);
            assert_eq!(one(&mut r, expression, "result"), None);
            assert!(r.element_by_id(&old_binding_id.to_string()).is_none());
            assert!(r.element_by_id(&old_result_id.to_string()).is_none());
            assert_eq!(r.element_id(expression), expression_id);
        }
    }
}

#[test]
fn full_binding_subtrees_have_consistent_generic_endpoints_and_lift_away_atomically() {
    use std::collections::HashSet;
    use sysmlv2_parser::{
        full::{EmissionPolicy, UnresolvedReferencePolicy, resolved_to_full_json},
        json::model_to_compact_json,
        lift::from_compact_json_with_names,
        print::print_source,
    };
    for (model, mut r) in models(LIBRARY, "feature x=Values::n;") {
        let compact = model_to_compact_json(&model);
        let compact_ids: HashSet<_> = compact
            .as_array()
            .unwrap()
            .iter()
            .map(|row| row["@id"].as_str().unwrap())
            .collect();
        let names = sysmlv2_parser::json::library_element_name_map(&model);
        let compact_lift = from_compact_json_with_names(&compact, &names).unwrap();
        assert!(
            compact_lift.errors.is_empty(),
            "compact baseline lift: {:?}",
            compact_lift.errors
        );
        let source = print_source(&compact_lift.unit);
        let expression = value(&mut r, "x");
        for policy in [
            ClosurePolicy::Passthrough,
            ClosurePolicy::Closure {
                include_implied: false,
            },
            ClosurePolicy::Closure {
                include_implied: true,
            },
        ] {
            let full = resolved_to_full_json(
                &mut r,
                &model,
                EmissionPolicy {
                    unresolved: UnresolvedReferencePolicy::Reject,
                    closures: policy,
                },
            )
            .unwrap();
            let connector = binding(&mut r, expression).unwrap();
            let result = one(&mut r, expression, "result").unwrap();
            let target = r.resolve_qualified("Values::n").unwrap();
            let rows = full.as_array().unwrap();
            assert_eq!(rows.len(), compact_ids.len() + 14);
            let generated: Vec<_> = rows
                .iter()
                .filter(|row| !compact_ids.contains(row["@id"].as_str().unwrap()))
                .collect();
            assert_eq!(generated.len(), 14);
            let unique: HashSet<_> = generated
                .iter()
                .map(|row| row["@id"].as_str().unwrap())
                .collect();
            assert_eq!(unique.len(), 14);
            let featuring: Vec<_> = generated
                .iter()
                .filter(|row| row["@type"] == "TypeFeaturing")
                .collect();
            assert_eq!(featuring.len(), 3);
            let ends = many(&mut r, connector, "connectorEnd");
            assert_eq!(ends.len(), 2);
            let sources = std::iter::once((result, expression))
                .chain(ends.into_iter().map(|end| (end, connector)));
            for (source, target) in sources {
                let relationship = featuring
                    .iter()
                    .find(|row| row["featureOfType"]["@id"] == r.element_id(source).to_string())
                    .unwrap();
                assert_eq!(
                    relationship["owningRelatedElement"],
                    relationship["featureOfType"]
                );
                assert_eq!(
                    relationship["owningFeatureOfType"],
                    relationship["featureOfType"]
                );
                assert_eq!(
                    relationship["featuringType"]["@id"],
                    r.element_id(target).to_string()
                );
                assert_eq!(
                    relationship["source"],
                    serde_json::json!([relationship["featureOfType"]])
                );
                assert_eq!(
                    relationship["target"],
                    serde_json::json!([relationship["featuringType"]])
                );
            }
            let row = rows
                .iter()
                .find(|row| row["@id"] == r.element_id(connector).to_string())
                .unwrap();
            assert_eq!(
                row["source"],
                serde_json::json!([{"@id":r.element_id(target).to_string()}])
            );
            assert_eq!(
                row["target"],
                serde_json::json!([{"@id":r.element_id(result).to_string()}])
            );
            assert_eq!(
                row["relatedElement"],
                serde_json::json!([{"@id":r.element_id(target).to_string()},{"@id":r.element_id(result).to_string()}])
            );
            assert_eq!(row["relatedFeature"], row["relatedElement"]);
            assert_eq!(
                row["owningRelatedElement"],
                serde_json::Value::Null,
                "binding is owned through its membership, not as a direct relationship"
            );
            assert_eq!(r.owner(connector), Some(expression));
            let full_lift = from_compact_json_with_names(&full, &names).unwrap();
            assert!(
                full_lift.errors.is_empty(),
                "full lift: {:?}",
                full_lift.errors
            );
            assert_eq!(print_source(&full_lift.unit), source);
            assert_eq!(model_to_compact_json(&model), compact);
        }
    }
}

#[test]
fn generated_binding_does_not_change_sysml_lift_dialect() {
    use sysmlv2_parser::{
        ast::Dialect, full::model_to_full_json, json::model_to_compact_json,
        lift::from_compact_json, print::print_source,
    };
    for (model, _) in models_named(
        "",
        "part def Container { attribute n; attribute x=n; }",
        "reference.sysml",
    ) {
        let compact = from_compact_json(&model_to_compact_json(&model)).unwrap();
        let full = model_to_full_json(&model);
        assert!(
            full.as_array()
                .unwrap()
                .iter()
                .any(|row| { row["@type"] == "BindingConnector" && row["isImplied"] == true })
        );
        let lifted = from_compact_json(&full).unwrap();
        assert!(compact.errors.is_empty(), "{:?}", compact.errors);
        assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
        assert_eq!(lifted.unit.dialect, Dialect::Sysml);
        assert_eq!(print_source(&lifted.unit), print_source(&compact.unit));
    }
}
