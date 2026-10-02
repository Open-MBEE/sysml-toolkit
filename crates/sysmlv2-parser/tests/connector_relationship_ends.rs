#![cfg(feature = "json")]

use std::sync::Arc;
use sysmlv2_parser::{
    full::{EmissionPolicy, UnresolvedReferencePolicy, resolved_to_full_json},
    json::{
        ClosurePolicy, Derived, DerivedValue, ElementRef, Reference, ResolvedModel,
        model_to_compact_json,
    },
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};

fn models(source: &str) -> Vec<(Model, ResolvedModel)> {
    let mut library = Model::new();
    library.add_library_source(
        "connector-library.kerml",
        "package L {feature a; feature b;}",
    );
    library.record_library_cache();
    ResolvedModel::build(&library);
    let cache =
        LibraryCache::from_bytes(&library.take_recorded_library_cache().unwrap().to_bytes())
            .unwrap();
    let prepared = library.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(37).unwrap(), 37).unwrap());
    (0..4)
        .map(|mode| {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source(
                        "connector-library.kerml",
                        "package L {feature a; feature b;}",
                    );
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            assert!(
                model
                    .add_source("connectors.sysml", source)
                    .diagnostics
                    .is_empty()
            );
            let resolved = ResolvedModel::build(&model);
            (model, resolved)
        })
        .collect()
}

fn refs(r: &mut ResolvedModel, e: ElementRef, property: &str) -> Vec<Reference> {
    match r.derived(e, property) {
        Derived::Value(DerivedValue::References(values)) => values,
        Derived::Value(DerivedValue::Reference(value)) => vec![value],
        Derived::Value(DerivedValue::Null) => vec![],
        other => panic!("{property}: {other:?}"),
    }
}

fn policies() -> [ClosurePolicy; 3] {
    [
        ClosurePolicy::Passthrough,
        ClosurePolicy::Closure {
            include_implied: false,
        },
        ClosurePolicy::Closure {
            include_implied: true,
        },
    ]
}

#[test]
fn connector_generic_ends_agree_with_typed_projections_and_keep_repeated_related_features() {
    let source = "package P {
        part a; part b;
        connection empty;
        connection single {end one ::> a;}
        connection binary connect a to b;
        connection reflexive connect a to a;
        connection ternary connect (a,b,a);
        connection repeated connect (a,b,b);
        connection imported connect L::a to L::b;
    }";
    for (model, mut r) in models(source) {
        let loaded = model.loaded_library_unit_count();
        let compact = model_to_compact_json(&model);
        let a = Reference::Element(r.resolve_qualified("P::a").unwrap());
        let b = Reference::Element(r.resolve_qualified("P::b").unwrap());
        let la = Reference::Element(r.resolve_qualified("L::a").unwrap());
        let lb = Reference::Element(r.resolve_qualified("L::b").unwrap());
        let cases = [
            ("empty", vec![], vec![]),
            ("single", vec![a.clone()], vec![]),
            ("binary", vec![a.clone(), b.clone()], vec![b.clone()]),
            ("reflexive", vec![a.clone(), a.clone()], vec![a.clone()]),
            (
                "ternary",
                vec![a.clone(), b.clone(), a.clone()],
                vec![b.clone(), a.clone()],
            ),
            (
                "repeated",
                vec![a.clone(), b.clone(), b.clone()],
                vec![b.clone()],
            ),
            ("imported", vec![la.clone(), lb.clone()], vec![lb.clone()]),
        ];
        for policy in policies() {
            r.set_closure_policy(policy);
            for (name, related, targets) in &cases {
                let e = r.resolve_qualified(&format!("P::{name}")).unwrap();
                let sources: Vec<_> = related.first().cloned().into_iter().collect();
                assert_eq!(
                    r.relationship_ends(e),
                    (sources.clone(), targets.clone()),
                    "{name}/{policy:?}"
                );
                assert_eq!(refs(&mut r, e, "sourceFeature"), sources);
                assert_eq!(refs(&mut r, e, "targetFeature"), *targets);
                assert_eq!(refs(&mut r, e, "relatedFeature"), *related);
                assert_eq!(refs(&mut r, e, "relatedElement"), *related);
                assert_eq!(
                    r.derived_exact(e, "relatedElement"),
                    Err(sysmlv2_parser::json::PropertyError::Approximate),
                    "generic alias cannot certify more than relatedFeature"
                );
            }
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
            for (name, related, targets) in &cases {
                let e = r.resolve_qualified(&format!("P::{name}")).unwrap();
                let row = rows
                    .iter()
                    .find(|row| row["@id"] == r.element_id(e).to_string())
                    .unwrap();
                let json_refs = |values: &[Reference]| {
                    serde_json::Value::Array(
                        values
                            .iter()
                            .map(|value| {
                                let Reference::Element(element) = value else {
                                    panic!("in-model fixture")
                                };
                                serde_json::json!({"@id":r.element_id(*element).to_string()})
                            })
                            .collect(),
                    )
                };
                assert_eq!(row["source"], json_refs(&related[..related.len().min(1)]));
                assert_eq!(row["target"], json_refs(targets));
                assert_eq!(row["relatedElement"], json_refs(related));
                assert_eq!(row["relatedFeature"], json_refs(related));
                assert_eq!(row["targetFeature"], json_refs(targets));
            }
        }
        assert_eq!(model_to_compact_json(&model), compact);
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}

#[test]
fn connector_generic_ends_follow_the_existing_inherited_end_policy() {
    for (_, mut r) in models(
        "package P {part a; part b; connection base connect a to b; connection child :> base;}",
    ) {
        let child = r.resolve_qualified("P::child").unwrap();
        let a = Reference::Element(r.resolve_qualified("P::a").unwrap());
        let b = Reference::Element(r.resolve_qualified("P::b").unwrap());
        for policy in policies() {
            r.set_closure_policy(policy);
            let expected = if policy == ClosurePolicy::Passthrough {
                vec![]
            } else {
                vec![a.clone(), b.clone()]
            };
            assert_eq!(refs(&mut r, child, "relatedElement"), expected);
            assert_eq!(
                r.derived_exact(child, "relatedElement"),
                Err(sysmlv2_parser::json::PropertyError::Approximate)
            );
            assert_eq!(
                r.relationship_ends(child),
                (
                    expected.first().cloned().into_iter().collect(),
                    expected.into_iter().skip(1).collect()
                )
            );
        }
    }
}

#[test]
fn connector_generic_ends_preserve_unresolved_reference_identity() {
    for (model, mut r) in models(
        "package P {part a; connection missing connect a to Absent; connection repeated connect (Absent,Absent,Absent);}",
    ) {
        for policy in policies() {
            r.set_closure_policy(policy);
            let e = r.resolve_qualified("P::missing").unwrap();
            let a = Reference::Element(r.resolve_qualified("P::a").unwrap());
            let missing = Reference::Unresolved("Absent".into());
            assert_eq!(
                r.derived_exact(e, "relatedElement"),
                Err(sysmlv2_parser::json::PropertyError::Approximate)
            );
            assert_eq!(
                r.relationship_ends(e),
                (vec![a.clone()], vec![missing.clone()])
            );
            assert_eq!(refs(&mut r, e, "relatedElement"), vec![a, missing.clone()]);
            let repeated = r.resolve_qualified("P::repeated").unwrap();
            assert_eq!(
                r.relationship_ends(repeated),
                (vec![missing.clone()], vec![missing.clone()])
            );
            assert_eq!(
                refs(&mut r, repeated, "relatedElement"),
                vec![missing.clone(), missing.clone(), missing]
            );
            let full = resolved_to_full_json(
                &mut r,
                &model,
                EmissionPolicy {
                    unresolved: UnresolvedReferencePolicy::LegacyDanglingId,
                    closures: policy,
                },
            )
            .unwrap();
            let row = full
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["@id"] == r.element_id(repeated).to_string())
                .unwrap();
            let target = row["relatedFeature"][0].clone();
            assert_eq!(row["source"], serde_json::json!([target.clone()]));
            assert_eq!(row["target"], serde_json::json!([target.clone()]));
            assert_eq!(
                row["relatedElement"],
                serde_json::json!([target.clone(), target.clone(), target])
            );
        }
    }
}

#[test]
fn payload_endpoint_completion_preserves_supplied_owned_values() {
    use std::collections::HashMap;
    use sysmlv2_parser::full::from_compact_value;
    let mut model = Model::new();
    assert!(
        model
            .add_source(
                "payload.sysml",
                "part a; part b; connection c connect (a,b,b);"
            )
            .diagnostics
            .is_empty()
    );
    let mut resolved = ResolvedModel::build(&model);
    let connector = resolved.resolve_qualified("c").unwrap();
    let connector_id = resolved.element_id(connector).to_string();
    let b = resolved.resolve_qualified("b").unwrap();
    let compact = model_to_compact_json(&model);
    let full = from_compact_value(compact.clone(), &HashMap::new(), true);
    let by_id =
        |value: &serde_json::Value| -> std::collections::BTreeMap<String, serde_json::Value> {
            value
                .as_array()
                .unwrap()
                .iter()
                .map(|row| (row["@id"].as_str().unwrap().to_owned(), row.clone()))
                .collect()
        };
    let expected = by_id(&full);
    assert_eq!(
        by_id(&from_compact_value(full.clone(), &HashMap::new(), true)),
        expected
    );
    let mut missing = full;
    let row = missing
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|row| row["@id"] == connector_id)
        .unwrap()
        .as_object_mut()
        .unwrap();
    row.remove("source");
    row.remove("target");
    assert_eq!(
        by_id(&from_compact_value(missing, &HashMap::new(), true)),
        expected
    );

    let mut supplied = compact;
    let row = supplied
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|row| row["@id"] == connector_id)
        .unwrap();
    let source = serde_json::json!([{"@id":resolved.element_id(b).to_string()}]);
    row["source"] = source.clone();
    row["target"] = serde_json::json!([]);
    let result = by_id(&from_compact_value(supplied, &HashMap::new(), true));
    assert_eq!(result[&connector_id]["source"], source);
    assert_eq!(result[&connector_id]["target"], serde_json::json!([]));
}

#[test]
fn unrelated_relationship_fidelity_is_unchanged() {
    use sysmlv2_parser::json::{Derives, derives_under};
    for policy in policies() {
        assert_eq!(
            derives_under("Subsetting", "relatedElement", policy),
            Derives::Exact
        );
        assert_eq!(
            derives_under("Membership", "relatedElement", policy),
            Derives::Exact
        );
        assert_eq!(
            derives_under("ConnectionUsage", "relatedElement", policy),
            Derives::Passthrough
        );
        assert_eq!(
            derives_under("BindingConnector", "relatedElement", policy),
            Derives::Passthrough
        );
    }
}
