#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, ElementRef, ResolvedModel},
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};
fn models(library: &str, user: &str) -> Vec<(Model, ResolvedModel)> {
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
            assert!(model.add_source("calls.kerml", user).diagnostics.is_empty());
            let resolved = ResolvedModel::build(&model);
            (model, resolved)
        })
        .collect()
}

fn value(r: &mut ResolvedModel, name: &str) -> ElementRef {
    let feature = r.resolve_qualified(name).unwrap();
    let relation = r
        .owned_relationships(feature)
        .into_iter()
        .find(|&x| r.element_type(x) == "FeatureValue")
        .unwrap();
    match r.derived(relation, "value") {
        Derived::Value(v) => v.element().unwrap(),
        x => panic!("{x:?}"),
    }
}
fn result(r: &mut ResolvedModel, e: ElementRef) -> Option<ElementRef> {
    match r.derived(e, "result") {
        Derived::Value(v) => v.element(),
        x => panic!("{x:?}"),
    }
}
fn assert_canonical_role(model: &Model, r: &mut ResolvedModel, name: &str) -> ElementRef {
    let role = r
        .resolve_qualified(name)
        .expect("required role is declared");
    let names = sysmlv2_parser::json::library_element_name_map(model);
    assert_eq!(
        names.get(&r.element_id(role).to_string()),
        Some(&name.split("::").map(str::to_owned).collect::<Vec<_>>())
    );
    role
}

const LIBRARY: &str = r#"standard library package Metaobjects {metaclass Metaobject;}
standard library package Performances {
function MetadataAccessEvaluation {return result: Metaobjects::Metaobject[1..*];}
expr metadataAccessEvaluations: MetadataAccessEvaluation;
}"#;
const USER: &str =
    "class Subject; alias Other for Subject; feature a=Subject.metadata; feature b=Other.metadata;";

#[test]
fn metadata_access_inherits_typed_return_without_replacing_referenced_identity() {
    for materialize_first in [false, true] {
        for (mode, (model, mut r)) in models(LIBRARY, USER).into_iter().enumerate() {
            let loaded = model.loaded_library_unit_count();
            assert_canonical_role(&model, &mut r, "Performances::metadataAccessEvaluations");
            let subject = r.resolve_qualified("Subject").unwrap();
            let expected = r
                .resolve_qualified("Performances::MetadataAccessEvaluation::result")
                .unwrap();
            let scalar = r.resolve_qualified("Metaobjects::Metaobject").unwrap();
            for name in ["a", "b"] {
                let e = value(&mut r, name);
                assert_eq!(r.element_type(e), "MetadataAccessExpression");
                assert!(r.element_scope(e).is_none());
                let owned = r.owned_relationships(e);
                assert_eq!(owned.len(), 1);
                assert_eq!(r.element_type(owned[0]), "Membership");
                assert_eq!(r.membership_member(owned[0]), Some(subject));
                if materialize_first {
                    r.implied_relationships(e);
                }
                for policy in [
                    ClosurePolicy::Passthrough,
                    ClosurePolicy::Closure {
                        include_implied: false,
                    },
                ] {
                    r.set_closure_policy(policy);
                    assert_eq!(result(&mut r, e), None);
                }
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                });
                for _ in 0..2 {
                    assert_eq!(result(&mut r, e), Some(expected), "mode {mode}");
                    let memberships: Vec<_> = r
                        .inherited_memberships(e, true)
                        .into_iter()
                        .filter(|&m| r.element_type(m) == "ReturnParameterMembership")
                        .collect();
                    assert_eq!(memberships.len(), 1);
                    assert_eq!(r.membership_member(memberships[0]), Some(expected));
                    assert!(!r.inheritance_incomplete(e, true));
                    assert!(!r.inheritance_walk_truncated(e, true));
                    assert_eq!(r.effective_cardinality(expected), Some((1, None)));
                    let typing = r
                        .owned_relationships(expected)
                        .into_iter()
                        .find(|&x| r.element_type(x) == "FeatureTyping")
                        .unwrap();
                    assert_eq!(
                        r.element_properties(typing)["type"]["@id"],
                        r.element_id(scalar).to_string()
                    );
                    assert_eq!(r.owned_relationships(e), owned);
                    assert_eq!(r.membership_member(owned[0]), Some(subject));
                    assert!(r.element_scope(e).is_none());
                }
            }
            assert_eq!(model.loaded_library_unit_count(), loaded);
        }
    }
}

#[test]
fn metadata_result_requires_a_unique_loaded_canonical_typed_base() {
    for library in [
        "standard library package Performances;",
        "standard library package Performances {class metadataAccessEvaluations;}",
        "standard library package Performances {expr metadataAccessEvaluations;}",
        "standard library package Performances {function F; expr metadataAccessEvaluations:F;}",
        "standard library package Performances {function F {return result:Missing;} expr metadataAccessEvaluations:F;}",
        "standard library package Values {datatype A;datatype B;} standard library package Performances {function F {return a:Values::A;} function G{return b:Values::B;} expr metadataAccessEvaluations:F,G;}",
    ] {
        for (model, mut r) in models(library, USER) {
            let role = (library != "standard library package Performances;").then(|| {
                assert_canonical_role(&model, &mut r, "Performances::metadataAccessEvaluations")
            });
            let e = value(&mut r, "a");
            r.set_closure_policy(ClosurePolicy::Closure {
                include_implied: true,
            });
            assert_eq!(result(&mut r, e), None, "{library}");
            assert!(r.inheritance_incomplete(e, true), "{library}");
            if let Some(role) = role {
                let edges = r.implied_relationships(e);
                if r.element_type(role) == "Expression" {
                    assert_eq!(
                        edges.len(),
                        1,
                        "the partial hierarchy must reach the canonical base"
                    );
                    assert_eq!(
                        r.element_properties(edges[0])["subsettedFeature"]["@id"],
                        r.element_id(role).to_string()
                    );
                } else {
                    assert!(edges.is_empty());
                }
            }
        }
    }
}

#[test]
fn supplied_metadata_names_cannot_promote_loaded_user_returns() {
    use std::collections::HashMap;
    let user = format!("{USER} function F {{return wrong:Subject;}} expr fake:F;");
    for (_, mut r) in models("standard library package Performances;", &user) {
        let fake = r.resolve_qualified("fake").unwrap();
        r.set_library_names(&HashMap::from([(
            r.element_id(fake).to_string(),
            vec!["Performances".into(), "metadataAccessEvaluations".into()],
        )]));
        let e = value(&mut r, "a");
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        assert_eq!(result(&mut r, e), None);
        assert!(r.inheritance_incomplete(e, true));
        assert!(r.implied_relationships(e).is_empty());
    }
}

#[test]
fn standard_metadata_access_return_is_the_library_metaobject_parameter() {
    let library = sysmlv2_testkit::library_dir();
    if !library.exists() {
        eprintln!("skipping: library not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&library).expect("library loads");
    assert!(
        model
            .add_source("metadata-use.kerml", USER)
            .diagnostics
            .is_empty()
    );
    let mut r = ResolvedModel::build(&model);
    let function = r
        .resolve_qualified("Performances::MetadataAccessEvaluation")
        .unwrap();
    let scalar = r.resolve_qualified("Metaobjects::Metaobject").unwrap();
    let memberships: Vec<_> = r
        .owned_relationships(function)
        .into_iter()
        .filter(|&m| r.element_type(m) == "ReturnParameterMembership")
        .collect();
    assert_eq!(memberships.len(), 1);
    let expected = r.membership_member(memberships[0]).unwrap();
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let e = value(&mut r, "a");
    assert_eq!(result(&mut r, e), Some(expected));
    assert!(!r.inheritance_incomplete(e, true));
    assert_eq!(r.effective_cardinality(expected), Some((1, None)));
    let typing = r
        .owned_relationships(expected)
        .into_iter()
        .find(|&rel| r.element_type(rel) == "FeatureTyping")
        .unwrap();
    assert_eq!(
        r.element_properties(typing)["type"]["@id"],
        r.element_id(scalar).to_string()
    );
    assert!(r.element_scope(e).is_none());
    assert_eq!(r.owned_relationships(e).len(), 1);
}

#[test]
fn warmed_metadata_results_follow_role_and_referent_identity_updates() {
    use std::collections::HashMap;
    use uuid::Uuid;
    for external in [false, true] {
        for (_, mut r) in models(LIBRARY, USER) {
            let e = value(&mut r, "a");
            r.set_closure_policy(ClosurePolicy::Closure {
                include_implied: true,
            });
            let ret = result(&mut r, e).unwrap();
            let role = r
                .resolve_qualified("Performances::metadataAccessEvaluations")
                .unwrap();
            let subject = r.resolve_qualified("Subject").unwrap();
            let role_id = Uuid::parse_str("b0300000-0000-4000-8000-000000000001").unwrap();
            let subject_id = Uuid::parse_str("b0300000-0000-4000-8000-000000000002").unwrap();
            let ret_id = Uuid::parse_str("b0300000-0000-4000-8000-000000000003").unwrap();
            r.override_ids(&HashMap::from([
                (r.element_id(subject), subject_id),
                (r.element_id(ret), ret_id),
            ]));
            if external {
                r.set_library_names(&HashMap::from([(
                    role_id.to_string(),
                    vec!["Performances".into(), "metadataAccessEvaluations".into()],
                )]));
                assert_eq!(result(&mut r, e), None);
                assert!(r.inheritance_incomplete(e, true));
            } else {
                r.override_ids(&HashMap::from([(r.element_id(role), role_id)]));
                let actual = result(&mut r, e).unwrap();
                assert_eq!(r.element_id(actual), ret_id);
                assert!(!r.inheritance_incomplete(e, true));
            }
            let membership = r.owned_relationships(e)[0];
            let referent = r.membership_member(membership).unwrap();
            assert_eq!(r.element_id(referent), subject_id);
            let rels = r.implied_relationships(e);
            assert_eq!(rels.len(), 1);
            assert_eq!(
                r.element_properties(rels[0])["subsettedFeature"]["@id"],
                role_id.to_string()
            );
        }
    }
}
