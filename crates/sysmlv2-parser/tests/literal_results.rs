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

const LIBRARY: &str = r#"standard library package Values {datatype Integer; datatype Boolean; datatype Real; datatype String; datatype Anything;}
standard library package Performances {
function IntegerEvaluation {return result: Values::Integer[1];}
function BooleanEvaluation {return result: Values::Boolean[1];}
function RationalEvaluation {return result: Values::Real[1];}
function StringEvaluation {return result: Values::String[1];}
function NullEvaluation {return result: Values::Anything[0..0];}
expr literalIntegerEvaluations: IntegerEvaluation;
expr literalBooleanEvaluations: BooleanEvaluation;
expr literalRationalEvaluations: RationalEvaluation;
expr literalStringEvaluations: StringEvaluation;
expr nullEvaluations: NullEvaluation;
}"#;
const USER: &str =
    r#"feature b=true; feature i=1; feature r=1.25; feature s="x"; feature inf=*; feature n=null;"#;
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
#[test]
fn literal_results_reuse_library_return_identities_without_scopes_or_owned_results() {
    for materialize_first in [false, true] {
        for (mode, (model, mut r)) in models(LIBRARY, USER).into_iter().enumerate() {
            let loaded = model.loaded_library_unit_count();
            assert_canonical_role(&model, &mut r, "Performances::literalIntegerEvaluations");
            let explicit: Vec<_> = r
                .elements()
                .map(|e| {
                    (
                        r.element_id(e),
                        r.element_type(e).to_string(),
                        r.element_properties(e),
                        r.owned_relationships(e),
                    )
                })
                .collect();
            for (name, function, kind) in [
                ("b", "BooleanEvaluation", "Boolean"),
                ("i", "IntegerEvaluation", "Integer"),
                ("r", "RationalEvaluation", "Real"),
                ("s", "StringEvaluation", "String"),
                ("inf", "IntegerEvaluation", "Integer"),
                ("n", "NullEvaluation", "Anything"),
            ] {
                let e = value(&mut r, name);
                assert!(r.element_scope(e).is_none());
                assert!(r.owned_relationships(e).is_empty());
                if materialize_first {
                    r.implied_relationships(e);
                }
                r.set_closure_policy(ClosurePolicy::Passthrough);
                assert_eq!(result(&mut r, e), None);
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: false,
                });
                assert_eq!(result(&mut r, e), None);
                assert!(r.inherited_memberships(e, false).is_empty());
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                });
                let expected = r
                    .resolve_qualified(&format!("Performances::{function}::result"))
                    .unwrap();
                let expected_type = r.resolve_qualified(&format!("Values::{kind}")).unwrap();
                for _ in 0..2 {
                    assert_eq!(result(&mut r, e), Some(expected), "mode {mode} {name}");
                    let returns: Vec<_> = r
                        .inherited_memberships(e, true)
                        .into_iter()
                        .filter(|&m| r.element_type(m) == "ReturnParameterMembership")
                        .collect();
                    assert_eq!(returns.len(), 1);
                    assert_eq!(r.membership_member(returns[0]), Some(expected));
                    assert!(r.inherited_features(e, true).contains(&expected));
                    assert!(!r.inheritance_incomplete(e, true));
                    assert!(!r.inheritance_walk_truncated(e, true));
                    assert_eq!(
                        r.effective_cardinality(expected),
                        Some(if name == "n" {
                            (0, Some(0))
                        } else {
                            (1, Some(1))
                        })
                    );
                    let typing = r
                        .owned_relationships(expected)
                        .into_iter()
                        .find(|&rel| r.element_type(rel) == "FeatureTyping")
                        .unwrap();
                    assert_eq!(
                        r.element_properties(typing)["type"]["@id"],
                        r.element_id(expected_type).to_string()
                    );
                }
                assert!(r.element_scope(e).is_none());
                assert!(r.owned_relationships(e).is_empty());
            }
            let after: Vec<_> = r
                .elements()
                .map(|e| {
                    (
                        r.element_id(e),
                        r.element_type(e).to_string(),
                        r.element_properties(e),
                        r.owned_relationships(e),
                    )
                })
                .collect();
            assert_eq!(explicit, after);
            assert_eq!(loaded, model.loaded_library_unit_count());
        }
    }
}
#[test]
fn absent_or_incomplete_literal_library_never_fabricates_a_result() {
    for library in [
        "",
        "standard library package Performances {class literalIntegerEvaluations;}",
        "standard library package Performances {expr literalIntegerEvaluations;}",
        "standard library package Performances {function F; expr literalIntegerEvaluations:F;}",
        "standard library package Performances {function F {return result:Missing;} expr literalIntegerEvaluations:F;}",
        "standard library package Values {datatype T;} standard library package Performances {function A {return a:Values::T;} function B {return b:Values::T;} expr literalIntegerEvaluations:A,B;}",
    ] {
        for (model, mut r) in models(library, "feature i=1;") {
            let role = (!library.is_empty()).then(|| {
                assert_canonical_role(&model, &mut r, "Performances::literalIntegerEvaluations")
            });
            let e = value(&mut r, "i");
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
            assert!(r.owned_relationships(e).is_empty());
            assert!(r.element_scope(e).is_none());
        }
    }
}
#[test]
fn external_literal_base_retains_identity_but_has_no_in_model_return() {
    use std::collections::HashMap;
    for (_, mut r) in models("", "feature i=1;") {
        let id = "b0200000-0000-4000-8000-000000000001";
        r.set_library_names(&HashMap::from([(
            id.to_owned(),
            vec![
                "Performances".to_owned(),
                "literalIntegerEvaluations".to_owned(),
            ],
        )]));
        let e = value(&mut r, "i");
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        assert_eq!(result(&mut r, e), None);
        assert!(r.inheritance_incomplete(e, true));
        let relationships = r.implied_relationships(e);
        assert_eq!(relationships.len(), 1);
        assert_eq!(
            r.element_properties(relationships[0])["subsettedFeature"]["@id"],
            id
        );
    }
}
#[test]
fn literal_plan_obeys_id_remaps_and_external_override_before_materialization() {
    use std::collections::HashMap;
    use uuid::Uuid;
    for override_names in [false, true] {
        for (_, mut r) in models(LIBRARY, "feature i=1;") {
            let e = value(&mut r, "i");
            r.set_closure_policy(ClosurePolicy::Closure {
                include_implied: true,
            });
            assert!(result(&mut r, e).is_some());
            let target = r
                .resolve_qualified("Performances::literalIntegerEvaluations")
                .unwrap();
            let new = Uuid::parse_str("b0200000-0000-4000-8000-000000000002").unwrap();
            if override_names {
                r.set_library_names(&HashMap::from([(
                    new.to_string(),
                    vec![
                        "Performances".to_owned(),
                        "literalIntegerEvaluations".to_owned(),
                    ],
                )]));
                assert_eq!(result(&mut r, e), None);
                assert!(r.inheritance_incomplete(e, true));
            } else {
                let ret = r
                    .resolve_qualified("Performances::IntegerEvaluation::result")
                    .unwrap();
                let ret_id = Uuid::parse_str("b0200000-0000-4000-8000-000000000003").unwrap();
                r.override_ids(&HashMap::from([
                    (r.element_id(target), new),
                    (r.element_id(ret), ret_id),
                ]));
                let actual = result(&mut r, e).unwrap();
                assert_eq!(r.element_id(actual), ret_id);
                assert!(!r.inheritance_incomplete(e, true));
            }
            let rels = r.implied_relationships(e);
            assert_eq!(rels.len(), 1);
            assert_eq!(
                r.element_properties(rels[0])["subsettedFeature"]["@id"],
                new.to_string()
            );
            let expected = Uuid::new_v5(
                &Uuid::NAMESPACE_OID,
                format!("{}/implied/Subsetting/{new}", r.element_id(e)).as_bytes(),
            );
            assert_eq!(r.element_id(rels[0]), expected);
        }
    }
}
#[test]
fn user_spelling_does_not_override_library_literal_identity() {
    let user = "package U {package Performances {feature literalIntegerEvaluations;} feature i=1;}";
    for (_, mut r) in models(LIBRARY, user) {
        let e = value(&mut r, "U::i");
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let expected = r
            .resolve_qualified("Performances::IntegerEvaluation::result")
            .unwrap();
        assert_eq!(result(&mut r, e), Some(expected));
    }
}

#[test]
fn supplied_names_cannot_promote_a_loaded_user_expression_into_literal_library_role() {
    use std::collections::HashMap;
    for (_, mut r) in models(
        "standard library package Values {datatype T;}",
        "function F {return result:Values::T;} expr replacement:F; feature i=1;",
    ) {
        let replacement = r.resolve_qualified("replacement").unwrap();
        r.set_library_names(&HashMap::from([(
            r.element_id(replacement).to_string(),
            vec![
                "Performances".to_owned(),
                "literalIntegerEvaluations".to_owned(),
            ],
        )]));
        let e = value(&mut r, "i");
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        assert_eq!(result(&mut r, e), None);
        assert!(r.inheritance_incomplete(e, true));
        assert!(r.implied_relationships(e).is_empty());
    }
}

#[test]
fn loaded_standard_library_supplies_literal_integer_and_null_results() {
    let library = sysmlv2_testkit::library_dir();
    if !library.exists() {
        eprintln!("skipping: library not present");
        return;
    }
    let mut m = Model::new();
    m.load_library_dir(&library).expect("library loads");
    assert!(
        m.add_source("literal-use.kerml", "feature i=1; feature n=null;")
            .diagnostics
            .is_empty()
    );
    let mut r = ResolvedModel::build(&m);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    for (name, function, scalar, range) in [
        (
            "i",
            "Performances::LiteralIntegerEvaluation",
            "ScalarValues::Integer",
            (1, Some(1)),
        ),
        (
            "n",
            "Performances::NullEvaluation",
            "Base::Anything",
            (0, Some(0)),
        ),
    ] {
        let e = value(&mut r, name);
        let function = r.resolve_qualified(function).unwrap();
        let scalar = r.resolve_qualified(scalar).unwrap();
        let returns: Vec<_> = r
            .owned_relationships(function)
            .into_iter()
            .filter(|&relationship| r.element_type(relationship) == "ReturnParameterMembership")
            .collect();
        assert_eq!(returns.len(), 1);
        let expected = r.membership_member(returns[0]).unwrap();
        for _ in 0..2 {
            assert_eq!(result(&mut r, e), Some(expected), "{name}");
            assert!(!r.inheritance_walk_truncated(e, true));
            assert!(!r.inheritance_incomplete(e, true));
            let membership: Vec<_> = r
                .inherited_memberships(e, true)
                .into_iter()
                .filter(|&m| r.element_type(m) == "ReturnParameterMembership")
                .collect();
            assert_eq!(membership, returns);
            let typing = r
                .owned_relationships(expected)
                .into_iter()
                .find(|&rel| r.element_type(rel) == "FeatureTyping")
                .unwrap();
            assert_eq!(
                r.element_properties(typing)["type"]["@id"],
                r.element_id(scalar).to_string()
            );
            assert_eq!(r.effective_cardinality(expected), Some(range));
            assert!(r.element_scope(e).is_none());
            assert!(r.owned_relationships(e).is_empty());
        }
    }
}

#[test]
fn existing_implied_relationships_keep_library_and_user_identity_schemes() {
    use uuid::Uuid;
    let library = LIBRARY.replace(
        "standard library package Performances {",
        "standard library package Performances {function Evaluation; function Marker;",
    );
    for (_, mut r) in models_named(
        &library,
        "enum def Color { red; } attribute i=1;",
        "calls.sysml",
    ) {
        let marker = r.resolve_qualified("Performances::Marker").unwrap();
        let evaluation = r.resolve_qualified("Performances::Evaluation").unwrap();
        let variant = r.resolve_qualified("Color::red").unwrap();
        let expected_library = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!(
                "{}/implied/Subclassification/{}",
                r.element_id(marker),
                r.element_id(evaluation)
            )
            .as_bytes(),
        );
        let expected_user = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!("{}/implied0", r.element_id(variant)).as_bytes(),
        );
        let mut before = Vec::new();
        for (owner, expected) in [(marker, expected_library), (variant, expected_user)] {
            let ids: Vec<_> = r
                .implied_relationships(owner)
                .into_iter()
                .map(|rel| r.element_id(rel))
                .collect();
            assert_eq!(ids, vec![expected]);
            before.push((owner, ids));
        }
        let e = value(&mut r, "i");
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        assert!(result(&mut r, e).is_some());
        for (owner, expected) in before {
            let ids: Vec<_> = r
                .implied_relationships(owner)
                .into_iter()
                .map(|rel| r.element_id(rel))
                .collect();
            assert_eq!(ids, expected);
        }
    }
}

#[test]
fn loaded_literal_identity_collisions_never_choose_a_library_namesake() {
    use std::collections::HashMap;
    const LIB: &str = r#"
standard library package Values {datatype Integer; datatype String;}
standard library package Performances {
 function IntegerEvaluation {return integerResult:Values::Integer;}
 function OtherEvaluation {return otherResult:Values::String;}
 expr literalIntegerEvaluations:IntegerEvaluation;
 expr impostor:OtherEvaluation;
}"#;
    for collision in ["role", "return", "owner", "type", "membership", "typing"] {
        for materialize_first in [false, true] {
            for (mode, (_, mut r)) in models(LIB, "feature i=1;").into_iter().enumerate() {
                let literal = value(&mut r, "i");
                r.set_closure_policy(ClosurePolicy::Closure {
                    include_implied: true,
                });
                let good = r
                    .resolve_qualified("Performances::IntegerEvaluation::integerResult")
                    .unwrap();
                let bad = r
                    .resolve_qualified("Performances::OtherEvaluation::otherResult")
                    .unwrap();
                assert_eq!(result(&mut r, literal), Some(good));
                assert!(!r.inheritance_incomplete(literal, true));
                let role = r
                    .resolve_qualified("Performances::literalIntegerEvaluations")
                    .unwrap();
                let impostor = r.resolve_qualified("Performances::impostor").unwrap();
                let owner = r
                    .resolve_qualified("Performances::IntegerEvaluation")
                    .unwrap();
                let other_owner = r
                    .resolve_qualified("Performances::OtherEvaluation")
                    .unwrap();
                let find = |r: &mut ResolvedModel, e, kind| {
                    r.owned_relationships(e)
                        .into_iter()
                        .find(|&rel| r.element_type(rel) == kind)
                        .unwrap()
                };
                let (source, target) = match collision {
                    "role" => (role, impostor),
                    "return" => (good, bad),
                    "owner" => (owner, other_owner),
                    "type" => (
                        r.resolve_qualified("Values::Integer").unwrap(),
                        r.resolve_qualified("Values::String").unwrap(),
                    ),
                    "membership" => (
                        find(&mut r, owner, "ReturnParameterMembership"),
                        find(&mut r, other_owner, "ReturnParameterMembership"),
                    ),
                    "typing" => (
                        find(&mut r, role, "FeatureTyping"),
                        find(&mut r, impostor, "FeatureTyping"),
                    ),
                    _ => unreachable!(),
                };
                if materialize_first {
                    r.implied_relationships(literal);
                }
                r.override_ids(&HashMap::from([(
                    r.element_id(source),
                    r.element_id(target),
                )]));
                for _ in 0..2 {
                    assert_eq!(
                        result(&mut r, literal),
                        None,
                        "{collision} mode={mode} materialized={materialize_first}"
                    );
                    assert!(
                        r.inheritance_incomplete(literal, true),
                        "{collision} mode={mode} materialized={materialize_first}"
                    );
                }
                assert!(r.element_scope(literal).is_none());
                assert!(r.owned_relationships(literal).is_empty());
            }
        }
    }
}

#[test]
fn materializing_an_implied_edge_invalidates_unique_literal_endpoint_evidence() {
    use std::collections::HashMap;
    use uuid::Uuid;
    for (_, mut r) in models(LIBRARY, "feature i=1;") {
        let literal = value(&mut r, "i");
        let role = r
            .resolve_qualified("Performances::literalIntegerEvaluations")
            .unwrap();
        let ret = r
            .resolve_qualified("Performances::IntegerEvaluation::result")
            .unwrap();
        let generated_id = Uuid::new_v5(
            &Uuid::NAMESPACE_OID,
            format!(
                "{}/implied/Subsetting/{}",
                r.element_id(literal),
                r.element_id(role)
            )
            .as_bytes(),
        );
        r.override_ids(&HashMap::from([(r.element_id(ret), generated_id)]));
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        assert_eq!(result(&mut r, literal), Some(ret));
        assert!(!r.inheritance_incomplete(literal, true));
        let edges = r.implied_relationships(literal);
        assert!(
            edges
                .into_iter()
                .any(|edge| r.element_id(edge) == generated_id)
        );
        assert_eq!(result(&mut r, literal), None);
        assert!(r.inheritance_incomplete(literal, true));
    }
}
