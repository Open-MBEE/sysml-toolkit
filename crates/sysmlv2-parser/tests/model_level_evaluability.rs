//! Additive checked model-level eligibility remains distinct from execution.
#![cfg(feature = "json")]
use std::{collections::HashMap, sync::Arc};
use sysmlv2_parser::{
    json::{
        ClosurePolicy, Derived, DerivedValue, ElementRef, ModelLevelEvaluability as Eligibility,
        PropertyError, ResolvedModel,
    },
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};
use uuid::Uuid;
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
            let unit = model.add_source(user_name, user);
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
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
        .find(|&r0| r.element_type(r0) == "FeatureValue")
        .unwrap();
    match r.derived(relation, "value") {
        Derived::Value(v) => v.element().unwrap(),
        value => panic!("{value:?}"),
    }
}
const LIBRARY: &str = "standard library package Base {classifier Anything {feature self;}} standard library package DataFunctions {function '+' {in a; in b; return r;}}";
#[test]
fn eligibility_leaf_reference_and_unknown_cases_survive_all_replay_modes() {
    let source = r#"class T; feature raw; feature plain=raw; feature lit=1; feature via=lit;
        feature n=null; feature text="s"; feature metaRead=T.metadata;
        feature bad featured by Missing; feature badRef=bad;
        feature missingCtor=new Missing(); feature missingMetadata=Missing.metadata;
        feature selfRef=Base::Anything::self;
        function User {return result;} feature call=User();
        feature sum=DataFunctions::'+'(1,2);"#;
    for (mode, (model, mut r)) in models(LIBRARY, source).into_iter().enumerate() {
        let loaded = model.loaded_library_unit_count();
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
            for _ in 0..2 {
                for name in ["plain", "lit", "via", "n", "text", "metaRead", "selfRef"] {
                    let e = value(&mut r, name);
                    assert_eq!(
                        r.model_level_evaluability(e).classification,
                        Eligibility::Evaluable,
                        "mode {mode}: {name}"
                    );
                    assert_eq!(
                        r.property(e, "isModelLevelEvaluable"),
                        Err(PropertyError::Approximate)
                    );
                }
                for name in ["badRef", "missingCtor", "missingMetadata", "sum", "call"] {
                    let e = value(&mut r, name);
                    assert!(
                        matches!(
                            r.model_level_evaluability(e).classification,
                            Eligibility::Unknown(_)
                        ),
                        "mode {mode}: {name}"
                    );
                }
                let bad = value(&mut r, "badRef");
                assert!(
                    matches!(
                        r.derived(bad, "isModelLevelEvaluable"),
                        Derived::Value(DerivedValue::Bool(true))
                    ),
                    "legacy compatibility value is deliberately unchanged"
                );
            }
        }
        let self_element = r.resolve_qualified("Base::Anything::self").unwrap();
        r.override_ids(&HashMap::from([(
            r.element_id(self_element),
            Uuid::new_v4(),
        )]));
        let e = value(&mut r, "selfRef");
        assert_eq!(
            r.model_level_evaluability(e).classification,
            Eligibility::Evaluable
        );
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}
#[test]
fn definite_sysml_override_and_explicit_general_specialization_are_negative() {
    for (_, mut r) in models_named(LIBRARY, "calc def F {return r;} calc c:F;", "uses.sysml") {
        let c = r.resolve_qualified("c").unwrap();
        assert_eq!(
            r.model_level_evaluability(c).classification,
            Eligibility::NotEvaluable
        );
    }
    for (_, mut r) in models(LIBRARY, "expr explicit : Missing;") {
        let explicit = r.resolve_qualified("explicit").unwrap();
        assert_eq!(
            r.model_level_evaluability(explicit).classification,
            Eligibility::NotEvaluable
        );
    }
}

#[test]
fn checked_metadata_and_references_survive_materialization_and_id_remap() {
    let library = format!(
        "{LIBRARY} standard library package Occurrences {{class Occurrence specializes Base::Anything;}}"
    );
    for (mode, (model, mut r)) in models(&library,
        "class T; feature lit=1; feature via=lit; feature metaRead=T.metadata; feature selfRef=Base::Anything::self;").into_iter().enumerate() {
        let loaded = model.loaded_library_unit_count();
        for name in ["via", "metaRead", "selfRef"] {
            let expression = value(&mut r, name);
            assert_eq!(r.model_level_evaluability(expression).classification, Eligibility::Evaluable);
        }
        let t = r.resolve_qualified("T").unwrap();
        assert!(!r.implied_relationships(t).is_empty(), "fixture must materialize a real suffix");
        for remapped in [false, true] {
            if remapped {
                let self_feature = r.resolve_qualified("Base::Anything::self").unwrap();
                r.override_ids(&HashMap::from([
                    (r.element_id(t), Uuid::new_v4()),
                    (r.element_id(self_feature), Uuid::new_v4()),
                ]));
            }
            for name in ["via", "metaRead", "selfRef"] {
                let expression = value(&mut r, name);
                assert_eq!(r.model_level_evaluability(expression).classification, Eligibility::Evaluable,
                    "mode {mode}, remapped {remapped}: {name}");
            }
        }
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}
