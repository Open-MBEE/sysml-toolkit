#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, ElementRef, ResolvedModel, model_to_compact_json},
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};
const LIB: &str = "standard library package ControlFunctions {function '.' {in source {feature target;} return result;}}";
const USER: &str = "class A {feature x;} feature a:A; feature y=a.x;";
fn refs(r: &mut ResolvedModel, e: ElementRef, property: &str) -> Vec<ElementRef> {
    match r.derived(e, property) {
        Derived::Value(value) => value.elements(),
        other => panic!("{property}: {other:?}"),
    }
}
#[test]
fn fixed_chain_typing_and_input_redefinition_replay_without_promoting_function() {
    let mut base = Model::new();
    base.add_library_source("fixed-dot-library.kerml", LIB);
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(118).unwrap(), 118).unwrap());
    let mut expected = None;
    for mode in 0..4 {
        let mut model = Model::new();
        match mode {
            2 => Arc::clone(&prepared).install(&mut model).unwrap(),
            3 => Arc::clone(&decoded).install(&mut model).unwrap(),
            _ => {
                model.add_library_source("fixed-dot-library.kerml", LIB);
                if mode == 1 {
                    model.set_library_cache(cache.clone());
                }
            }
        }
        assert!(
            model
                .add_source("fixed-dot-user.kerml", USER)
                .diagnostics
                .is_empty()
        );
        let compact = model_to_compact_json(&model);
        let mut r = ResolvedModel::build(&model);
        let source_ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
        let chain = r
            .user_elements()
            .find(|&e| r.element_type(e) == "FeatureChainExpression")
            .unwrap();
        let dot = r.resolve_qualified("ControlFunctions::'.'").unwrap();
        let source = r
            .resolve_qualified("ControlFunctions::'.'::source")
            .unwrap();
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
            let typing: Vec<_> = r
                .implied_relationships(chain)
                .into_iter()
                .filter(|&e| r.element_type(e) == "FeatureTyping")
                .collect();
            assert_eq!(typing.len(), 1);
            assert_eq!(
                r.element_properties(typing[0])["type"]["@id"],
                r.element_id(dot).to_string()
            );
            let input = refs(&mut r, chain, "ownedFeature")
                .into_iter()
                .find(|&e| r.element_properties(e)["direction"] == "in")
                .unwrap();
            let redefinitions: Vec<_> = r
                .implied_relationships(input)
                .into_iter()
                .filter(|&e| r.element_type(e) == "Redefinition")
                .collect();
            assert_eq!(redefinitions.len(), 1);
            assert_eq!(
                r.element_properties(redefinitions[0])["redefinedFeature"]["@id"],
                r.element_id(source).to_string()
            );
            let ids = (r.element_id(typing[0]), r.element_id(redefinitions[0]));
            if let Some(old) = expected {
                assert_eq!(old, ids);
            } else {
                expected = Some(ids);
            }
            assert!(r.feature_type_report(chain).function.is_err());
        }
        assert_eq!(
            source_ids,
            r.user_elements()
                .map(|e| r.element_id(e))
                .collect::<Vec<_>>()
        );
        assert_eq!(compact, model_to_compact_json(&model));
    }
}
