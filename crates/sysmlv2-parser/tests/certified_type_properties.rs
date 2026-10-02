#![cfg(feature = "json")]
use std::{collections::HashMap, sync::Arc};
use sysmlv2_parser::{
    json::{
        ClosurePolicy, DerivedValue, Derives, FeatureTypeIssue, PropertyError, Reference,
        ResolvedModel, conditional_property_capability, derives,
    },
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};
const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance; step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
fn models() -> Vec<(Model, ResolvedModel)> {
    models_with_library(LIB)
}
fn models_with_library(library: &str) -> Vec<(Model, ResolvedModel)> {
    let mut base = Model::new();
    assert!(
        base.add_library_source("certified-library.kerml", library)
            .diagnostics
            .is_empty()
    );
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(83).unwrap(), 83).unwrap());
    (0..4).map(|mode|{let mut m=Model::new();match mode {2=>Arc::clone(&prepared).install(&mut m).unwrap(),3=>Arc::clone(&decoded).install(&mut m).unwrap(),_=>{m.add_library_source("certified-library.kerml",library);if mode==1{m.set_library_cache(cache.clone());}}};assert!(m.add_source("certified-user.kerml","function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations; expr implicit:F; feature x:Base::Anything subsets Base::things;").diagnostics.is_empty());let r=ResolvedModel::build(&m);(m,r)}).collect()
}
#[test]
fn conditional_generic_properties_replay_preserve_ids_policy_and_compatibility() {
    for (m, mut r) in models() {
        let e = r.resolve_qualified("e").unwrap();
        let f = r.resolve_qualified("F").unwrap();
        let implicit = r.resolve_qualified("implicit").unwrap();
        let x = r.resolve_qualified("x").unwrap();
        let anything = r.resolve_qualified("Base::Anything").unwrap();
        let ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
        let rows = r.elements().count();
        let loaded = m.loaded_library_unit_count();
        assert_eq!(derives("Expression", "function"), Derives::Passthrough);
        assert!(conditional_property_capability("Kernel-Functions-Expression-function").is_some());
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
            let legacy = r.derived(e, "type");
            if policy
                == (ClosurePolicy::Closure {
                    include_implied: true,
                })
            {
                for _ in 0..2 {
                    let expected = serde_json::json!({"@id":r.element_id(f).to_string()});
                    assert_eq!(r.property(e, "function"), Ok(expected.clone()));
                    assert_eq!(
                        r.property(e, "behavior"),
                        Ok(serde_json::json!([expected.clone()]))
                    );
                    assert_eq!(r.property(e, "type"), Ok(serde_json::json!([expected])));
                    assert_eq!(
                        r.derived_exact(e, "function"),
                        Ok(DerivedValue::Reference(Reference::Element(f)))
                    );
                    assert_eq!(
                        r.derived_exact(e, "behavior"),
                        Ok(DerivedValue::References(vec![Reference::Element(f)]))
                    );
                    assert_eq!(
                        r.property(x, "type"),
                        Ok(serde_json::json!([{"@id":r.element_id(anything).to_string()}]))
                    );
                    assert_eq!(
                        r.property(implicit, "function"),
                        Ok(serde_json::json!({"@id":r.element_id(f).to_string()}))
                    );
                }
            } else {
                assert_eq!(r.property(e, "function"), Err(PropertyError::Approximate));
                assert_eq!(r.derived_exact(e, "type"), Err(PropertyError::Approximate));
            }
            assert_eq!(r.derived(e, "type"), legacy);
            assert_eq!(r.closure_policy(), policy);
        }
        assert_eq!(
            r.user_elements()
                .map(|e| r.element_id(e))
                .collect::<Vec<_>>(),
            ids
        );
        assert_eq!(r.elements().count(), rows);
        assert_eq!(m.loaded_library_unit_count(), loaded);
        let replacement = uuid::Uuid::new_v4();
        r.override_ids(&HashMap::from([(r.element_id(f), replacement)]));
        assert_eq!(
            r.property(e, "function"),
            Ok(serde_json::json!({"@id":replacement.to_string()}))
        );
        assert_eq!(
            r.property(implicit, "function"),
            Ok(serde_json::json!({"@id":replacement.to_string()}))
        );
    }
}
#[test]
fn actual_library_generic_certification_uses_the_same_report_identity() {
    let library = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../spec-refs/SysML-v2-Release/sysml.library");
    if !library.exists() {
        eprintln!("standard library unavailable");
        return;
    }
    let mut m = Model::new();
    m.load_library_dir(&library).unwrap();
    assert!(m.add_source("certified-actual.kerml","function F specializes Performances::Evaluation; expr e:F subsets Performances::evaluations;").diagnostics.is_empty());
    let mut r = ResolvedModel::build(&m);
    let e = r.resolve_qualified("e").unwrap();
    let f = r.resolve_qualified("F").unwrap();
    let report = r.feature_type_report(e);
    assert_eq!(report.function, Ok(Some(f)));
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    assert_eq!(
        r.property(e, "function"),
        Ok(serde_json::json!({"@id":r.element_id(f).to_string()}))
    );
    assert_eq!(
        r.derived_exact(e, "type"),
        Ok(DerivedValue::References(vec![Reference::Element(f)]))
    );
}

#[test]
fn inverse_typing_is_available_to_generic_facades_without_changing_legacy_output() {
    let mut m = Model::new();
    assert!(
        m.add_library_source("inverse-library.kerml", LIB)
            .diagnostics
            .is_empty()
    );
    assert!(m.add_source("inverse-user.kerml","function F specializes Performances::Evaluation; feature x subsets Performances::evaluations; typing x typed by F;").diagnostics.is_empty());
    let mut r = ResolvedModel::build(&m);
    let x = r.resolve_qualified("x").unwrap();
    let f = r.resolve_qualified("F").unwrap();
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let old = match r.derived(x, "type") {
        sysmlv2_parser::json::Derived::Value(value) => value,
        other => panic!("{other:?}"),
    };
    assert!(
        !old.elements().contains(&f),
        "legacy owned-only reader misses standalone typing"
    );
    assert_eq!(
        r.derived_exact(x, "type"),
        Ok(DerivedValue::References(vec![Reference::Element(f)]))
    );
    assert_eq!(
        r.property(x, "type"),
        Ok(serde_json::json!([{"@id":r.element_id(f).to_string()}]))
    );
    assert_eq!(
        r.derived(x, "type"),
        sysmlv2_parser::json::Derived::Value(old)
    );
    assert_eq!(
        r.derived_exact(x, "type"),
        Ok(DerivedValue::References(vec![Reference::Element(f)]))
    );
}

#[test]
fn implied_step_ancestry_supplies_omitted_authored_subsetting_across_replay() {
    let library = LIB.replace(
        "expr evaluations:Evaluation subsets performances;",
        "expr evaluations:Evaluation;",
    );
    assert_ne!(library, LIB);
    for (_, mut r) in models_with_library(&library) {
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let f = r.resolve_qualified("F").unwrap();
        for path in ["e", "implicit"] {
            let e = r.resolve_qualified(path).unwrap();
            assert_eq!(r.feature_type_report(e).function, Ok(Some(f)));
            assert_eq!(
                r.property(e, "function"),
                Ok(serde_json::json!({"@id":r.element_id(f).to_string()}))
            );
        }
    }
}

#[test]
fn missing_required_ancestry_stays_incomplete_across_replay() {
    // A missing canonical Step Feature cannot be repaired by implied ancestry.
    // Remove its authored reference too, retaining a well-formed stored graph
    // whose only missing requirement is the implied specialization family.
    let library = LIB
        .replace(
            "step performances:Performance subsets Occurrences::occurrences;",
            "",
        )
        .replace(
            "expr evaluations:Evaluation subsets performances;",
            "expr evaluations:Evaluation;",
        );
    assert_ne!(library, LIB);
    for (model, mut r) in models_with_library(&library) {
        let e = r.resolve_qualified("implicit").unwrap();
        assert!(r.resolve_qualified("Performances::evaluations").is_some());
        assert!(r.resolve_qualified("Performances::performances").is_none());
        assert!(r.resolve_qualified("Performances::Performance").is_some());
        let ids: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
        let loaded = model.loaded_library_unit_count();
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let legacy = r.derived(e, "type");
        for _ in 0..2 {
            assert_eq!(
                r.feature_type_report(e).function,
                Err(FeatureTypeIssue::MissingRequiredFamilies)
            );
            assert_eq!(
                r.property(e, "function"),
                Err(PropertyError::IncompleteTypeProjection(
                    FeatureTypeIssue::MissingRequiredFamilies
                ))
            );
            let errors = r.to_full_json_strict().unwrap_err();
            assert!(
                errors
                    .issues
                    .iter()
                    .any(|issue| issue.element_id == r.element_id(e)
                        && issue.property == "function"
                        && issue.reason
                            == PropertyError::IncompleteTypeProjection(
                                FeatureTypeIssue::MissingRequiredFamilies
                            ))
            );
            assert_eq!(r.derived(e, "type"), legacy);
        }
        assert_eq!(
            r.user_elements()
                .map(|e| r.element_id(e))
                .collect::<Vec<_>>(),
            ids
        );
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}
