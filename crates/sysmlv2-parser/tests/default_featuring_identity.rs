//! Specialization identity in connector featuring compatibility reads.
#![cfg(feature = "json")]
use std::{collections::HashMap, sync::Arc};
use sysmlv2_parser::{
    json::{Derived, DerivedValue, PropertyError, ResolvedModel},
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
            assert!(model.add_source(user_name, user).diagnostics.is_empty());
            let resolved = ResolvedModel::build(&model);
            (model, resolved)
        })
        .collect()
}

fn default(r: &mut ResolvedModel, name: &str) -> Option<sysmlv2_parser::json::ElementRef> {
    let connector = r.resolve_qualified(name).unwrap();
    assert_eq!(
        r.property(connector, "defaultFeaturingType"),
        Err(PropertyError::Approximate)
    );
    match r.derived(connector, "defaultFeaturingType") {
        Derived::Value(DerivedValue::Element(value)) => Some(value),
        Derived::Value(DerivedValue::Null) => None,
        other => panic!("unexpected default featuring value: {other:?}"),
    }
}
#[test]
fn conjugated_and_ordinary_specializations_preserve_default_featuring_identity() {
    let library = "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;} class A {feature x; feature y;}";
    let user = "class B conjugates A {feature y; connector c from A::x to y;} class C specializes A {feature z; connector c from A::x to z;} class D conjugates B {feature q; connector c from A::x to q;} class E specializes B {feature r; connector c from A::x to r;}";
    for (model, mut r) in models(library, user) {
        let loaded = model.loaded_library_unit_count();
        for _ in 0..2 {
            for name in ["C", "E"] {
                let expected = r.resolve_qualified(name).unwrap();
                assert_eq!(default(&mut r, &format!("{name}::c")), Some(expected));
            }
            // A conjugated receiver delegates specializes before reflexivity:
            // A does not specialize B or D, so neither is a common context.
            for name in ["B", "D"] {
                assert_eq!(default(&mut r, &format!("{name}::c")), None);
            }
        }
        let a = r.resolve_qualified("A").unwrap();
        r.override_ids(&HashMap::from([(r.element_id(a), Uuid::new_v4())]));
        let e = r.resolve_qualified("E").unwrap();
        assert_eq!(default(&mut r, "E::c"), Some(e));
        assert_eq!(default(&mut r, "B::c"), None);
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}
#[test]
fn missing_owned_featuring_evidence_cannot_select_a_default() {
    let library = "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;} class A;";
    let user = "class Good {feature x; feature y; connector c from x to y;} class MissingFeaturing {feature x featured by Missing; feature y; connector c from x to y;} class ExternalBase specializes Missing {feature x; feature y; connector c from x to y;}";
    for (_, mut r) in models(library, user) {
        let expected = r.resolve_qualified("Good").unwrap();
        assert_eq!(default(&mut r, "Good::c"), Some(expected));
        assert_eq!(default(&mut r, "MissingFeaturing::c"), None);
        // Reflexive compatibility remains a witness even if an unrelated
        // superclass is unavailable. Strict property access still refuses.
        let expected = r.resolve_qualified("ExternalBase").unwrap();
        assert_eq!(default(&mut r, "ExternalBase::c"), Some(expected));
    }
}

#[test]
fn inverse_type_featuring_is_not_omitted_from_common_contexts() {
    let library = "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;}";
    for (_, mut r) in models(
        library,
        "class B; class A {feature x; feature y; connector c from x to y;} featuring A::x by B;",
    ) {
        assert_eq!(default(&mut r, "A::c"), None);
    }
}
#[test]
fn a_missing_required_library_hierarchy_does_not_prove_candidate_absence() {
    for (_, mut r) in models(
        "class A {feature x;}",
        "class B conjugates A {feature y; connector c from A::x to y;}",
    ) {
        assert_eq!(default(&mut r, "B::c"), None);
    }
}

#[test]
fn unaudited_sysml_compatibility_domain_retains_existing_defaults() {
    let source = "package P { part def Wheel { port hub; } part def Axle {port end_;} part def Car {part w:Wheel; part ax:Axle; connection c1 connect w to ax; connection c2 connect w.hub to ax.end_; part inner {part x;part y;connection c3 connect x to y;}} part car:Car;connection top connect car.w to car.ax;}";
    for (_, mut r) in models_named("class A;", source, "compat.sysml") {
        let car = r.resolve_qualified("P::Car").unwrap();
        let inner = r.resolve_qualified("P::Car::inner").unwrap();
        assert_eq!(default(&mut r, "P::Car::c1"), Some(car));
        assert_eq!(default(&mut r, "P::Car::c2"), Some(car));
        assert_eq!(default(&mut r, "P::Car::inner::c3"), Some(inner));
        assert_eq!(default(&mut r, "P::top"), None);
    }
}

#[test]
fn materialized_implied_ownership_preserves_featuring_proofs_and_id_overrides() {
    let library = "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;}";
    let source =
        "class A {feature x;} class C specializes A {feature y; connector c from A::x to y;}";
    for (model, mut r) in models(library, source) {
        let loaded = model.loaded_library_unit_count();
        let a = r.resolve_qualified("A").unwrap();
        let c = r.resolve_qualified("C").unwrap();
        assert_eq!(default(&mut r, "C::c"), Some(c));
        assert!(!r.implied_relationships(a).is_empty());
        assert_eq!(default(&mut r, "C::c"), Some(c));
        r.override_ids(&HashMap::from([(r.element_id(a), Uuid::new_v4())]));
        assert_eq!(default(&mut r, "C::c"), Some(c));
        r.implied_relationships(a);
        assert_eq!(default(&mut r, "C::c"), Some(c));
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}
