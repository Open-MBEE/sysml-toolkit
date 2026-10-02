//! Compatibility view exposures retain import operation order and identity.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};

fn models(library: &str, user: &str) -> Vec<(Model, ResolvedModel)> {
    let mut base = Model::new();
    base.add_library_source("views.sysml", library);
    assert!(!base.has_errors());
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(67).unwrap(), 67).unwrap());
    (0..4)
        .map(|mode| {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("views.sysml", library);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            m.add_source("view-use.sysml", user);
            assert!(!m.has_errors());
            let r = ResolvedModel::build(&m);
            (m, r)
        })
        .collect()
}

fn check(library: &str, user: &str, cases: &[(&str, &[&str])]) {
    for (mode, (model, mut resolved)) in models(library, user).into_iter().enumerate() {
        let loaded = model.loaded_library_unit_count();
        for _ in 0..2 {
            for &(view, expected) in cases {
                let view = resolved.resolve_qualified(view).unwrap();
                let names: Vec<_> = resolved
                    .view_exposed_elements(view)
                    .into_iter()
                    .map(|element| resolved.element_qualified_name(element).unwrap())
                    .collect();
                assert_eq!(names, expected, "mode={mode}");
            }
        }
        assert_eq!(model.loaded_library_unit_count(), loaded);
        if mode == 3 {
            assert_eq!(loaded, 0);
        }
    }
}

#[test]
fn excluded_redefining_import_does_not_remove_a_valid_inherited_membership() {
    let library = "part def A {part x;}
        part def P :> A {part y redefines A::x; public import D::*;}
        part def C {public import P::*;}
        part def D :> A, C;";
    let user = "view v {expose P::*;}";
    for first_global in [false, true] {
        for (mode, (model, mut r)) in models(library, user).into_iter().enumerate() {
            let loaded = model.loaded_library_unit_count();
            let a = r.resolve_qualified("A::x").unwrap();
            let y = r.resolve_qualified("P::y").unwrap();
            let d = r.resolve_qualified("D").unwrap();
            let v = r.resolve_qualified("v").unwrap();
            assert_eq!(r.redefinition_targets(y), vec![a]);
            let global = |r: &mut ResolvedModel| {
                r.inherited_memberships(d, true)
                    .into_iter()
                    .filter_map(|membership| r.membership_member(membership))
                    .collect::<Vec<_>>()
            };
            if first_global {
                assert_eq!(global(&mut r), vec![y]);
            }
            for _ in 0..2 {
                // These are identity assertions, not reconstructed name checks.
                assert_eq!(
                    r.view_exposed_elements(v),
                    vec![y, a],
                    "mode {mode}, first_global={first_global}"
                );
                assert_eq!(global(&mut r), vec![y]);
            }
            assert_eq!(model.loaded_library_unit_count(), loaded);
        }
    }
}

#[test]
fn ordinary_import_projection_and_exposure_share_inherited_survival() {
    for (_, mut r) in models(
        "part def A {part x;} part def D :> A {part y redefines A::x;}",
        "package P {import all D::*;} view v {expose P::*;}",
    ) {
        let d = r.resolve_qualified("D::y").unwrap();
        let p = r.resolve_qualified("P").unwrap();
        let actual: Vec<_> = r
            .imported_memberships(p)
            .into_iter()
            .filter_map(|m| r.membership_member(m))
            .collect();
        assert_eq!(actual, vec![d]);
        let v = r.resolve_qualified("v").unwrap();
        assert_eq!(r.view_exposed_elements(v), vec![d]);
    }
}

#[test]
fn contextual_namespace_pruning_stays_at_the_namespace_result_boundary() {
    for (_, mut r) in models(
        "package A {part x;} package B {part x;}",
        "package P {public import A::*; public import B::*;} view v {expose P::*;}",
    ) {
        let p = r.resolve_qualified("P").unwrap();
        assert!(r.imported_memberships(p).is_empty());
        let a = r.resolve_qualified("A::x").unwrap();
        let b = r.resolve_qualified("B::x").unwrap();
        let v = r.resolve_qualified("v").unwrap();
        assert_eq!(r.view_exposed_elements(v), vec![a, b]);
    }
}

#[test]
fn aliases_remain_distinct_memberships_during_contextual_reduction() {
    check(
        "part def A {part x; alias ax for x;} part def D :> A;",
        "view v {expose D::*;}",
        &[("v", &[])],
    );
}

#[test]
fn contextual_cycles_separate_namespace_from_type_exclusions() {
    check(
        "part def A :> B {part x;} part def B :> A {part y;}",
        "view v {expose A::*;}",
        &[("v", &["A::x", "B::y"])],
    );
    check(
        "package P {package N {part child;} public import D::*;} part def C {public import P::**;} part def D :> C;",
        "view v {expose P::*;}",
        &[("v", &["P::N", "P"])],
    );
}

#[test]
fn layered_diamonds_reuse_equivalent_contexts_without_duplicate_memberships() {
    let mut library = "part def Base {part x;}".to_string();
    let mut last = "Base".to_string();
    for n in 0..24 {
        library.push_str(&format!(
            "part def L{n} :> {last}; part def R{n} :> {last}; part def Join{n} :> L{n},R{n};"
        ));
        last = format!("Join{n}");
    }
    check(
        &library,
        &format!("view v {{expose {last}::*;}}"),
        &[("v", &["Base::x"])],
    );
}

#[test]
fn contextual_projection_preserves_previously_supported_positive_bases() {
    check(
        "part def Frame {part cell {attribute rating;}} part def Housing {part slot : Frame;}",
        "part merged :> Housing::slot.cell; view v {expose merged::*;}",
        &[("v", &["Frame::cell::rating"])],
    );
    check(
        "part def A {part x;}",
        "part def D :> A, Missing; view v {expose D::*;}",
        &[("v", &["A::x"])],
    );
    for (mode, (model, mut r)) in models(
        "package Metaobjects {metadata def SemanticMetadata {attribute baseType;}} package M {metadata def U; part def Target {part member;} metadata def Tagged :> Metaobjects::SemanticMetadata {:>> baseType = Target meta U;} #Tagged part def Annotated;}",
        "view v {expose M::Annotated::*;}",
    ).into_iter().enumerate() {
        let loaded = model.loaded_library_unit_count();
        let annotated = r.resolve_qualified("M::Annotated").unwrap();
        let member = r.resolve_qualified("M::Target::member").unwrap();
        let view = r.resolve_qualified("v").unwrap();
        let mut expected: Vec<_> = r.owned_relationships(annotated).into_iter()
            .filter_map(|relationship| r.membership_member(relationship)).collect();
        // The annotation itself is a legitimate anonymous owned member.
        assert_eq!(expected.len(), 1);
        assert!(r.element_qualified_name(expected[0]).is_none());
        expected.push(member);
        for _ in 0..2 {
            assert_eq!(r.view_exposed_elements(view), expected, "mode {mode}");
        }
        assert_eq!(model.loaded_library_unit_count(), loaded);
    }
}
