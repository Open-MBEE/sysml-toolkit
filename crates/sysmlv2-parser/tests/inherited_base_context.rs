//! Derived base scopes retain the target selected by a redefinition header.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};

fn models(library: &str, user: &str) -> Vec<ResolvedModel> {
    source_models(library, user)
        .iter()
        .map(ResolvedModel::build)
        .collect()
}

fn source_models(library: &str, user: &str) -> Vec<Model> {
    let mut base = Model::new();
    base.add_library_source("lookup.kerml", library);
    assert!(!base.has_errors());
    base.record_library_cache();
    let _ = ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(23).unwrap(), 23).unwrap());
    (0..4)
        .map(|mode| {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("lookup.kerml", library);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            model.add_source("user.kerml", user);
            assert!(!model.has_errors());
            model
        })
        .collect()
}

#[test]
fn redefining_features_inherit_members_from_their_suppressed_target() {
    let library = "package Lib { class Base { feature x[2..4] { feature leaf; } } }";
    let user = "package P { private import Lib::*;
        class Child specializes Base { feature y redefines x; }
        feature useMember references Child::y::leaf;
    }";
    for mut r in models(library, user) {
        let base = r.resolve_qualified("Lib::Base::x").unwrap();
        let member = r.resolve_qualified("Lib::Base::x::leaf").unwrap();
        let derived = r.resolve_qualified("P::Child::y").unwrap();
        assert_eq!(r.resolve_qualified("P::Child::x"), None);
        assert_eq!(r.resolve_qualified("P::Child::y::leaf"), Some(member));
        let expected: Vec<_> = r
            .owned_relationships(base)
            .into_iter()
            .filter(|&e| r.membership_member(e).is_some())
            .collect();
        assert!(expected.iter().any(|&e| {
            let target = r.membership_member(e).unwrap();
            r.element_type(target) == "MultiplicityRange"
        }));
        for implied in [false, true] {
            assert_eq!(r.inherited_memberships(derived, implied), expected);
        }
        let relation = r
            .owned_relationships(derived)
            .into_iter()
            .find(|&e| r.element_type(e) == "Redefinition")
            .unwrap();
        assert_eq!(
            r.element_properties(relation)["redefinedFeature"]["@id"],
            r.element_id(base).to_string()
        );
        let selected = r.resolve_qualified("P::useMember").unwrap();
        let reference = r
            .owned_relationships(selected)
            .into_iter()
            .find(|&e| r.element_type(e) == "ReferenceSubsetting")
            .unwrap();
        assert_eq!(
            r.element_properties(reference)["referencedFeature"]["@id"],
            r.element_id(member).to_string()
        );
        let site = r
            .reference_sites()
            .iter()
            .find(|s| s.owner == reference)
            .unwrap();
        assert!(site.via_imports.is_empty());
    }
}
