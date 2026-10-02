//! Import-free alias paths retain Membership selection without losing provenance.
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
fn qualified_alias_paths_retain_import_walks() {
    for target in ["Exposed::x", "$::Exposed::x", "Intermediate::forwarded"] {
        let library = format!(
            "package Q {{ feature x; }}
            package Exposed {{ public import Q::*; }}
            package Intermediate {{ alias forwarded for Exposed::x; }}
            class Base {{ alias ax for {target}; }}
            class Child specializes Base;"
        );
        for mut r in models(&library, "feature useAlias references Child::ax;") {
            let x = r.resolve_qualified("Q::x").unwrap();
            assert_eq!(r.resolve_qualified("Child::ax"), Some(x));
            let exposed = r.resolve_qualified("Exposed").unwrap();
            let import = r
                .owned_relationships(exposed)
                .into_iter()
                .find(|&e| r.element_type(e) == "NamespaceImport")
                .unwrap();
            let selected = r.resolve_qualified("useAlias").unwrap();
            let relation = r
                .owned_relationships(selected)
                .into_iter()
                .find(|&e| r.element_type(e) == "ReferenceSubsetting")
                .unwrap();
            assert_eq!(
                r.element_properties(relation)["referencedFeature"]["@id"],
                r.element_id(x).to_string()
            );
            let site = r
                .reference_sites()
                .iter()
                .find(|site| site.owner == relation && site.kind == "referencedFeature")
                .unwrap();
            assert_eq!(
                site.via_imports,
                vec![(import, sysmlv2_parser::json::AccessMode::Public)]
            );
            assert!(r.unresolved_references().is_empty());
        }
    }
}

#[test]
fn pure_alias_chains_keep_membership_suppression() {
    for aliases in [
        "feature x; alias ax for x; alias bx for ax;",
        "feature <x> x; alias ax for x; alias bx for ax;",
        "private feature x; alias ax for Base::x; alias bx for ax;",
        "private feature x; alias ax for $::Base::x; alias bx for Base::ax;",
    ] {
        let library = format!("class Base {{ {aliases} }} class Child specializes Base;");
        for mut r in models(&library, "feature useAlias references Child::bx;") {
            for name in ["Child::ax", "Child::bx"] {
                assert_eq!(r.resolve_qualified(name), None, "{name} in {aliases}");
            }
            let child = r.resolve_qualified("Child").unwrap();
            assert!(r.inherited_memberships(child, false).is_empty());
            let selected = r.resolve_qualified("useAlias").unwrap();
            let relation = r
                .owned_relationships(selected)
                .into_iter()
                .find(|&e| r.element_type(e) == "ReferenceSubsetting")
                .unwrap();
            assert_eq!(
                r.element_properties(relation)["referencedFeature"]["@ref"],
                "Child::bx"
            );
        }
    }
}

#[test]
fn unrelated_ancestor_imports_do_not_disqualify_local_aliases() {
    let library = "package Unrelated { feature other; }
        package P { private import Unrelated::*;
            class Base { feature x; alias ax for x; alias bx for ax; }
            class Child specializes Base;
        }";
    for mut r in models(library, "feature useAlias references P::Child::ax;") {
        assert_eq!(r.resolve_qualified("P::Child::x"), None);
        assert_eq!(r.resolve_qualified("P::Child::ax"), None);
        assert_eq!(r.resolve_qualified("P::Child::bx"), None);
    }
}

#[test]
fn aliases_to_inherited_and_effective_bindings_remain_filtered() {
    for member in ["", "feature redefines x;"] {
        let library = format!(
            "class A {{ feature x; }} class B specializes A {{ {member} }}
            class Base {{ alias ax for B::x; alias bx for B::x; }}
            class Child specializes Base;"
        );
        for mut r in models(&library, "feature useAlias references Child::ax;") {
            assert!(r.resolve_qualified("B::x").is_some());
            assert_eq!(r.resolve_qualified("Child::ax"), None);
            assert_eq!(r.resolve_qualified("Child::bx"), None);
        }
    }
}

#[test]
fn alias_certificates_use_filtered_multiple_inheritance() {
    let library = "class A { feature x; }
        class B specializes A { feature x redefines x; }
        class Combined specializes A, B;
        class Base { alias ax for Combined::x; alias bx for Combined::x; }
        class Child specializes Base;";
    for mut r in models(library, "feature useAlias references Child::ax;") {
        let x = r.resolve_qualified("B::x").unwrap();
        assert_eq!(r.resolve_qualified("Combined::x"), Some(x));
        assert_eq!(r.resolve_qualified("Child::ax"), None);
        assert_eq!(r.resolve_qualified("Child::bx"), None);
    }
}

#[test]
fn qualified_protected_alias_targets_keep_inherited_membership_filtering() {
    let library = "class A { protected feature x; }
        class Base specializes A { alias ax for A::x; alias bx for A::x; }
        class Child specializes Base;";
    for mut r in models(library, "feature useAlias references Child::ax;") {
        assert!(r.resolve_qualified("Base::ax").is_some());
        assert_eq!(r.resolve_qualified("Child::ax"), None);
        assert_eq!(r.resolve_qualified("Child::bx"), None);
    }
}
