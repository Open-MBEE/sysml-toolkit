//! Inherited name selection must agree with stored reference endpoints.
#![cfg(feature = "json")]

use std::sync::Arc;
use sysmlv2_parser::{
    json::{ElementRef, ResolvedModel},
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
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

fn edge(r: &mut ResolvedModel, owner: &str, kind: &str) -> ElementRef {
    let e = r.resolve_qualified(owner).unwrap();
    r.owned_relationships(e)
        .into_iter()
        .find(|&e| r.element_type(e) == kind)
        .unwrap()
}

fn endpoint(r: &mut ResolvedModel, owner: &str, kind: &str, property: &str, target: Option<&str>) {
    let e = edge(r, owner, kind);
    let value = r.element_properties(e);
    match target {
        Some(name) => {
            let target = r.resolve_qualified(name).unwrap();
            assert_eq!(
                value[property]["@id"],
                r.element_id(target).to_string(),
                "{owner}"
            );
            // Library sites are deliberately absent from reference-site records.
            if !r.is_library_element(e) {
                assert!(
                    r.reference_sites()
                        .iter()
                        .any(|s| { s.owner == e && s.kind == property && s.target == target }),
                    "missing reference site for {owner}"
                );
            }
        }
        None => {
            assert!(value[property]["@ref"].is_string(), "{owner}: {value:?}");
            assert!(
                !r.reference_sites()
                    .iter()
                    .any(|s| s.owner == e && s.kind == property)
            );
            assert!(r.unresolved_references().iter().any(|s| s.owner == e));
        }
    }
}

#[test]
fn distinct_feature_memberships_are_removed_before_lookup_and_binding() {
    let library = "class Base { feature x; alias ax for x; } class Child specializes Base;";
    let user = "feature useX subsets Child::x; feature useAlias references Child::ax;";
    for mut r in models(library, user) {
        for warm in [false, true] {
            if warm {
                let child = r.resolve_qualified("Child").unwrap();
                assert!(r.inherited_memberships(child, false).is_empty());
            }
            assert_eq!(r.resolve_qualified("Child::x"), None);
            assert_eq!(r.resolve_qualified("Child::ax"), None);
            endpoint(&mut r, "useX", "Subsetting", "subsettedFeature", None);
            endpoint(
                &mut r,
                "useAlias",
                "ReferenceSubsetting",
                "referencedFeature",
                None,
            );
        }
    }
}

#[test]
fn redefinitions_under_other_names_remove_inherited_lookup_candidates() {
    for library in [
        "class A { feature x; } class B specializes A { feature y redefines A::x; } class Child specializes A, B;",
        "class Child specializes A, B; class B specializes A { feature y redefines A::x; } class A { feature x; }",
    ] {
        for mut r in models(
            library,
            "feature gone subsets Child::x; feature kept subsets Child::y;",
        ) {
            assert_eq!(r.resolve_qualified("Child::x"), None);
            let y = r.resolve_qualified("B::y").unwrap();
            assert_eq!(r.resolve_qualified("Child::y"), Some(y));
            endpoint(&mut r, "gone", "Subsetting", "subsettedFeature", None);
            endpoint(
                &mut r,
                "kept",
                "Subsetting",
                "subsettedFeature",
                Some("B::y"),
            );
        }
    }
}

#[test]
fn descendant_filtering_can_recover_a_candidate_from_ancestor_ambiguity() {
    let library = "class A { feature x; } class B { feature x; }
        class Mid specializes A, B;
        class Child specializes Mid { feature z redefines A::x; }";
    for mut r in models(library, "feature selected subsets Child::x;") {
        assert_eq!(r.resolve_qualified("Mid::x"), None);
        let x = r.resolve_qualified("B::x").unwrap();
        assert_eq!(r.resolve_qualified("Child::x"), Some(x));
        endpoint(
            &mut r,
            "selected",
            "Subsetting",
            "subsettedFeature",
            Some("B::x"),
        );
        endpoint(
            &mut r,
            "Child::z",
            "Redefinition",
            "redefinedFeature",
            Some("A::x"),
        );
    }
}

#[test]
fn redefinition_headers_keep_their_inherited_target_on_replay() {
    let library = "class Base { feature x; }";
    for user in [
        "class Child specializes Base { feature y redefines x; feature z redefines x; feature use references x; }",
        "class Child specializes Base { feature use references x; feature z redefines x; feature y redefines x; }",
    ] {
        for mut r in models(library, user) {
            for name in ["Child::y", "Child::z"] {
                endpoint(
                    &mut r,
                    name,
                    "Redefinition",
                    "redefinedFeature",
                    Some("Base::x"),
                );
            }
            assert_eq!(r.resolve_qualified("Child::x"), None);
            endpoint(
                &mut r,
                "Child::use",
                "ReferenceSubsetting",
                "referencedFeature",
                None,
            );
        }
    }
}

#[test]
fn alias_visibility_applies_to_the_membership_instead_of_its_target() {
    let library = "class PublicAlias { private feature x; alias ax for x; }
        class PrivateAlias { feature x; private alias ax for x; }
        class A specializes PublicAlias;
        class B specializes PrivateAlias;";
    for mut r in models(library, "feature a subsets A::ax; feature b subsets B::x;") {
        let ax = r.resolve_qualified("PublicAlias::x").unwrap();
        let bx = r.resolve_qualified("PrivateAlias::x").unwrap();
        assert_eq!(r.resolve_qualified("A::ax"), Some(ax));
        assert_eq!(r.resolve_qualified("A::x"), None);
        assert_eq!(r.resolve_qualified("B::x"), Some(bx));
        assert_eq!(r.resolve_qualified("B::ax"), None);
        endpoint(
            &mut r,
            "a",
            "Subsetting",
            "subsettedFeature",
            Some("PublicAlias::x"),
        );
        endpoint(
            &mut r,
            "b",
            "Subsetting",
            "subsettedFeature",
            Some("PrivateAlias::x"),
        );
    }
}

#[test]
fn a_shared_alias_identity_survives_a_diamond_but_distinct_aliases_do_not() {
    let library = "class Values { feature x; }
        class Base { alias ax for Values::x; }
        class Left specializes Base; class Right specializes Base;
        class Shared specializes Left, Right;
        class Other { alias bx for Values::x; }
        class Distinct specializes Base, Other;";
    for mut r in models(
        library,
        "feature a subsets Shared::ax; feature b subsets Distinct::ax;",
    ) {
        let x = r.resolve_qualified("Values::x").unwrap();
        assert_eq!(r.resolve_qualified("Shared::ax"), Some(x));
        assert_eq!(r.resolve_qualified("Distinct::ax"), None);
        assert_eq!(r.resolve_qualified("Distinct::bx"), None);
        endpoint(
            &mut r,
            "a",
            "Subsetting",
            "subsettedFeature",
            Some("Values::x"),
        );
        endpoint(&mut r, "b", "Subsetting", "subsettedFeature", None);
    }
}

#[test]
fn library_origin_references_use_the_same_selection_after_cache_replay() {
    let library = "feature before references Child::ax;
        class Base { feature x; alias ax for x; }
        class Child specializes Base;
        feature after subsets Child::x;";
    for mut r in models(library, "feature userReference references Child::ax;") {
        endpoint(
            &mut r,
            "before",
            "ReferenceSubsetting",
            "referencedFeature",
            None,
        );
        endpoint(&mut r, "after", "Subsetting", "subsettedFeature", None);
        endpoint(
            &mut r,
            "userReference",
            "ReferenceSubsetting",
            "referencedFeature",
            None,
        );
    }
}

#[test]
fn identity_overrides_preserve_cached_membership_selection_and_reference_endpoints() {
    let library = "class Base { feature x; alias ax for x; feature safe; }
        class Child specializes Base;";
    for mut r in models(
        library,
        "feature gone subsets Child::ax; feature kept subsets Child::safe;",
    ) {
        let child = r.resolve_qualified("Child").unwrap();
        r.inherited_memberships(child, true);
        r.resolve_qualified("Child::safe");
        let x = r.resolve_qualified("Base::x").unwrap();
        let safe = r.resolve_qualified("Base::safe").unwrap();
        let replacement = uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"lookup target override");
        let replacement_safe =
            uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"lookup safe override");
        r.override_ids(&std::collections::HashMap::from([
            (r.element_id(x), replacement),
            (r.element_id(safe), replacement_safe),
        ]));
        assert_eq!(r.resolve_qualified("Child::x"), None);
        assert_eq!(r.resolve_qualified("Child::ax"), None);
        assert_eq!(r.resolve_qualified("Child::safe"), Some(safe));
        endpoint(&mut r, "gone", "Subsetting", "subsettedFeature", None);
        endpoint(
            &mut r,
            "kept",
            "Subsetting",
            "subsettedFeature",
            Some("Base::safe"),
        );
    }
}

#[test]
fn unknown_and_cyclic_dependencies_remain_qualified_without_losing_known_members() {
    let library = "class Base { feature x; alias unknown for Missing; }
        class Child specializes Base;
        class A specializes B { feature a; } class B specializes A;";
    for mut r in models(
        library,
        "feature useX subsets Child::x; feature useA subsets B::a;",
    ) {
        let child = r.resolve_qualified("Child").unwrap();
        let b = r.resolve_qualified("B").unwrap();
        assert!(r.inheritance_incomplete(child, false));
        assert!(r.inheritance_incomplete(b, false));
        endpoint(
            &mut r,
            "useX",
            "Subsetting",
            "subsettedFeature",
            Some("Base::x"),
        );
        endpoint(
            &mut r,
            "useA",
            "Subsetting",
            "subsettedFeature",
            Some("A::a"),
        );
    }
}

#[test]
fn user_completion_rechecks_library_references_that_depend_on_alias_membership() {
    let library = "class Base { feature x; alias ax for Future::x; }
        class Child specializes Base;
        feature libraryReference references Child::x;";
    for mut r in models(
        library,
        "class Future { alias x for Base::x; } feature userReference references Child::ax;",
    ) {
        assert_eq!(r.resolve_qualified("Child::x"), None);
        assert_eq!(r.resolve_qualified("Child::ax"), None);
        endpoint(
            &mut r,
            "libraryReference",
            "ReferenceSubsetting",
            "referencedFeature",
            None,
        );
        endpoint(
            &mut r,
            "userReference",
            "ReferenceSubsetting",
            "referencedFeature",
            None,
        );
    }
    let library = "class Base { alias ax for Future::x; }
        class Child specializes Base;
        feature libraryReference references Child::ax;";
    for mut r in models(library, "class Future { feature x; }") {
        endpoint(
            &mut r,
            "libraryReference",
            "ReferenceSubsetting",
            "referencedFeature",
            Some("Future::x"),
        );
    }
}

#[test]
fn an_actual_self_redefinition_does_not_remove_its_only_membership() {
    let target_id = uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"self redefinition target");
    let mut model = Model::new();
    model.add_source(
        "self.kerml",
        &format!(
            "assoc SelfCycle {{ end feature x redefines '{target_id}'; }}
             assoc Child specializes SelfCycle {{ end feature slot; }}"
        ),
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let x = r.resolve_qualified("SelfCycle::x").unwrap();
    let child = r.resolve_qualified("Child").unwrap();
    let _ = r.inherited_memberships(child, false);
    r.override_ids(&std::collections::HashMap::from([(
        r.element_id(x),
        target_id,
    )]));
    assert!(r.bind_id_spelled_references().contains(&target_id));
    let relation = edge(&mut r, "SelfCycle::x", "Redefinition");
    assert_eq!(
        r.element_properties(relation)["redefinedFeature"]["@id"],
        target_id.to_string(),
        "the fixture must contain a resolved self-edge"
    );
    assert_eq!(r.inherited_memberships(child, false).len(), 1);
    assert_eq!(r.resolve_qualified("Child::x"), Some(x));
    let slot = r.resolve_qualified("Child::slot").unwrap();
    let targets: Vec<_> = r
        .implied_relationships(slot)
        .into_iter()
        .filter(|&edge| r.element_type(edge) == "Redefinition")
        .map(|edge| r.element_properties(edge)["redefinedFeature"]["@id"].clone())
        .collect();
    assert_eq!(targets, [serde_json::json!(target_id.to_string())]);
}

#[test]
fn redefinition_targets_start_in_direct_bases_before_declaring_type_locals() {
    for (bases, local) in [("A, B", ""), ("B, A", ""), ("A", "feature x;")] {
        let library = "class A { feature x; } class B { feature x; }";
        let user = format!("class Child specializes {bases} {{ {local} feature y redefines x; }}");
        for mut r in models(library, &user) {
            endpoint(
                &mut r,
                "Child::y",
                "Redefinition",
                "redefinedFeature",
                Some(if bases.starts_with('A') {
                    "A::x"
                } else {
                    "B::x"
                }),
            );
            let remaining = r.resolve_qualified("Child::x").unwrap();
            if bases == "A" {
                let child = r.resolve_qualified("Child").unwrap();
                assert!(r.owned_features(child).contains(&remaining));
            } else {
                let unselected = if bases.starts_with('A') {
                    "B::x"
                } else {
                    "A::x"
                };
                assert_eq!(Some(remaining), r.resolve_qualified(unselected));
            }
        }
    }
}

#[test]
fn inherited_effective_names_retain_the_unnamed_redefining_feature() {
    for mut r in models(
        "class Base { feature x; }",
        "class Mid specializes Base { feature redefines x; }
         class Child specializes Mid; feature useX references Child::x;",
    ) {
        let inherited = r.resolve_qualified("Child::x").unwrap();
        let original = r.resolve_qualified("Base::x").unwrap();
        assert_ne!(inherited, original);
        let mid = r.resolve_qualified("Mid").unwrap();
        assert!(r.owned_features(mid).contains(&inherited));
        endpoint(
            &mut r,
            "useX",
            "ReferenceSubsetting",
            "referencedFeature",
            Some("Child::x"),
        );
    }
}

#[test]
fn unstable_reference_dependencies_restore_a_consistent_qualified_result() {
    let library = "class A { feature x; }
        class B specializes A { feature y redefines C::x; }
        class C specializes A, B;
        feature libraryReference references C::x;";
    for mut r in models(library, "feature userReference references C::x;") {
        let c = r.resolve_qualified("C").unwrap();
        assert!(r.inheritance_incomplete(c, false));
        // The contextual bootstrap consistently binds all three endpoints.
        // Never expose endpoints or diagnostics from an arbitrary replay pass.
        for (owner, kind, property) in [
            ("B::y", "Redefinition", "redefinedFeature"),
            (
                "libraryReference",
                "ReferenceSubsetting",
                "referencedFeature",
            ),
            ("userReference", "ReferenceSubsetting", "referencedFeature"),
        ] {
            endpoint(&mut r, owner, kind, property, Some("A::x"));
        }
        assert_eq!(r.resolve_qualified("C::x"), r.resolve_qualified("A::x"));
        assert!(r.unresolved_references().is_empty());
    }
}

#[test]
fn replay_preserves_ambiguity_and_missing_diagnostic_categories() {
    let library = "class A { feature x; } class B { feature x; }
        class Mid specializes A, B;
        class Child specializes Mid { feature z redefines A::x; }
        feature libraryAmbiguous references Mid::x;";
    let user = "feature ambiguousUse references Mid::x;
        feature missingUse references Child::absent;
        feature resolvedUse references Child::x;";
    for model in source_models(library, user) {
        let report = sysmlv2_parser::json::model_resolution_report(&model);
        let ambiguous: Vec<_> = report
            .ambiguous
            .iter()
            .map(|(unit, qn)| (*unit, qn.to_ref_string()))
            .collect();
        assert_eq!(ambiguous, [(0, "Mid::x".into()), (1, "Mid::x".into())]);
        assert!(
            report
                .unresolved
                .iter()
                .any(|(unit, qn)| { *unit == 1 && qn.to_ref_string() == "Child::absent" })
        );
        assert!(
            !report
                .unresolved
                .iter()
                .any(|(_, qn)| qn.to_ref_string() == "Child::x")
        );
    }
}

#[test]
fn global_redefinition_targets_still_require_a_direct_base_starting_context() {
    for mut r in models(
        "class A { feature x; }",
        "class C { feature y redefines $::A::x; }
         class D specializes A { feature y redefines $::A::x; }",
    ) {
        endpoint(&mut r, "C::y", "Redefinition", "redefinedFeature", None);
        endpoint(
            &mut r,
            "D::y",
            "Redefinition",
            "redefinedFeature",
            Some("A::x"),
        );
    }
}

#[test]
fn inherited_aliases_preserve_import_provenance_from_enclosing_namespaces() {
    let library = "package Q { feature importedFeature; }
        package P { private import Q::*;
            class Base { alias ax for importedFeature; }
            class Child specializes Base;
        }";
    for mut r in models(library, "feature useAlias references P::Child::ax;") {
        endpoint(
            &mut r,
            "useAlias",
            "ReferenceSubsetting",
            "referencedFeature",
            Some("Q::importedFeature"),
        );
        let reference = edge(&mut r, "useAlias", "ReferenceSubsetting");
        let import = edge(&mut r, "P", "NamespaceImport");
        let site = r
            .reference_sites()
            .iter()
            .find(|s| s.owner == reference && s.kind == "referencedFeature")
            .unwrap();
        assert!(site.via_imports.iter().any(|&(e, _)| e == import));
        assert!(r.unresolved_references().is_empty());
    }
}

#[test]
fn imported_explicit_bases_filter_names_without_inheriting_import_walks() {
    let library = "package Lib {
        class A { feature x; }
        class B specializes A { feature y redefines x; }
    }";
    for imports in [
        "private import Lib::*;",
        "private import Lib::A; private import Lib::B;",
    ] {
        let user = format!(
            "package P {{ {imports} package Nested {{
                class Child specializes A, B;
                feature useX references Child::x;
                feature useY references Child::y;
            }} }}"
        );
        for mut r in models(library, &user) {
            endpoint(
                &mut r,
                "P::Nested::useX",
                "ReferenceSubsetting",
                "referencedFeature",
                None,
            );
            endpoint(
                &mut r,
                "P::Nested::useY",
                "ReferenceSubsetting",
                "referencedFeature",
                Some("Lib::B::y"),
            );
            for warm in [false, true] {
                let child = r.resolve_qualified("P::Nested::Child").unwrap();
                if warm {
                    let _ = r.inherited_memberships(child, false);
                }
                assert_eq!(r.resolve_qualified("P::Nested::Child::x"), None);
                let y = r.resolve_qualified("Lib::B::y").unwrap();
                assert_eq!(r.resolve_qualified("P::Nested::Child::y"), Some(y));
            }
            let child = r.resolve_qualified("P::Nested::Child").unwrap();
            for relation in r.owned_relationships(child) {
                if r.element_type(relation) != "Subclassification" {
                    continue;
                }
                let site = r
                    .reference_sites()
                    .iter()
                    .find(|s| s.owner == relation && s.kind == "superclassifier")
                    .unwrap();
                assert_eq!(site.via_imports.len(), 1);
                assert_eq!(site.via_imports[0].1, sysmlv2_parser::json::AccessMode::Any);
                assert!(r.element_type(site.via_imports[0].0).ends_with("Import"));
            }
            let use_y = edge(&mut r, "P::Nested::useY", "ReferenceSubsetting");
            let site = r
                .reference_sites()
                .iter()
                .find(|s| s.owner == use_y && s.kind == "referencedFeature")
                .unwrap();
            assert!(
                site.via_imports.is_empty(),
                "base binding imports belong only to the specialization"
            );
            assert!(r.blocked_references().is_empty());
        }
    }
}

#[test]
fn imported_base_redefinition_headers_ignore_declaring_type_shadowing() {
    for mut r in models(
        "package Lib { class Base { feature x; } }",
        "package P { private import Lib::*;
            class Child specializes Base { feature x; feature y redefines x; }
        }",
    ) {
        endpoint(
            &mut r,
            "P::Child::y",
            "Redefinition",
            "redefinedFeature",
            Some("Lib::Base::x"),
        );
        let edge = edge(&mut r, "P::Child::y", "Redefinition");
        let site = r
            .reference_sites()
            .iter()
            .find(|s| s.owner == edge && s.kind == "redefinedFeature")
            .unwrap();
        assert!(site.via_imports.is_empty());
        assert!(r.unresolved_references().is_empty());
    }
}

#[test]
fn qualified_alias_targets_preserve_import_walks_outside_lexical_ancestors() {
    for target in ["Exposed::x", "$::Exposed::x", "Intermediate::ax"] {
        let library = format!(
            "package Q {{ feature x; }}
            package Exposed {{ public import Q::*; }}
            class Intermediate {{ alias ax for Exposed::x; }}
            class Base {{ alias ax for {target}; }}
            class Mid specializes Base;
            class Child specializes Mid;"
        );
        for mut r in models(&library, "feature selected references Child::ax;") {
            endpoint(
                &mut r,
                "selected",
                "ReferenceSubsetting",
                "referencedFeature",
                Some("Q::x"),
            );
            let import = edge(&mut r, "Exposed", "NamespaceImport");
            let relation = edge(&mut r, "selected", "ReferenceSubsetting");
            let site = r
                .reference_sites()
                .iter()
                .find(|s| s.owner == relation && s.kind == "referencedFeature")
                .unwrap();
            assert_eq!(
                site.via_imports,
                [(import, sysmlv2_parser::json::AccessMode::Public)],
                "{target}"
            );
            let child = r.resolve_qualified("Child").unwrap();
            let _ = r.inherited_memberships(child, false);
            let expected = r.resolve_qualified("Q::x").unwrap();
            assert_eq!(r.resolve_qualified("Child::ax"), Some(expected));
        }
    }
}

#[test]
fn imports_in_base_bodies_keep_their_actual_member_access_walks() {
    for visibility in ["public", "protected"] {
        let library = format!(
            "package Q {{ feature x; }}
            class Base {{ {visibility} import Q::*; }}
            class Child specializes Base;"
        );
        for mut r in models(
            &library,
            "class User specializes Child { feature selected references x; }",
        ) {
            endpoint(
                &mut r,
                "User::selected",
                "ReferenceSubsetting",
                "referencedFeature",
                Some("Q::x"),
            );
            let import = edge(&mut r, "Base", "NamespaceImport");
            let relation = edge(&mut r, "User::selected", "ReferenceSubsetting");
            let site = r
                .reference_sites()
                .iter()
                .find(|s| s.owner == relation && s.kind == "referencedFeature")
                .unwrap();
            assert_eq!(
                site.via_imports,
                [(import, sysmlv2_parser::json::AccessMode::Protected)]
            );
        }
    }
}

#[test]
fn suppressed_inheritance_cannot_certify_an_alias_lexical_fallback() {
    let library = "package Q { feature x; }
        class A { alias ax for Q::x; alias bx for Q::x; }
        package P { private import A::*;
            class B specializes A { class AliasOwner { alias selected for ax; } }
        }
        class Child specializes P::B::AliasOwner;";
    for mut r in models(library, "feature selected references Child::selected;") {
        endpoint(
            &mut r,
            "selected",
            "ReferenceSubsetting",
            "referencedFeature",
            Some("Q::x"),
        );
        let import = edge(&mut r, "P", "NamespaceImport");
        let relation = edge(&mut r, "selected", "ReferenceSubsetting");
        let site = r
            .reference_sites()
            .iter()
            .find(|s| s.owner == relation && s.kind == "referencedFeature")
            .unwrap();
        assert_eq!(
            site.via_imports,
            [(import, sysmlv2_parser::json::AccessMode::Any)]
        );
    }
}

#[test]
fn positional_header_contexts_try_written_bases_in_order() {
    let library = "class Transfer { end feature source; end feature target; }
        feature transfers : Transfer { end feature source redefines Transfer::source;
            end feature target redefines Transfer::target; }
        ";
    let user = "feature incoming : Transfer subsets transfers {
        end feature source redefines source;
        end feature target redefines target;
    }";
    for mut r in models(library, user) {
        for name in ["source", "target"] {
            endpoint(
                &mut r,
                &format!("incoming::{name}"),
                "Redefinition",
                "redefinedFeature",
                Some(&format!("Transfer::{name}")),
            );
        }
    }
}

#[test]
fn redefinition_before_typing_is_the_first_header_context() {
    let library = "class Anything { feature self; }
        class Port specializes Anything { feature self redefines Anything::self; }
        class Link { feature participant : Anything; }";
    let user = "class Interface specializes Link {
        feature participant redefines participant : Port {
            feature thisParticipant redefines self;
        }
    }";
    for mut r in models(library, user) {
        endpoint(
            &mut r,
            "Interface::participant::thisParticipant",
            "Redefinition",
            "redefinedFeature",
            Some("Anything::self"),
        );
    }
}

#[test]
fn header_without_a_general_does_not_depend_on_unrelated_heritage() {
    for mut r in models(
        "class A { feature x; }",
        "class C { feature y redefines $::A::x; }",
    ) {
        endpoint(&mut r, "C::y", "Redefinition", "redefinedFeature", None);
    }
}

#[test]
fn header_full_resolution_in_an_earlier_general_precedes_later_typing() {
    let library = "package Quantities { feature width; }
        package P { private import Quantities::*;
            class First;
            class Second { feature width; }
        }";
    let user = "class Child specializes P::First, P::Second {
        feature dimension redefines width;
    }";
    for mut r in models(library, user) {
        endpoint(
            &mut r,
            "Child::dimension",
            "Redefinition",
            "redefinedFeature",
            Some("Quantities::width"),
        );
        let relation = edge(&mut r, "Child::dimension", "Redefinition");
        let site = r
            .reference_sites()
            .iter()
            .find(|site| site.owner == relation && site.kind == "redefinedFeature")
            .unwrap();
        assert_eq!(site.via_imports.len(), 1);
    }
}

#[test]
fn anonymous_chain_redefinitions_do_not_capture_a_leaf_name() {
    let library = "package Measures { feature mass; }
        class Vehicle { feature chassis { feature mass = 1; } }
        class Anonymous specializes Vehicle { feature redefines chassis.mass = 2; }
        class Named specializes Vehicle { feature mass redefines chassis.mass = 2; }";
    let user = "package P {
        private import Measures::*;
        class A specializes Anonymous { feature redefines mass = 3; }
        class N specializes Named { feature redefines mass = 3; }
    }";
    for mut r in models(library, user) {
        assert!(r.resolve_qualified("Anonymous::mass").is_none());
        endpoint(
            &mut r,
            "P::A::mass",
            "Redefinition",
            "redefinedFeature",
            Some("Measures::mass"),
        );
        endpoint(
            &mut r,
            "P::N::mass",
            "Redefinition",
            "redefinedFeature",
            Some("Named::mass"),
        );
    }
}
