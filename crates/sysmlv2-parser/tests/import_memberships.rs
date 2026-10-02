//! Imported Membership identity is distinct from the element its name denotes.
#![cfg(feature = "json")]

use std::sync::Arc;
use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, DerivedValue, ElementRef, Reference, ResolvedModel},
    libcache::LibraryCache,
    model::Model,
    prepared::PreparedLibrary,
};

fn models(library: &str, user: &str) -> Vec<ResolvedModel> {
    let mut base = Model::new();
    base.add_library_source("library.kerml", library);
    assert!(!base.has_errors());
    base.record_library_cache();
    let _ = ResolvedModel::build(&base);
    let cache = base.take_recorded_library_cache().unwrap();
    let cache = LibraryCache::from_bytes(&cache.to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let prepared =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(7).unwrap(), 7).unwrap());
    (0..3)
        .map(|mode| {
            let mut model = Model::new();
            if mode == 2 {
                prepared.clone().install(&mut model).unwrap();
            } else {
                model.add_library_source("library.kerml", library);
                if mode == 1 {
                    model.set_library_cache(cache.clone());
                }
            }
            model.add_source("user.kerml", user);
            assert!(
                !model.has_errors(),
                "{:?}",
                model
                    .units()
                    .iter()
                    .flat_map(|u| &u.diagnostics)
                    .collect::<Vec<_>>()
            );
            ResolvedModel::build(&model)
        })
        .collect()
}

fn many(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Vec<ElementRef> {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::Elements(v)) => v,
        other => panic!("{name}: {other:?}"),
    }
}

fn one(r: &mut ResolvedModel, e: ElementRef, name: &str) -> ElementRef {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::Element(e))
        | Derived::Value(DerivedValue::Reference(Reference::Element(e))) => e,
        Derived::NotDeclared => {
            let value = r.element_properties(e);
            let id = value[name]["@id"].as_str().unwrap();
            r.element_by_id(id).unwrap()
        }
        other => panic!("{name}: {other:?}"),
    }
}

fn alias(r: &mut ResolvedModel, scope: &str, name: &str) -> ElementRef {
    let owner = r.resolve_qualified(scope).unwrap();
    many(r, owner, "ownedMembership")
        .into_iter()
        .find(|&m| r.membership_is_alias(m) && r.membership_member_name(m).as_deref() == Some(name))
        .unwrap()
}

#[test]
fn named_imports_preserve_alias_membership_through_reexports_and_qualification() {
    let library = "package L {
        class T { feature x; }
        alias A for T; alias B for T;
    }
    package Bridge { public import L::A; public import L::B; }
    package Wild { public import Bridge::*; }
    package Named { public import Wild::A; }
    ";
    let user = "package U { private import Named::A; private import Wild::B; }
        package Child { private import L::A::x; }
        package Both { private import L::T; private import L::A; private import L::B; }
        package Renamed { alias C for Wild::A; }
        package Last { private import Renamed::C; }
        class Base { public import L::A; } class Derived :> Base;";
    for mut r in models(library, user) {
        let a = alias(&mut r, "L", "A");
        let b = alias(&mut r, "L", "B");
        let t = r.resolve_qualified("L::T").unwrap();
        let home = one(&mut r, t, "owningMembership");
        for name in ["U", "Bridge", "Wild"] {
            let owner = r.resolve_qualified(name).unwrap();
            assert_eq!(r.imported_memberships(owner), [a, b], "{name}");
        }
        for name in ["U", "Bridge", "Named"] {
            let owner = r.resolve_qualified(name).unwrap();
            let imports = many(&mut r, owner, "ownedImport");
            assert_eq!(one(&mut r, imports[0], "importedMembership"), a, "{name}");
            assert_eq!(one(&mut r, imports[0], "importedElement"), t);
        }
        let owner = r.resolve_qualified("Both").unwrap();
        assert_eq!(r.imported_memberships(owner), [home, a, b]);
        let child = r.resolve_qualified("Child").unwrap();
        let x = r.resolve_qualified("L::T::x").unwrap();
        let xm = one(&mut r, x, "owningMembership");
        assert_eq!(
            r.imported_memberships(child),
            [xm],
            "qualifier alias must not replace final membership"
        );
        let c = alias(&mut r, "Renamed", "C");
        let last = r.resolve_qualified("Last").unwrap();
        assert_eq!(r.imported_memberships(last), [c], "last named alias wins");
        let derived = r.resolve_qualified("Derived").unwrap();
        assert_eq!(r.inherited_memberships(derived, false), [a]);
        assert_eq!(
            r.resolve_qualified("U::A"),
            Some(t),
            "ordinary lookup still returns element"
        );
    }
}

#[test]
fn cycles_exclude_the_import_owner_without_suppressing_independent_filtered_paths() {
    let library = "package A { class Own; public import B::*; }
        package B { class Other; public import all A::*; }
        package Self { class Local; public import Self::*; }
        package Leaf { class Item; }
        package Filtered { public import Leaf::*[false]; }
        package Open { public import Leaf::*[true]; }";
    let user = "package U { private import Filtered::*; private import Open::*; }
        package V { private import Open::*; private import Filtered::*; }";
    for mut r in models(library, user) {
        let a = r.resolve_qualified("A").unwrap();
        let b = r.resolve_qualified("B").unwrap();
        let own = r.resolve_qualified("A::Own").unwrap();
        let other = r.resolve_qualified("B::Other").unwrap();
        let own_m = one(&mut r, own, "owningMembership");
        let other_m = one(&mut r, other, "owningMembership");
        assert_eq!(r.imported_memberships(a), [other_m]);
        assert_eq!(r.imported_memberships(b), [own_m]);
        let self_ = r.resolve_qualified("Self").unwrap();
        assert!(r.imported_memberships(self_).is_empty());
        let item = r.resolve_qualified("Leaf::Item").unwrap();
        let item_m = one(&mut r, item, "owningMembership");
        for name in ["U", "V"] {
            let owner = r.resolve_qualified(name).unwrap();
            assert_eq!(r.imported_memberships(owner), [item_m]);
        }
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: false,
        });
        let membership = many(&mut r, a, "membership");
        assert_eq!(membership, [own_m, other_m]);
    }
}

#[test]
fn alias_imports_apply_visibility_filters_and_recursive_scope_policy() {
    let library = "package L { class T { feature x; }
        private alias Hidden for T; public alias Visible for T;
    }
    package Blocked { private import L::Hidden; }
    package All { private import all L::Hidden; }
    package Rejected { public import L::Visible[false]; }
    package Accepted { public import L::Visible[true]; }
    package Recursive { public import L::Visible::**; }";
    for mut r in models(library, "package U { private import Accepted::*; }") {
        let hidden = alias(&mut r, "L", "Hidden");
        let visible = alias(&mut r, "L", "Visible");
        for name in ["Blocked", "Rejected"] {
            let owner = r.resolve_qualified(name).unwrap();
            assert!(r.imported_memberships(owner).is_empty(), "{name}");
        }
        let all = r.resolve_qualified("All").unwrap();
        assert_eq!(r.imported_memberships(all), [hidden]);
        let imp = many(&mut r, all, "ownedImport")[0];
        assert_eq!(one(&mut r, imp, "importedMembership"), hidden);
        let accepted = r.resolve_qualified("Accepted").unwrap();
        assert_eq!(r.imported_memberships(accepted), [visible]);
        let u = r.resolve_qualified("U").unwrap();
        assert_eq!(r.imported_memberships(u), [visible]);
        let recursive = r.resolve_qualified("Recursive").unwrap();
        let x = r.resolve_qualified("L::T::x").unwrap();
        let xm = one(&mut r, x, "owningMembership");
        assert_eq!(r.imported_memberships(recursive), [visible, xm]);
    }
}

#[test]
fn cycle_boundaries_do_not_hide_a_wider_independent_path() {
    let library = "package B { class Public; private class Secret; public import C::*; }
        package C { public import all B::*; }";
    let user = "package Narrow { private import B::*; }
        package Wide { private import B::*; private import C::*; }
        package Reverse { private import C::*; private import B::*; }";
    for mut r in models(library, user) {
        let public = r.resolve_qualified("B::Public").unwrap();
        let secret = r.resolve_qualified("B::Secret").unwrap();
        let pm = one(&mut r, public, "owningMembership");
        let sm = one(&mut r, secret, "owningMembership");
        let narrow = r.resolve_qualified("Narrow").unwrap();
        assert_eq!(
            r.imported_memberships(narrow),
            [pm],
            "cycle cannot widen access to an ancestor"
        );
        for name in ["Wide", "Reverse"] {
            let owner = r.resolve_qualified(name).unwrap();
            assert_eq!(
                r.imported_memberships(owner),
                [pm, sm],
                "{name}: independent path may widen access"
            );
        }
    }
}

#[test]
fn short_alias_names_select_the_same_membership_as_the_long_name() {
    let library = "package L { class T; alias <Short> Long for T; alias <Only> for T; }";
    for mut r in models(library, "package U { import L::Short; import L::Only; }") {
        let long = alias(&mut r, "L", "Long");
        let l = r.resolve_qualified("L").unwrap();
        let only = many(&mut r, l, "ownedMembership")
            .into_iter()
            .find(|&m| {
                r.element_properties(m)
                    .get("memberShortName")
                    .and_then(|v| v.as_str())
                    == Some("Only")
            })
            .unwrap();
        let u = r.resolve_qualified("U").unwrap();
        assert_eq!(r.imported_memberships(u), [long, only]);
        let imports = many(&mut r, u, "ownedImport");
        assert_eq!(one(&mut r, imports[0], "importedMembership"), long);
        assert_eq!(one(&mut r, imports[1], "importedMembership"), only);
    }
}

#[test]
fn layered_import_diamonds_share_completed_visits() {
    // There are over sixteen million paths but only 49 imported scopes.
    // Enumeration must reuse complete visits without losing leaf identity.
    let mut src = String::new();
    for level in 0..24 {
        for suffix in ['a', 'b'] {
            src += &format!("package N{level}{suffix} {{");
            if level < 23 {
                src += &format!(
                    "public import N{}a::*; public import N{}b::*;",
                    level + 1,
                    level + 1
                );
            } else {
                src += "public import Leaf::*;";
            }
            src += "}";
        }
    }
    src += "package Leaf { class Item; } package Root { import N0a::*; import N0b::*; }";
    let mut model = Model::new();
    model.add_source("diamond.kerml", &src);
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let root = r.resolve_qualified("Root").unwrap();
    let leaf = r.resolve_qualified("Leaf::Item").unwrap();
    let membership = one(&mut r, leaf, "owningMembership");
    assert_eq!(r.imported_memberships(root), [membership]);
}

#[test]
fn interchange_reload_preserves_local_and_cross_document_alias_imports() {
    let mut model = Model::new();
    model.add_source(
        "decl.kerml",
        "package L { class T; alias A for T; alias <S> Short for T; } alias RootAlias for L::T;",
    );
    model.add_source(
        "use.kerml",
        "package U { import L::A; import L::S; import RootAlias; }",
    );
    let compact = sysmlv2_parser::json::model_to_compact_json(&model);
    let mut original = ResolvedModel::build(&model);
    let original_u = original.resolve_qualified("U").unwrap();
    let expected: Vec<_> = original
        .imported_memberships(original_u)
        .into_iter()
        .map(|m| original.element_id(m))
        .collect();
    let (_, mut loaded, _, warnings) =
        sysmlv2_parser::loader::load_document(&compact, &Default::default()).unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    let u = loaded.resolve_qualified("U").unwrap();
    let actual: Vec<_> = loaded
        .imported_memberships(u)
        .into_iter()
        .map(|m| loaded.element_id(m))
        .collect();
    assert_eq!(actual, expected);
    for (i, imp) in many(&mut loaded, u, "ownedImport").into_iter().enumerate() {
        let membership = one(&mut loaded, imp, "importedMembership");
        assert_eq!(loaded.element_id(membership), expected[i]);
    }
}

#[test]
fn same_membership_diamonds_resolve_but_distinct_same_named_aliases_are_ambiguous() {
    let library = "package L { class T; alias A for T; }
        package Left { public import L::*; }
        package Right { public import L::*; }
        package Other { alias A for L::T; }
        package AliasToHome { alias T for L::T; }
        package Diamond { public import Left::*; public import Right::*; }
        package Collision { public import Left::*; public import Other::*; }
        package HomeCollision { public import L::*; public import AliasToHome::*; }";
    let user = "package Good { import Diamond::A; }
        package Bad { import Collision::A; }
        package BadHome { import HomeCollision::T; }";
    for mut r in models(library, user) {
        let a = alias(&mut r, "L", "A");
        let good = r.resolve_qualified("Good").unwrap();
        assert_eq!(r.imported_memberships(good), [a]);
        let import = many(&mut r, good, "ownedImport")[0];
        assert_eq!(one(&mut r, import, "importedMembership"), a);
        for scope in ["Bad", "BadHome"] {
            let owner = r.resolve_qualified(scope).unwrap();
            assert!(r.imported_memberships(owner).is_empty());
            let imp = many(&mut r, owner, "ownedImport")[0];
            assert!(
                r.element_properties(imp)["importedMembership"]
                    .get("@ref")
                    .is_some()
            );
        }
        assert!(r.resolve_qualified("Collision::A").is_none());
        assert!(r.resolve_qualified("HomeCollision::T").is_none());
    }
}

#[test]
fn mixed_imports_retain_declaration_order_and_recursive_membership_prefix() {
    let library = "package L { class T { feature x; } alias A for T; }
        package Extra { class E; }
        package Reexport { public import L::A; public import Extra::*; public import L::T; }";
    let user = "package U { import L::A; import L::T; }
        package Mixed { import L::A; import Extra::*; import L::T; }
        package Through { import Reexport::*; }";
    for mut r in models(library, user) {
        let a = alias(&mut r, "L", "A");
        let t = r.resolve_qualified("L::T").unwrap();
        let tm = one(&mut r, t, "owningMembership");
        let e = r.resolve_qualified("Extra::E").unwrap();
        let em = one(&mut r, e, "owningMembership");
        let u = r.resolve_qualified("U").unwrap();
        assert_eq!(r.imported_memberships(u), [a, tm]);
        for name in ["Mixed", "Through", "Reexport"] {
            let owner = r.resolve_qualified(name).unwrap();
            assert_eq!(r.imported_memberships(owner), [a, em, tm], "{name}");
        }
    }
}

#[test]
fn namespace_imports_include_unnamed_memberships_and_recursive_anonymous_namespaces() {
    let library = "package L { feature; private feature; package { class Nested; } }";
    let user = "package U { import L::*; } package All { import all L::*; }
        package Recursive { import L::**; }";
    for mut r in models(library, user) {
        let l = r.resolve_qualified("L").unwrap();
        let all_owned = many(&mut r, l, "ownedMembership");
        assert_eq!(all_owned.len(), 3);
        let public = vec![all_owned[0], all_owned[2]];
        let u = r.resolve_qualified("U").unwrap();
        assert_eq!(r.imported_memberships(u), public);
        let all = r.resolve_qualified("All").unwrap();
        assert_eq!(r.imported_memberships(all), all_owned);
        let anonymous_package = r.membership_member(all_owned[2]).unwrap();
        let nested = many(&mut r, anonymous_package, "ownedMembership")[0];
        let lm = one(&mut r, l, "owningMembership");
        let recursive = r.resolve_qualified("Recursive").unwrap();
        assert_eq!(
            r.imported_memberships(recursive),
            [lm, public[0], public[1], nested]
        );
    }
}

#[test]
fn inherited_import_context_admits_protected_aliases_but_not_private_ones() {
    let library = "package L { class T; } class Base {
        protected alias Protected for L::T; private alias Private for L::T;
    }";
    for mut r in models(
        library,
        "class Child :> Base { import Base::Protected; import Base::Private; }",
    ) {
        let protected = alias(&mut r, "Base", "Protected");
        let child = r.resolve_qualified("Child").unwrap();
        assert_eq!(r.imported_memberships(child), [protected]);
        let imports = many(&mut r, child, "ownedImport");
        assert_eq!(one(&mut r, imports[0], "importedMembership"), protected);
        assert!(
            r.element_properties(imports[1])["importedMembership"]
                .get("@ref")
                .is_some()
        );
    }
}

#[test]
fn imported_collisions_remove_both_peers_and_respect_cross_names_and_member_types() {
    let library = "package L { class <S> Long; class Same; feature Different; class Shared; }
        package R { class S; class Same; class Different; alias Shared for L::Shared; }
        package SameAlias { alias Shared for L::Shared; }
        package Diamond { public import L::*; public import L::*; }";
    let user = "package U { import L::*; import R::*; }
        package Owned { private class <Long> Local; import L::*; }
        package Aliases { import R::Shared; import SameAlias::Shared; }
        package Reexport { import U::*; }";
    for mut r in models(library, user) {
        let lf = r.resolve_qualified("L::Different").unwrap();
        let rc = r.resolve_qualified("R::Different").unwrap();
        let fm = one(&mut r, lf, "owningMembership");
        let cm = one(&mut r, rc, "owningMembership");
        for name in ["U", "Reexport"] {
            let owner = r.resolve_qualified(name).unwrap();
            assert_eq!(r.imported_memberships(owner), [fm, cm], "{name}");
        }
        let own = r.resolve_qualified("Owned").unwrap();
        let long = r.resolve_qualified("L::Long").unwrap();
        let lm = one(&mut r, long, "owningMembership");
        assert!(!r.imported_memberships(own).contains(&lm));
        let aliases = r.resolve_qualified("Aliases").unwrap();
        assert!(
            r.imported_memberships(aliases).is_empty(),
            "distinct memberships to same target collide"
        );
        let diamond = r.resolve_qualified("Diamond").unwrap();
        let l = r.resolve_qualified("L").unwrap();
        assert_eq!(
            r.imported_memberships(diamond),
            many(&mut r, l, "ownedMembership")
        );
    }
}

#[test]
fn namespace_pruning_is_distinct_from_visibility_specific_reexport() {
    let library = "package A { class X; } package B { class X; }
        package Bridge { public import A::*; private import B::*; }";
    for mut r in models(library, "package U { import Bridge::*; }") {
        let bridge = r.resolve_qualified("Bridge").unwrap();
        assert!(r.imported_memberships(bridge).is_empty());
        let u = r.resolve_qualified("U").unwrap();
        let x = r.resolve_qualified("A::X").unwrap();
        let xm = one(&mut r, x, "owningMembership");
        assert_eq!(r.imported_memberships(u), [xm]);
    }
}

#[test]
fn package_filter_follows_pruning_but_import_filter_precedes_it() {
    let mut model = Model::new();
    model.add_source(
        "filters.sysml",
        "metadata def Safety;
        package A { #Safety part def X; }
        package B { part def X; }
        package Collision { public import A::*; public import B::*; }
        package Outer { import Collision::*[@Safety]; }
        package PackageFilter { filter @Safety; public import A::*; public import B::*; }
        package EntryFilter { public import A::*; public import B::*[@Safety]; }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    for name in ["Collision", "PackageFilter"] {
        let owner = r.resolve_qualified(name).unwrap();
        assert!(r.imported_memberships(owner).is_empty(), "{name}");
    }
    let owner = r.resolve_qualified("EntryFilter").unwrap();
    let x = r.resolve_qualified("A::X").unwrap();
    let membership = one(&mut r, x, "owningMembership");
    assert_eq!(r.imported_memberships(owner), [membership]);
    let outer = r.resolve_qualified("Outer").unwrap();
    assert_eq!(r.imported_memberships(outer), [membership]);
}

#[test]
fn cyclic_collision_results_are_recomputed_for_changed_exclusions() {
    let library = "package A { class X; public import C::*; }
        package B { class X; }
        package C { public import A::*; public import B::*; }
        package First { public import A::*; public import C::*; }
        package Reverse { public import C::*; public import A::*; }";
    for mut r in models(
        library,
        "package U { import First::*; } package V { import Reverse::*; }",
    ) {
        // Visibility traversal is raw; the two identities collide only at
        // each queried Namespace importedMemberships projection.
        for name in ["First", "Reverse", "U", "V"] {
            let owner = r.resolve_qualified(name).unwrap();
            assert!(r.imported_memberships(owner).is_empty(), "{name}");
        }
    }
}

#[test]
fn stored_feature_naming_does_not_invent_reference_or_partial_declared_names() {
    let library = "package A { feature X; }
        package Redefined { feature :>> A::X; }
        package Referenced { feature references A::X; }
        package Short { feature <S> :>> A::X; }";
    let user = "package Collision { import A::*; import Redefined::*; }
        package Reference { import A::*; import Referenced::*; }
        package Declared { import A::*; import Short::*; }";
    for mut r in models(library, user) {
        let collision = r.resolve_qualified("Collision").unwrap();
        assert!(r.imported_memberships(collision).is_empty());
        for name in ["Reference", "Declared"] {
            let owner = r.resolve_qualified(name).unwrap();
            assert_eq!(r.imported_memberships(owner).len(), 2, "{name}");
        }
    }
}

#[test]
fn named_self_import_collides_with_the_owned_membership() {
    for mut r in models("package L { class X; import L::X; }", "") {
        let l = r.resolve_qualified("L").unwrap();
        assert!(r.imported_memberships(l).is_empty());
    }
}

#[test]
fn inheritance_filters_distinct_memberships_of_one_feature_but_not_diamond_repeats() {
    let library = "package L {
        class Values { feature x; class T; }
        class Aliases { alias a for Values::x; alias b for Values::x; }
        class Mixed { feature x; alias a for x; }
        class Types { alias a for Values::T; alias b for Values::T; }
        class Single { alias a for Values::x; }
        class Left specializes Single;
        class Right specializes Single;
    }";
    let user = "class A specializes L::Aliases;
        class B specializes L::Mixed;
        class C specializes L::Types;
        class D specializes L::Left, L::Right;";
    for mut r in models(library, user) {
        let single = alias(&mut r, "L::Single", "a");
        let types = [
            alias(&mut r, "L::Types", "a"),
            alias(&mut r, "L::Types", "b"),
        ];
        for include_implied in [false, true, false] {
            r.set_closure_policy(ClosurePolicy::Closure { include_implied });
            for name in ["A", "B"] {
                let e = r.resolve_qualified(name).unwrap();
                assert!(
                    r.inherited_memberships(e, include_implied).is_empty(),
                    "{name}"
                );
                assert!(many(&mut r, e, "inheritedMembership").is_empty());
                assert!(many(&mut r, e, "inheritedFeature").is_empty());
            }
            let c = r.resolve_qualified("C").unwrap();
            assert_eq!(r.inherited_memberships(c, include_implied), types);
            let d = r.resolve_qualified("D").unwrap();
            assert_eq!(r.inherited_memberships(d, include_implied), [single]);
        }
    }
}

#[test]
fn inherited_feature_aliases_are_redefinition_candidates_and_blockers() {
    let library = "package L {
        class Values { feature x; }
        class Redefiners specializes Values { feature y redefines x; }
        class Old { public import Values::x; }
        class Alias { alias renamed for Redefiners::y; }
    }";
    let user = "class Inherited specializes L::Old, L::Alias;
        class Owned specializes L::Alias { feature z redefines L::Values::x; }
        class Combined specializes L::Old, L::Alias { feature z redefines L::Redefiners::y; }
        class OwnedAlias specializes L::Old { alias local for L::Redefiners::y; }";
    for mut r in models(library, user) {
        let a = alias(&mut r, "L::Alias", "renamed");
        let x = r.resolve_qualified("L::Values::x").unwrap();
        let xm = one(&mut r, x, "owningMembership");
        for include_implied in [true, false, true] {
            let inherited = r.resolve_qualified("Inherited").unwrap();
            assert_eq!(r.inherited_memberships(inherited, include_implied), [a]);
            let owned = r.resolve_qualified("Owned").unwrap();
            assert!(r.inherited_memberships(owned, include_implied).is_empty());
            let combined = r.resolve_qualified("Combined").unwrap();
            assert!(
                r.inherited_memberships(combined, include_implied)
                    .is_empty()
            );
            let owned_alias = r.resolve_qualified("OwnedAlias").unwrap();
            assert_eq!(r.inherited_memberships(owned_alias, include_implied), [xm]);
        }
    }
}

#[test]
fn private_aliases_do_not_suppress_inherited_public_features() {
    let library = "class Base { feature x; private alias hidden for x; }
        class ProtectedBase { feature x; protected alias visible for x; }";
    for mut r in models(
        library,
        "class Sub specializes Base; class Other specializes ProtectedBase;",
    ) {
        let x = r.resolve_qualified("Base::x").unwrap();
        let xm = one(&mut r, x, "owningMembership");
        for include_implied in [false, true] {
            let sub = r.resolve_qualified("Sub").unwrap();
            assert_eq!(r.inherited_memberships(sub, include_implied), [xm]);
            let other = r.resolve_qualified("Other").unwrap();
            assert!(r.inherited_memberships(other, include_implied).is_empty());
        }
    }
}

#[test]
fn mutual_redefinition_cycles_remove_both_memberships() {
    // Deliberately malformed semantic graph; both targets must really bind.
    let library = "class Root;
        class Pair specializes Root { feature x redefines Pair::y; feature y redefines Pair::x; }";
    for mut r in models(library, "class Double specializes Pair;") {
        let x = r.resolve_qualified("Pair::x").unwrap();
        let y = r.resolve_qualified("Pair::y").unwrap();
        for (source, target) in [(x, y), (y, x)] {
            let edge = r
                .owned_relationships(source)
                .into_iter()
                .find(|&edge| r.element_type(edge) == "Redefinition")
                .unwrap();
            assert_eq!(
                r.element_properties(edge)["redefinedFeature"]["@id"],
                r.element_id(target).to_string()
            );
        }
        for include_implied in [false, true] {
            let double = r.resolve_qualified("Double").unwrap();
            assert!(r.inherited_memberships(double, include_implied).is_empty());
        }
    }
}

#[test]
fn unavailable_alias_targets_qualify_inheritance_without_removing_known_members() {
    for mut r in models(
        "class Base { feature x; alias unknown for Missing; }",
        "class Child specializes Base;",
    ) {
        let child = r.resolve_qualified("Child").unwrap();
        let unknown = alias(&mut r, "Base", "unknown");
        let x = r.resolve_qualified("Base::x").unwrap();
        let xm = one(&mut r, x, "owningMembership");
        for include_implied in [false, true] {
            assert_eq!(
                r.inherited_memberships(child, include_implied),
                [xm, unknown]
            );
            assert!(r.inheritance_incomplete(child, include_implied));
        }
    }
}

#[test]
fn layered_inheritance_diamonds_keep_one_alias_identity() {
    let mut library =
        String::from("class Values { feature x; } class Root { alias a for Values::x; }\n");
    for level in 0..24 {
        let bases = if level == 0 {
            "Root".to_owned()
        } else {
            format!("Left{}, Right{}", level - 1, level - 1)
        };
        library.push_str(&format!(
            "class Left{level} specializes {bases}; class Right{level} specializes {bases};\n"
        ));
    }
    for mut r in models(&library, "class Leaf specializes Left23, Right23;") {
        let a = alias(&mut r, "Root", "a");
        let leaf = r.resolve_qualified("Leaf").unwrap();
        for include_implied in [false, true, false] {
            assert_eq!(r.inherited_memberships(leaf, include_implied), [a]);
            assert!(!r.inheritance_walk_truncated(leaf, include_implied));
        }
    }
}
