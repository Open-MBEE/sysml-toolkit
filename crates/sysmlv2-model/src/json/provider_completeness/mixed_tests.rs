use super::{recursive_tests::fixture, *};
const TREE: &str = "package Tree {package Nested {alias Leaf for $::Marker;}} package Extra {alias Added for $::Other;}";

#[test]
fn mixed_recursive_and_ordinary_imports_preserve_member_and_namespace_lookup() {
    for ordinary in ["$::Other", "$::Extra::*", "$::Extra::**", "$::Extra::*::**"] {
        for recursive in ["$::Tree::**", "$::Tree::*::**"] {
            let import = format!("{recursive}; private import {ordinary}");
            let (mut r, scope) = fixture(TREE, &import);
            let marker = r.resolve_qualified("Marker").unwrap().0;
            let other = r.resolve_qualified("Other").unwrap().0;
            let mut proof = ProviderCompleteness::default();
            r.b.import_cache[scope] = None;
            let used = r.b.used_imports.clone();
            assert!(proof.scope(&mut r.b, scope, &mut 0), "{import}");
            assert!(r.b.import_cache[scope].is_none());
            assert_eq!(r.b.used_imports, used);
            assert_eq!(r.b.lookup(scope, "Leaf", 0).map(|v| v.0), Some(marker));
            let added = if ordinary == "$::Other" {
                "Other"
            } else {
                "Added"
            };
            assert_eq!(r.b.lookup(scope, added, 0).map(|v| v.0), Some(other));
            let mut exhausted = crate::eval::MAX_STEPS;
            assert!(!proof.scope(&mut r.b, scope, &mut exhausted));
            assert!(proof.scope(&mut r.b, scope, &mut 0));
        }
    }
}

#[test]
fn recursive_package_contents_admit_acyclic_internal_imports_and_global_aliases() {
    for internal in [
        "$::Marker",
        "$::Relay::*",
        "$::Relay::**",
        "$::Relay::*::**",
    ] {
        let tree = format!(
            "package Relay {{alias Imported for $::Marker;}} package Tree {{alias Local for $::Other; public import {internal};}}"
        );
        let (mut r, scope) = fixture(&tree, "$::Tree::*::**");
        let marker = r.resolve_qualified("Marker").unwrap().0;
        let other = r.resolve_qualified("Other").unwrap().0;
        assert!(
            ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0),
            "{internal}"
        );
        let name = if internal == "$::Marker" {
            "Marker"
        } else {
            "Imported"
        };
        assert_eq!(r.b.lookup(scope, name, 0).map(|v| v.0), Some(marker));
        assert_eq!(r.b.lookup(scope, "Local", 0).map(|v| v.0), Some(other));
    }
    let (mut r, scope) = fixture(
        "package Relay {alias Imported for $::Marker;} package Tree {private import $::Relay::*;}",
        "$::Tree::*::**",
    );
    assert!(ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0));
    assert!(r.b.lookup(scope, "Imported", 0).is_none());
    let (mut r, scope) = fixture(
        "package Relay {alias Imported for $::Marker;} package Tree {private import $::Relay::*;}",
        "all $::Tree::*::**",
    );
    assert!(ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0));
    assert!(r.b.lookup(scope, "Imported", 0).is_some());
}

#[test]
fn ordinary_imports_in_recursive_domains_require_complete_current_mirrors_and_raw_rows() {
    for ordinary in ["$::Other", "$::Extra::*"] {
        let (mut r, scope) = fixture(TREE, &format!("$::Tree::*::**; private import {ordinary}"));
        let mut proof = ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let namespaces = r.b.scopes[scope].imports.clone();
        let members = r.b.scopes[scope].member_imports.clone();
        let relationship = if ordinary == "$::Other" {
            r.b.scopes[scope].member_imports.pop().unwrap().relationship
        } else {
            r.b.scopes[scope].imports.pop().unwrap().relationship
        };
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[scope].imports = namespaces.clone();
        r.b.scopes[scope].member_imports = members.clone();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let owner = r.b.scopes[scope].owner.unwrap();
        let relationships = r.b.elements[owner].owned_relationships.clone();
        r.b.elements[owner].owned_relationships = relationships
            .iter()
            .copied()
            .filter(|&r| r != relationship)
            .collect();
        r.b.scopes[scope]
            .imports
            .retain(|entry| entry.relationship != relationship);
        r.b.scopes[scope]
            .member_imports
            .retain(|entry| entry.relationship != relationship);
        r.b.import_cache[scope] = None;
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.elements[owner].owned_relationships = relationships;
        r.b.scopes[scope].imports = namespaces;
        r.b.scopes[scope].member_imports = members;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        r.b.elements[relationship]
            .props
            .insert("isRecursive", serde_json::json!(true));
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.elements[relationship]
            .props
            .insert("isRecursive", serde_json::json!(false));
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        r.b.import_scopes(scope);
        let cache = r.b.import_cache[scope].clone();
        r.b.import_cache[scope] = Some(std::sync::Arc::new(vec![]));
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.import_cache[scope] = cache;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }
}

#[test]
fn ordinary_package_visits_do_not_certify_recursive_children_or_cache_unsupported_aliases() {
    // Both dependency kinds visit Tree. Its child is irrelevant to ordinary
    // lookup but requires a separate recursive certificate, in either order.
    for imports in [
        "$::Tree::*; private import $::Tree::*::**",
        "$::Tree::*::**; private import $::Tree::*",
    ] {
        let (mut r, scope) = fixture(
            "package Tree {package Nested {alias Leaf for Missing;}}",
            imports,
        );
        assert!(!ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0));
    }
    for tree in [
        "package Tree {public import $::Tree::*;}",
        "package Tree {public import $::Relay::*;} package Relay {public import $::Tree::*;}",
        "package Tree {package Child {public import $::Tree::*;}}",
        "package Tree {public import $::Relay::*;} package Relay {alias Leaf for Marker;}",
        "package Tree {public import $::Relay::*;} package Relay {filter true;}",
        "package Tree {public import Relay::*;} package Relay {alias Leaf for $::Marker;}",
    ] {
        let (mut r, scope) = fixture(tree, "$::Tree::*::**");
        assert!(
            !ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0),
            "{tree}"
        );
    }
}

#[test]
fn internal_import_depth_and_diamond_ambiguity_match_lookup() {
    for hops in [0, 20, 21, 22, 23] {
        let mut tree = "package Tree {public import $::P0::*;}".to_owned();
        for i in 0..hops {
            tree.push_str(&format!("package P{i} {{public import $::P{}::*;}}", i + 1));
        }
        tree.push_str(&format!("package P{hops} {{alias Leaf for $::Marker;}}"));
        let (mut r, scope) = fixture(&tree, "$::Tree::*::**");
        let expected = hops <= crate::json::MAX_RESOLUTION_DEPTH - 3;
        assert_eq!(
            ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0),
            expected,
            "hops={hops}"
        );
        assert_eq!(
            r.b.lookup(scope, "Leaf", 0).is_some(),
            expected,
            "lookup hops={hops}"
        );
    }
    for same in [true, false] {
        let tree = format!(
            "package End {{alias Leaf for $::Marker;}} package OtherEnd {{alias Leaf for $::Other;}} package Left {{public import $::End::*;}} package Right {{public import $::{}::*;}} package Tree {{public import $::Left::*; public import $::Right::*;}}",
            if same { "End" } else { "OtherEnd" }
        );
        let (mut r, scope) = fixture(&tree, "$::Tree::*::**");
        assert!(ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0));
        assert_eq!(r.b.lookup(scope, "Leaf", 0).is_some(), same);
    }
}

#[test]
fn completed_ordinary_package_memos_cannot_hide_recursive_children_or_active_cycles() {
    for tree in [
        "package Tree {package Nested {alias Leaf for Missing;}}",
        "package Tree {package Child {public import $::Tree::*;}}",
    ] {
        let (mut r, scope) = fixture(tree, "$::Tree::*");
        let owner = r.resolve_qualified("Tree").unwrap().0;
        let tree_scope = *r.b.elem_scope.get(&owner).unwrap();
        let mut proof = ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        assert!(proof.package_scope(&mut r.b, tree_scope, 0, None, &mut 0));
        // Child imports Tree at depth two. Prime that exact memo key so the
        // active-cycle guard, rather than a cache miss, must reject the route.
        assert!(proof.package_scope(&mut r.b, tree_scope, 2, None, &mut 0));
        assert!(
            !proof.package_scope(&mut r.b, tree_scope, 0, Some(false), &mut 0),
            "{tree}"
        );
    }
}

#[test]
fn ordinary_membership_imports_preserve_dynamic_qualified_depth_and_current_target() {
    for hops in [19, 20, 21, 22] {
        let mut tree =
            "package Definitions {class Target;} package Tree {public import $::P0::*;}".to_owned();
        for i in 0..hops {
            tree.push_str(&format!("package P{i} {{public import $::P{}::*;}}", i + 1));
        }
        tree.push_str(&format!(
            "package P{hops} {{public import $::Definitions::Target;}}"
        ));
        let (mut r, scope) = fixture(&tree, "$::Tree::*::**");
        assert_eq!(
            ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0),
            hops <= 20,
            "proof hops={hops}"
        );
        assert_eq!(
            r.b.lookup(scope, "Target", 0).is_some(),
            hops <= 20,
            "lookup hops={hops}"
        );
    }
    let (mut r, scope) = fixture(TREE, "$::Tree::*::**; private import $::Other");
    let mut proof = ProviderCompleteness::default();
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    let member = r.b.scopes[scope].member_imports[0].clone();
    r.b.scopes[scope].member_imports[0].target.segments[0].value = "Marker".to_owned();
    assert!(!proof.scope(&mut r.b, scope, &mut 0));
    r.b.scopes[scope].member_imports[0] = member.clone();
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    r.b.scopes[scope].member_imports[0].is_public = !member.is_public;
    assert!(!proof.scope(&mut r.b, scope, &mut 0));
    r.b.scopes[scope].member_imports[0] = member;
    assert!(proof.scope(&mut r.b, scope, &mut 0));
}
