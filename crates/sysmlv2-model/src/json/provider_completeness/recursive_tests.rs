use super::*;
use crate::{json::ResolvedModel, model::Model};
pub(super) fn fixture(tree: &str, import: &str) -> (ResolvedModel, usize) {
    let mut model = Model::new();
    let parsed = model.add_source(
        "recursive-providers.kerml",
        &format!("class Marker; class Other; {tree} package Consumer {{private import {import};}}"),
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut r = ResolvedModel::build(&model);
    let owner = r.resolve_qualified("Consumer").unwrap().0;
    let scope = *r.b.elem_scope.get(&owner).unwrap();
    (r, scope)
}
const TREE: &str = "package Tree {package Nested {alias Leaf for $::Marker;}}";
#[test]
fn recursive_import_forms_certify_named_trees_and_preserve_lookup_state() {
    for import in ["$::Tree::**", "$::Tree::*::**", "all $::Tree::*::**"] {
        let (mut r, scope) = fixture(TREE, import);
        let marker = r.resolve_qualified("Marker").unwrap().0;
        let mut proof = ProviderCompleteness::default();
        r.b.probing = true;
        let misses = r.b.current_misses.clone();
        assert!(proof.scope(&mut r.b, scope, &mut 0), "{import}");
        assert!(r.b.probing);
        assert_eq!(r.b.current_misses, misses);
        r.b.probing = false;
        assert_eq!(r.b.lookup(scope, "Leaf", 0).map(|v| v.0), Some(marker));
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(!proof.scope(&mut r.b, scope, &mut exhausted));
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }
}
#[test]
fn recursive_tree_depth_matches_lookup_including_terminal_alias_cost() {
    for nested in [0, 21, 22, 23, 24] {
        let mut tree = "package Tree {".to_owned();
        for i in 0..nested {
            tree.push_str(&format!("package N{i} {{"));
        }
        tree.push_str("alias Leaf for $::Marker;");
        tree.push_str(&"}".repeat(nested + 1));
        let (mut r, scope) = fixture(&tree, "$::Tree::*::**");
        let expected = nested <= crate::json::MAX_RESOLUTION_DEPTH - 2;
        let mut proof = ProviderCompleteness::default();
        assert_eq!(
            proof.scope(&mut r.b, scope, &mut 0),
            expected,
            "nested={nested}"
        );
        assert_eq!(
            r.b.lookup(scope, "Leaf", 0).is_some(),
            expected,
            "lookup nested={nested}"
        );
    }
}
#[test]
fn recursive_proofs_recheck_resolver_and_endpoint_mutations_then_recover() {
    for import in ["$::Tree::**", "$::Tree::*::**"] {
        let (mut r, scope) = fixture(TREE, import);
        let tree = r.resolve_qualified("Tree").unwrap().0;
        let tree_scope = *r.b.elem_scope.get(&tree).unwrap();
        let mut proof = ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[scope].filters.push(usize::MAX);
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[scope].filters.clear();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        // A cold direct global target is complete without warming lookup.
        r.b.import_cache[scope] = None;
        let targets = r.b.import_targets.clone();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        assert!(r.b.import_cache[scope].is_none());
        assert_eq!(r.b.import_targets, targets);
        r.b.import_scopes(scope);
        let cache = r.b.import_cache[scope].clone();
        r.b.import_cache[scope] = Some(std::sync::Arc::new(vec![]));
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.import_cache[scope] = cache;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let mut extra = r.b.import_cache[scope].as_ref().unwrap()[0].clone();
        extra.relationship = usize::MAX;
        std::sync::Arc::make_mut(r.b.import_cache[scope].as_mut().unwrap()).push(extra);
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        std::sync::Arc::make_mut(r.b.import_cache[scope].as_mut().unwrap()).pop();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let entries = r.b.scopes[scope].imports.clone();
        r.b.scopes[scope].imports.clear();
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[scope].imports = entries;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let root_names = r.b.scopes[0].names.clone();
        r.b.scopes[0].names = Default::default();
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[0].names = root_names;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let names = r.b.scopes[tree_scope].names.clone();
        r.b.scopes[tree_scope].names = Default::default();
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[tree_scope].names = names;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        r.b.elem_scope.insert(tree, scope);
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.elem_scope.insert(tree, tree_scope);
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let rel = r.b.scopes[scope].imports[0].relationship;
        let props = r.b.elements[rel].props.clone();
        r.b.elements[rel]
            .props
            .insert("isRecursive", serde_json::json!(false));
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.elements[rel].props = props;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[scope].imports[0].recursive = false;
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[scope].imports[0].recursive = true;
        // A failed mismatch still depends on resolver state, so must recover.
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }
}
#[test]
fn unsupported_recursive_domains_refuse_without_hiding_ambiguity() {
    for tree in [
        "package Tree {class Local;}",
        "package Tree {package {alias Leaf for $::Marker;}}",
        "package Tree {package Nested {private import Marker;}}",
        "package Tree {public import Tree::*;}",
        "package Tree {alias Leaf for Marker;}",
        "package Tree {alias Leaf for $::Missing;}",
        "package Tree {filter true;}",
    ] {
        let (mut r, scope) = fixture(tree, "$::Tree::*::**");
        assert!(
            !ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0),
            "{tree}"
        );
    }
    let (mut r, scope) = fixture(
        "package Tree {package A {alias Same for $::Marker;} package B {alias Same for $::Other;}}",
        "$::Tree::*::**",
    );
    assert!(ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0));
    assert!(r.b.lookup(scope, "Same", 0).is_none());
}

#[test]
fn inverse_recursive_imports_cannot_disappear_with_all_forward_views() {
    for import in ["$::Tree::**", "$::Tree::*::**"] {
        let (mut r, scope) = fixture(TREE, import);
        let owner = r.b.scopes[scope].owner.unwrap();
        let relationships = r.b.elements[owner].owned_relationships.clone();
        let imports = r.b.scopes[scope].imports.clone();
        let members = r.b.scopes[scope].member_imports.clone();
        let cached = r.b.import_cache[scope].clone();
        r.b.elements[owner].owned_relationships = Default::default();
        r.b.scopes[scope].imports.clear();
        r.b.scopes[scope].member_imports.clear();
        r.b.import_cache[scope] = None;
        let mut proof = ProviderCompleteness::default();
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.elements[owner].owned_relationships = relationships;
        r.b.scopes[scope].imports = imports;
        r.b.scopes[scope].member_imports = members;
        r.b.import_cache[scope] = cached;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }
}
#[test]
fn recursive_aliases_require_complete_raw_root_name_group_and_current_scope() {
    let (mut r, scope) = fixture(TREE, "$::Tree::*::**");
    let marker = r.resolve_qualified("Marker").unwrap().0;
    let other = r.resolve_qualified("Other").unwrap().0;
    let mut proof = ProviderCompleteness::default();
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    let original = r.b.elements[other].props.clone();
    r.b.elements[other]
        .props
        .insert("declaredName", serde_json::json!("Marker"));
    assert!(!proof.scope(&mut r.b, scope, &mut 0));
    r.b.elements[other].props = original;
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    let marker_scope = *r.b.elem_scope.get(&marker).unwrap();
    let other_scope = *r.b.elem_scope.get(&other).unwrap();
    let root_names = r.b.scopes[0].names.clone();
    let mut wrong = crate::json::scope_table::Names::default();
    for (name, bindings) in root_names.iter() {
        for binding in bindings {
            let mut binding = *binding;
            if binding.elem == marker {
                binding.sub_scope = Some(other_scope);
            }
            wrong.push(name.to_owned(), binding);
        }
    }
    r.b.scopes[0].names = wrong;
    r.b.elem_scope.insert(marker, other_scope);
    assert!(!proof.scope(&mut r.b, scope, &mut 0));
    r.b.scopes[0].names = root_names;
    r.b.elem_scope.insert(marker, marker_scope);
    assert!(proof.scope(&mut r.b, scope, &mut 0));
}

#[test]
fn stored_import_relationship_targets_keep_membership_and_element_identities_distinct() {
    for import in ["$::Tree::**", "$::Tree::*::**"] {
        let (mut r, scope) = fixture(TREE, import);
        let owner = r.b.scopes[scope].owner.unwrap();
        let rel = r.b.scopes[scope].imports[0].relationship;
        let tree = r.resolve_qualified("Tree").unwrap().0;
        let target = if r.b.elements[rel].ty == "MembershipImport" {
            r.b.elements[tree].owning_relationship.unwrap()
        } else {
            tree
        };
        let owner_id = r.b.elements[owner].id;
        let target_id = r.b.elements[target].id;
        let tree_id = r.b.elements[tree].id;
        r.b.elements[rel]
            .props
            .insert("target", serde_json::json!([{"@id": target_id}]));
        r.b.elements[rel].props.insert(
            "relatedElement",
            serde_json::json!([{"@id": owner_id}, {"@id": target_id}]),
        );
        r.b.elements[rel]
            .props
            .insert("importedElement", serde_json::json!({"@id": tree_id}));
        let mut proof = ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        if target != tree {
            r.b.elements[rel]
                .props
                .insert("target", serde_json::json!([{"@id": tree_id}]));
            assert!(!proof.scope(&mut r.b, scope, &mut 0));
            r.b.elements[rel]
                .props
                .insert("target", serde_json::json!([{"@id": target_id}]));
            assert!(proof.scope(&mut r.b, scope, &mut 0));
        }
    }
}

#[test]
fn recursive_root_name_cache_reset_charges_before_drop_and_can_retry() {
    let (mut r, scope) = fixture(TREE, "$::Tree::*::**");
    let mut proof = ProviderCompleteness::default();
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    let mut reset_cost = 0;
    assert_eq!(proof.reset_with_budget(&mut reset_cost), Some(()));
    assert!(reset_cost > 1);
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    let mut exhausted = crate::eval::MAX_STEPS - reset_cost + 1;
    assert_eq!(proof.reset_with_budget(&mut exhausted), None);
    assert!(exhausted > crate::eval::MAX_STEPS);
    assert_eq!(proof.reset_with_budget(&mut 0), Some(()));
    assert!(proof.scope(&mut r.b, scope, &mut 0));
}

const QUALIFIED_TREE: &str = "package Definitions {class Target;} package Catalog {package Tree {package Nested {alias Leaf for $::Definitions::Target;}}}";
#[test]
fn qualified_recursive_targets_and_aliases_use_direct_membership_paths() {
    for import in [
        "$::Catalog::Tree::**",
        "$::Catalog::Tree::*::**",
        "all $::Catalog::Tree::*::**",
    ] {
        let (mut r, scope) = fixture(QUALIFIED_TREE, import);
        let marker = r.resolve_qualified("Definitions::Target").unwrap().0;
        let mut proof = ProviderCompleteness::default();
        r.b.import_cache[scope] = None;
        assert!(proof.scope(&mut r.b, scope, &mut 0), "{import}");
        assert!(r.b.import_cache[scope].is_none());
        assert_eq!(r.b.lookup(scope, "Leaf", 0).map(|v| v.0), Some(marker));
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(!proof.scope(&mut r.b, scope, &mut exhausted));
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }
}

#[test]
fn qualified_target_witnesses_reject_hidden_ambiguity_stale_bindings_and_identity_overrides() {
    let (mut r, scope) = fixture(QUALIFIED_TREE, "$::Catalog::Tree::**");
    let tree = r.resolve_qualified("Catalog::Tree").unwrap().0;
    let catalog = r.resolve_qualified("Catalog").unwrap().0;
    let catalog_scope = *r.b.elem_scope.get(&catalog).unwrap();
    let target = r.resolve_qualified("Definitions::Target").unwrap().0;
    let definitions = r.resolve_qualified("Definitions").unwrap().0;
    let definitions_scope = *r.b.elem_scope.get(&definitions).unwrap();
    let mut proof = ProviderCompleteness::default();
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    for (member, parent) in [(tree, catalog_scope), (target, definitions_scope)] {
        let relationship = r.b.elements[member].owning_relationship.unwrap();
        let props = r.b.elements[relationship].props.clone();
        r.b.elements[relationship]
            .props
            .insert("visibility", serde_json::json!("private"));
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.elements[relationship].props = props;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let names = r.b.scopes[parent].names.clone();
        r.b.scopes[parent].names = Default::default();
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[parent].names = names;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        let sub = *r.b.elem_scope.get(&member).unwrap();
        let original_parent = r.b.scopes[sub].parent;
        r.b.scopes[sub].parent = Some(scope);
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.scopes[sub].parent = original_parent;
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }
    let entry = r.b.scopes[scope].imports[0].clone();
    for segment in &entry.target.segments {
        let key = (
            r.b.unit_of_elem(entry.relationship),
            segment.span.start,
            segment.span.end,
        );
        let id = r.b.elements[tree].id;
        r.b.id_spelled_targets.insert(key, (id, id));
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.id_spelled_targets.remove(&key);
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }
    let nested = r.resolve_qualified("Catalog::Tree::Nested").unwrap().0;
    let nested_scope = *r.b.elem_scope.get(&nested).unwrap();
    let alias = r.b.scopes[nested_scope].aliases[0].1.clone();
    let unit =
        r.b.alias_origins
            .get(&(nested_scope, 0))
            .copied()
            .unwrap_or_else(|| r.b.unit_of_scope(nested_scope));
    for segment in &alias.segments {
        let key = (unit, segment.span.start, segment.span.end);
        let id = r.b.elements[target].id;
        r.b.id_spelled_targets.insert(key, (id, id));
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.id_spelled_targets.remove(&key);
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }
    // The raw name group must agree even if the resolver omits its collision.
    let (mut r, scope) = fixture(
        "package Catalog {package Tree {} package Other {}}",
        "$::Catalog::Tree::*::**",
    );
    let other = r.resolve_qualified("Catalog::Other").unwrap().0;
    let mut proof = ProviderCompleteness::default();
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    let props = r.b.elements[other].props.clone();
    r.b.elements[other]
        .props
        .insert("declaredName", serde_json::json!("Tree"));
    assert!(!proof.scope(&mut r.b, scope, &mut 0));
    r.b.elements[other].props = props;
    assert!(proof.scope(&mut r.b, scope, &mut 0));
}

#[test]
fn qualified_recursive_paths_keep_dynamic_and_cached_resolution_depth_distinct() {
    for form in ["**", "*::**"] {
        for depth in [22, 23, 24] {
            let (mut r, scope) = fixture(
                "package Catalog {package Tree {}}",
                &format!("$::Catalog::Tree::{form}"),
            );
            let mut proof = ProviderCompleteness::default();
            assert!(proof.scope(&mut r.b, scope, &mut 0));
            assert!(proof.invalidate_known(&mut 0));
            let expected = if form == "**" {
                depth <= 22
            } else {
                depth <= 23
            };
            assert_eq!(
                proof.scope_inner(&mut r.b, scope, depth, &mut 0),
                expected,
                "{form} depth={depth}"
            );
            if form == "**" {
                assert_eq!(r.b.lookup(scope, "Tree", depth).is_some(), expected);
            }
        }
    }
    for nested in [20, 21, 22] {
        let tree = format!(
            "package Definitions {{class Target;}} package Tree {{{}alias Leaf for $::Definitions::Target;{}}}",
            "package Nested {".repeat(nested),
            "}".repeat(nested)
        );
        let (mut r, scope) = fixture(&tree, "$::Tree::*::**");
        let expected = nested <= 21;
        assert_eq!(
            ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0),
            expected
        );
        assert_eq!(r.b.lookup(scope, "Leaf", 0).is_some(), expected);
    }
}

#[test]
fn qualified_recursive_paths_do_not_infer_indirect_or_hidden_qualifiers() {
    for tree in [
        "package Actual {package Tree {}} alias Catalog for $::Actual;",
        "class Catalog {package Tree {}}",
        "package Catalog {private package Tree {}}",
        "package Catalog {protected package Tree {}}",
        "package Actual {package Tree {}} package Catalog {public import $::Actual::*;}",
    ] {
        let (mut r, scope) = fixture(tree, "$::Catalog::Tree::*::**");
        assert!(
            !ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0),
            "{tree}"
        );
    }
}

#[test]
fn qualified_namespace_cache_targets_obey_their_own_cold_path_limit() {
    for segments in [24, 25, 26] {
        let path = (0..segments).map(|i| format!("N{i}")).collect::<Vec<_>>();
        let tree = path
            .iter()
            .map(|n| format!("package {n} {{"))
            .collect::<String>()
            + &"}".repeat(segments);
        let import = format!("$::{}::*::**", path.join("::"));
        let (mut r, scope) = fixture(&tree, &import);
        r.b.import_cache[scope] = None;
        let mut proof = ProviderCompleteness::default();
        assert_eq!(proof.scope(&mut r.b, scope, &mut 0), segments <= 25);
        assert!(r.b.import_cache[scope].is_none());
        assert_eq!(!r.b.import_scopes(scope).is_empty(), segments <= 25);
    }
}

#[test]
fn qualified_scope_name_indexes_charge_reset_and_recover_after_exhaustion() {
    let (mut r, scope) = fixture(QUALIFIED_TREE, "$::Catalog::Tree::*::**");
    let mut proof = ProviderCompleteness::default();
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    let mut cost = 0;
    assert_eq!(proof.reset_with_budget(&mut cost), Some(()));
    assert!(cost > 1);
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    let mut exhausted = crate::eval::MAX_STEPS - cost + 1;
    assert_eq!(proof.reset_with_budget(&mut exhausted), None);
    assert!(exhausted > crate::eval::MAX_STEPS);
    assert_eq!(proof.reset_with_budget(&mut 0), Some(()));
    assert!(proof.scope(&mut r.b, scope, &mut 0));
}

#[test]
fn qualified_paths_preserve_short_names_and_direct_binding_precedence() {
    for (tree, import) in [
        (
            "package <C> Catalog {package <T> Tree {alias Leaf for $::Marker;}}",
            "$::C::T::*::**",
        ),
        (
            "package Catalog {package Mid {package Tree {alias Leaf for $::Marker;}}}",
            "$::Catalog::Mid::Tree::*::**",
        ),
        (
            "package Catalog {package Tree {alias Leaf for $::Marker;} alias Tree for $::Other; private import $::Other;}",
            "$::Catalog::Tree::*::**",
        ),
        (
            "package Definitions {class <T> Target;} package Tree {alias Leaf for $::Definitions::T;}",
            "$::Tree::*::**",
        ),
    ] {
        let (mut r, scope) = fixture(tree, import);
        assert!(
            ProviderCompleteness::default().scope(&mut r.b, scope, &mut 0),
            "{tree}"
        );
        assert!(r.b.lookup(scope, "Leaf", 0).is_some());
    }
    let (mut r, scope) = fixture(
        "package Catalog {package Tree {} package Other {}}",
        "$::Catalog::Tree::*::**",
    );
    let other = r.resolve_qualified("Catalog::Other").unwrap().0;
    let mut proof = ProviderCompleteness::default();
    assert!(proof.scope(&mut r.b, scope, &mut 0));
    let props = r.b.elements[other].props.clone();
    r.b.elements[other]
        .props
        .insert("declaredShortName", serde_json::json!("Tree"));
    assert!(!proof.scope(&mut r.b, scope, &mut 0));
    r.b.elements[other].props = props;
    assert!(proof.scope(&mut r.b, scope, &mut 0));
}
