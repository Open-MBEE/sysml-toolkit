//! Recursive lookup providers certify named plain-package trees and exact Membership identity.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, OperationError, Reference, ResolvedModel},
    libcache::LibraryCache,
    model::{GraphFormat, Model},
    prepared::PreparedLibrary,
};
fn inherited(r: &mut ResolvedModel, owner: ElementRef) -> Result<Vec<ElementRef>, OperationError> {
    let report = r.invoke_operation(
        owner,
        "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean",
        &[
            DerivedValue::Elements(vec![]),
            DerivedValue::Elements(vec![]),
            DerivedValue::Bool(true),
        ],
    )?;
    let DerivedValue::References(values) = report.value else {
        panic!("expected memberships")
    };
    Ok(values
        .into_iter()
        .map(|v| match v {
            Reference::Element(e) => e,
            _ => panic!("expected loaded membership"),
        })
        .collect())
}
fn membership(r: &mut ResolvedModel, name: &str) -> ElementRef {
    let e = r.resolve_qualified(name).unwrap();
    let value = r.property(e, "owningRelationship").unwrap();
    r.element_by_id(value["@id"].as_str().unwrap()).unwrap()
}
fn named_member(r: &mut ResolvedModel, namespace: &str, name: &str) -> ElementRef {
    let owner = r.resolve_qualified(namespace).unwrap();
    r.owned_relationships(owner)
        .into_iter()
        .find(|&m| r.membership_member_name(m).as_deref() == Some(name))
        .unwrap()
}
#[test]
fn recursive_plain_package_providers_preserve_actual_library_identities_and_replay() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        return;
    }
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut base = Model::with_graph_format(format);
        base.load_library_dir(&library).unwrap();
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(97).unwrap(), 97).unwrap());
        for (early_tree, qualified) in [(true, false), (false, false), (true, true), (false, true)]
        {
            let mut expected = None;
            for mode in 0..4 {
                let mut model = Model::with_graph_format(format);
                match mode {
                    2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                    _ => {
                        model.load_library_dir(&library).unwrap();
                        if mode == 1 {
                            model.set_library_cache(cache.clone());
                        }
                    }
                }
                let tree = "package Tree {
                    alias RootAlias for $::Marker;
                    package Left {alias DeepAlias for $::Marker; alias Clash for $::Marker;}
                    package Right {alias Clash for $::OtherMarker;}
                    private package Hidden {alias SecretAlias for $::Marker;}
                    private alias PrivateAlias for $::Marker;
                }";
                let consumers = "
                    class MemberProvider {public import $::Tree::**;}
                    class MemberChild specializes MemberProvider {feature ownMember;}
                    class NamespaceProvider {public import $::Tree::*::**;}
                    class NamespaceChild specializes NamespaceProvider {feature ownNamespace;}
                    class AllProvider {public import all $::Tree::*::**;}
                    class AllChild specializes AllProvider {feature ownAll;}
                    package NamespaceConsumer {private import $::Tree::*::**;}
                ";
                let negatives = "
                    package InternalTree {package Nested {private import Marker;}}
                    class InternalProvider {public import $::InternalTree::*::**;}
                    class InternalChild specializes InternalProvider;
                    package CycleTree {public import CycleOther::*;}
                    package CycleOther {public import $::CycleTree::*;}
                    class CycleProvider {public import $::CycleTree::*::**;}
                    class CycleChild specializes CycleProvider;
                    package TypedTree {class OwnedType;}
                    class TypedProvider {public import $::TypedTree::*::**;}
                    class TypedChild specializes TypedProvider;
                    package UnnamedTree {package {alias AnonymousAlias for $::Marker;}}
                    class UnnamedProvider {public import $::UnnamedTree::*::**;}
                    class UnnamedChild specializes UnnamedProvider;
                ";
                let mixed_tree = "
                    package External {alias Imported for $::Definitions::Marker;}
                    package HiddenExternal {private alias Secret for $::Definitions::OtherMarker;}
                    package ImportTree {
                        alias Local for $::Definitions::Marker;
                        public import $::Relay0::*;
                        package Nested {public import all $::HiddenExternal::*;}
                    }
                ";
                let mut mixed_tree = mixed_tree.to_owned();
                // Exercise more semantic import edges than the old helper-call bound admitted.
                for hop in 0..8 {
                    let target = if hop == 7 {
                        "External".to_owned()
                    } else {
                        format!("Relay{}", hop + 1)
                    };
                    mixed_tree.push_str(&format!(
                        "package Relay{hop} {{public import $::{target}::*;}}"
                    ));
                }
                let mixed_consumers = "
                    class MixedProvider {
                        public import $::ImportTree::*::**;
                        public import $::External::*;
                        public import $::Definitions::Marker;
                    }
                    class MixedChild specializes MixedProvider {feature ownMixed;}
                    package MixedConsumer {private import $::ImportTree::*::**;}
                ";
                let tree_path = if qualified { "Catalog::Tree" } else { "Tree" };
                let marker_path = if qualified {
                    "Definitions::Marker"
                } else {
                    "Marker"
                };
                let other_path = if qualified {
                    "Definitions::OtherMarker"
                } else {
                    "OtherMarker"
                };
                let tree = if !qualified {
                    tree.to_owned()
                } else {
                    format!("package Catalog {{ {tree} }}")
                        .replace("$::Marker", "$::Definitions::Marker")
                        .replace("$::OtherMarker", "$::Definitions::OtherMarker")
                };
                let tree = format!("{tree} {mixed_tree}");
                let consumers = format!("{consumers} {mixed_consumers}")
                    .replace("$::Tree", &format!("$::{tree_path}"));
                let source = format!(
                    "class Marker; class OtherMarker; package Definitions {{class Marker; class OtherMarker;}} {} {} {negatives}",
                    if early_tree { &tree } else { &consumers },
                    if early_tree { &consumers } else { &tree }
                );
                let unit = model.add_source("checked-recursive-providers.kerml", &source);
                assert!(
                    unit.diagnostics.is_empty(),
                    "{format:?} early={early_tree} mode={mode}: {:?}",
                    unit.diagnostics
                );
                let mut r = ResolvedModel::build(&model);
                let mixed_child = r.resolve_qualified("MixedChild").unwrap();
                let cold_mixed = inherited(&mut r, mixed_child);
                if format == GraphFormat::CanonicalV3 {
                    assert!(
                        cold_mixed.is_ok(),
                        "cold mixed early={early_tree} mode={mode}: {cold_mixed:?}"
                    );
                } else {
                    assert!(matches!(cold_mixed, Err(OperationError::Incomplete { .. })));
                }
                let namespace_child = r.resolve_qualified("NamespaceChild").unwrap();
                // Cold provider proof, before relationship/feature publication.
                let cold = inherited(&mut r, namespace_child);
                if format == GraphFormat::CanonicalV3 {
                    assert!(cold.is_ok(), "early={early_tree} mode={mode}: {cold:?}");
                } else {
                    assert!(matches!(cold, Err(OperationError::Incomplete { .. })));
                }
                let root_alias = named_member(&mut r, tree_path, "RootAlias");
                let left = membership(&mut r, &format!("{tree_path}::Left"));
                let right = membership(&mut r, &format!("{tree_path}::Right"));
                let hidden = membership(&mut r, &format!("{tree_path}::Hidden"));
                let private_alias = named_member(&mut r, tree_path, "PrivateAlias");
                let deep = named_member(&mut r, &format!("{tree_path}::Left"), "DeepAlias");
                let clash_left = named_member(&mut r, &format!("{tree_path}::Left"), "Clash");
                let clash_right = named_member(&mut r, &format!("{tree_path}::Right"), "Clash");
                let secret = named_member(&mut r, &format!("{tree_path}::Hidden"), "SecretAlias");
                let public = vec![root_alias, left, right, deep, clash_left, clash_right];
                let all = vec![
                    root_alias,
                    left,
                    right,
                    hidden,
                    private_alias,
                    deep,
                    clash_left,
                    clash_right,
                    secret,
                ];
                let mut with_root = vec![membership(&mut r, tree_path)];
                with_root.extend(public.iter().copied());
                let mut identities = Vec::<Vec<String>>::new();
                for (owner, wanted, own_name) in [
                    ("MemberChild", with_root, "ownMember"),
                    ("NamespaceChild", public, "ownNamespace"),
                    ("AllChild", all, "ownAll"),
                ] {
                    let receiver = r.resolve_qualified(owner).unwrap();
                    let actual = inherited(&mut r, receiver);
                    if format == GraphFormat::CanonicalV3 {
                        let actual = actual.unwrap_or_else(|e| {
                            panic!("{owner} early={early_tree} mode={mode}: {e:?}")
                        });
                        assert_eq!(actual, wanted, "exact recursive Membership order: {owner}");
                        identities.push(
                            actual
                                .into_iter()
                                .map(|e| r.element_id(e).to_string())
                                .collect(),
                        );
                        let report = r.type_feature_report(receiver).projections.unwrap();
                        let own = r
                            .resolve_qualified(&format!("{owner}::{own_name}"))
                            .unwrap();
                        assert_eq!(
                            report.owned_feature_memberships,
                            vec![membership(&mut r, &format!("{owner}::{own_name}"))]
                        );
                        assert!(report.features.contains(&own));
                        // Imported aliases to Classes and Package memberships
                        // are bindings, not FeatureMembership slots.
                        let marker = r.resolve_qualified(marker_path).unwrap();
                        let other = r.resolve_qualified(other_path).unwrap();
                        assert!(!report.features.contains(&marker));
                        assert!(!report.features.contains(&other));
                    } else {
                        assert!(matches!(actual, Err(OperationError::Incomplete { .. })));
                    }
                }
                // Actual resolver lookup must consume the recursive tree's
                // descendants and preserve sibling ambiguity rather than first-hit wins.
                let marker = r.resolve_qualified(marker_path).unwrap();
                assert_eq!(
                    r.resolve_qualified("NamespaceChild::DeepAlias"),
                    Some(marker)
                );
                assert_eq!(r.resolve_qualified("NamespaceChild::Clash"), None);
                assert_eq!(r.resolve_qualified("NamespaceChild::SecretAlias"), None);
                assert_eq!(r.resolve_qualified("AllChild::SecretAlias"), Some(marker));
                assert_eq!(r.resolve_qualified("AllChild::PrivateAlias"), Some(marker));
                // Namespace importedMembership prunes the two colliding names;
                // Type visibility-specific inherited memberships retain both.
                let consumer = r.resolve_qualified("NamespaceConsumer").unwrap();
                let report = r
                    .invoke_operation(
                        consumer,
                        "Root-Namespaces-Namespace-importedMemberships_Namespace",
                        &[DerivedValue::Elements(vec![])],
                    )
                    .unwrap();
                assert_eq!(
                    report.value,
                    DerivedValue::References(
                        vec![root_alias, left, right, deep]
                            .into_iter()
                            .map(Reference::Element)
                            .collect()
                    )
                );
                identities.push(
                    vec![root_alias, left, right, deep]
                        .into_iter()
                        .map(|e| r.element_id(e).to_string())
                        .collect(),
                );
                let local = named_member(&mut r, "ImportTree", "Local");
                let nested = membership(&mut r, "ImportTree::Nested");
                let imported = named_member(&mut r, "External", "Imported");
                let secret = named_member(&mut r, "HiddenExternal", "Secret");
                let marker_membership = membership(&mut r, "Definitions::Marker");
                if format == GraphFormat::CanonicalV3 {
                    let wanted = vec![local, nested, imported, secret, marker_membership];
                    assert_eq!(inherited(&mut r, mixed_child).unwrap(), wanted);
                    identities.push(
                        wanted
                            .into_iter()
                            .map(|e| r.element_id(e).to_string())
                            .collect(),
                    );
                    let own = r.resolve_qualified("MixedChild::ownMixed").unwrap();
                    let report = r.type_feature_report(mixed_child).projections.unwrap();
                    assert_eq!(
                        report.owned_feature_memberships,
                        vec![membership(&mut r, "MixedChild::ownMixed")]
                    );
                    assert_eq!(
                        report
                            .features
                            .into_iter()
                            .filter(|&e| !r.is_library_element(e))
                            .collect::<Vec<_>>(),
                        vec![own]
                    );
                }
                let marker = r.resolve_qualified("Definitions::Marker").unwrap();
                let other = r.resolve_qualified("Definitions::OtherMarker").unwrap();
                assert_eq!(r.resolve_qualified("MixedChild::Imported"), Some(marker));
                assert_eq!(r.resolve_qualified("MixedChild::Secret"), Some(other));
                let consumer = r.resolve_qualified("MixedConsumer").unwrap();
                let report = r
                    .invoke_operation(
                        consumer,
                        "Root-Namespaces-Namespace-importedMemberships_Namespace",
                        &[DerivedValue::Elements(vec![])],
                    )
                    .unwrap();
                assert_eq!(
                    report.value,
                    DerivedValue::References(
                        vec![local, nested, imported, secret]
                            .into_iter()
                            .map(Reference::Element)
                            .collect()
                    )
                );
                for owner in ["InternalChild", "CycleChild", "TypedChild", "UnnamedChild"] {
                    let e = r.resolve_qualified(owner).unwrap();
                    assert!(
                        matches!(inherited(&mut r, e), Err(OperationError::Incomplete { .. })),
                        "unsupported recursive provider {owner}"
                    );
                }
                if let Some(expected) = &expected {
                    assert_eq!(
                        &identities, expected,
                        "{format:?} early={early_tree} mode={mode}"
                    );
                } else {
                    expected = Some(identities);
                }
            }
        }
    }
}
