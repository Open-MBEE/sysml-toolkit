//! Imported Type memberships and recursive Feature namespaces preserve replay evidence.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, OperationError, Reference, ResolvedModel},
    libcache::LibraryCache,
    model::{GraphFormat, Model},
    prepared::PreparedLibrary,
};

fn invoke(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    operation: &str,
    arguments: &[DerivedValue],
) -> Vec<ElementRef> {
    let report = r.invoke_operation(receiver, operation, arguments).unwrap();
    let DerivedValue::References(values) = report.value else {
        panic!("expected Membership references");
    };
    values
        .into_iter()
        .map(|value| match value {
            Reference::Element(e) => e,
            _ => panic!("expected loaded Membership identity"),
        })
        .collect()
}
fn membership(r: &mut ResolvedModel, owner: &str, name: &str) -> ElementRef {
    let owner = r.resolve_qualified(owner).unwrap();
    let values = r.property(owner, "ownedMembership").unwrap();
    values
        .as_array()
        .unwrap()
        .iter()
        .find_map(|value| {
            let member = r.element_by_id(value["@id"].as_str().unwrap()).unwrap();
            (r.membership_member_name(member).as_deref() == Some(name)).then_some(member)
        })
        .unwrap_or_else(|| panic!("missing owned Membership {name}"))
}
fn inherited(
    r: &mut ResolvedModel,
    owner: ElementRef,
    namespaces: Vec<ElementRef>,
    types: Vec<ElementRef>,
) -> Vec<ElementRef> {
    invoke(
        r,
        owner,
        "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean",
        &[
            DerivedValue::Elements(namespaces),
            DerivedValue::Elements(types),
            DerivedValue::Bool(true),
        ],
    )
}
fn visible(
    r: &mut ResolvedModel,
    owner: ElementRef,
    recursive: bool,
    all: bool,
) -> Vec<ElementRef> {
    invoke(
        r,
        owner,
        "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean",
        &[
            DerivedValue::Elements(vec![]),
            DerivedValue::Bool(recursive),
            DerivedValue::Bool(all),
        ],
    )
}

#[test]
fn type_imports_and_recursive_feature_visibility_preserve_actual_library_replay() {
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
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(79).unwrap(), 79).unwrap());
        let mut expected_ids = None;
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
            let source = "package Sources {
                class LocalType;
                alias NamedType for LocalType;
                feature packageSlot;
                class Slots { feature original; feature kept; }
                alias importedOriginal for Slots::original;
                alias importedKept for Slots::kept;
            }
            class Provider {
                public import Sources::NamedType;
                public import Sources::packageSlot;
                public import Sources::importedOriginal;
                protected import Sources::importedKept;
                protected feature ownProtected;
            }
            class Child specializes Provider { feature replacement redefines Sources::Slots::original; }
            package Leaf { class LeafType; }
            class LeafProvider { public import Leaf::*; }
            class LeafChild specializes LeafProvider;
            class UnsupportedProvider { public import Sources::Slots::original; }
            classifier BaseType { class Inherited; }
            class Outer {
                feature plain;
                feature typedSlot : BaseType { class Local; }
                private feature hidden { class Secret; }
            }
            package Consumer { public import Outer::**; }";
            let unit = model.add_source("checked-type-imports.kerml", source);
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            let mut r = ResolvedModel::build(&model);
            let child = r.resolve_qualified("Child").unwrap();
            let provider = r.resolve_qualified("Provider").unwrap();
            let sources = r.resolve_qualified("Sources").unwrap();
            let named = membership(&mut r, "Sources", "NamedType");
            let package_slot = membership(&mut r, "Sources", "packageSlot");
            let original_alias = membership(&mut r, "Sources", "importedOriginal");
            let kept_alias = membership(&mut r, "Sources", "importedKept");
            let protected = membership(&mut r, "Provider", "ownProtected");
            let replacement = membership(&mut r, "Child", "replacement");
            assert!(r.membership_is_alias(named));
            assert!(r.membership_is_alias(original_alias));
            assert!(r.membership_is_alias(kept_alias));
            let inherited_members = inherited(&mut r, child, vec![], vec![]);
            assert_eq!(
                inherited_members,
                vec![named, package_slot, protected, kept_alias],
                "{format:?} replay {mode}"
            );
            let inheritable = invoke(
                &mut r,
                child,
                "Core-Types-Type-inheritableMemberships_Namespace_Type_Boolean",
                &[
                    DerivedValue::Elements(vec![]),
                    DerivedValue::Elements(vec![]),
                    DerivedValue::Bool(true),
                ],
            );
            assert_eq!(
                inheritable,
                vec![named, package_slot, original_alias, protected, kept_alias]
            );
            let nonprivate = invoke(
                &mut r,
                child,
                "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean",
                &[
                    DerivedValue::Elements(vec![]),
                    DerivedValue::Elements(vec![]),
                    DerivedValue::Bool(true),
                ],
            );
            assert_eq!(
                nonprivate,
                vec![replacement, named, package_slot, protected, kept_alias]
            );
            assert_eq!(
                inherited(&mut r, child, vec![sources], vec![]),
                inherited_members,
                "direct MembershipImport retains its selected membership when its declaring namespace is excluded"
            );
            assert!(inherited(&mut r, child, vec![], vec![provider]).is_empty());
            let public = visible(&mut r, child, false, false);
            let relevant = [
                replacement,
                named,
                package_slot,
                original_alias,
                protected,
                kept_alias,
            ];
            assert_eq!(
                public
                    .iter()
                    .copied()
                    .filter(|e| relevant.contains(e))
                    .collect::<Vec<_>>(),
                vec![replacement, named, package_slot, kept_alias]
            );
            // Inherited visibility tests the original Membership's visibility;
            // the public kept alias remains public after a protected import.
            assert!(!public.contains(&protected));
            let features = r.type_feature_report(child).projections.unwrap();
            let kept = r.resolve_qualified("Sources::Slots::kept").unwrap();
            let package_feature = r.resolve_qualified("Sources::packageSlot").unwrap();
            assert!(!features.inherited_features.contains(&kept));
            assert!(!features.inherited_features.contains(&package_feature));
            assert!(
                features
                    .inherited_features
                    .contains(&r.resolve_qualified("Provider::ownProtected").unwrap())
            );
            let leaf = r.resolve_qualified("Leaf").unwrap();
            let leaf_child = r.resolve_qualified("LeafChild").unwrap();
            let leaf_type = membership(&mut r, "Leaf", "LeafType");
            let leaf_members = inherited(&mut r, leaf_child, vec![], vec![]);
            assert_eq!(leaf_members, vec![leaf_type]);
            assert!(inherited(&mut r, leaf_child, vec![leaf], vec![]).is_empty());
            let unsupported = r.resolve_qualified("UnsupportedProvider").unwrap();
            let direct_import = r.invoke_operation(
                unsupported,
                "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean",
                &[
                    DerivedValue::Elements(vec![]),
                    DerivedValue::Elements(vec![]),
                    DerivedValue::Bool(true),
                ],
            );
            if format == GraphFormat::CanonicalV3 {
                let original = membership(&mut r, "Sources::Slots", "original");
                assert_eq!(
                    direct_import.unwrap().value,
                    DerivedValue::References(vec![Reference::Element(original)]),
                    "{format:?} replay {mode}"
                );
            } else {
                assert!(matches!(
                    direct_import,
                    Err(OperationError::Incomplete { .. })
                ));
            }
            let outer = r.resolve_qualified("Outer").unwrap();
            let plain = membership(&mut r, "Outer", "plain");
            let typed = membership(&mut r, "Outer", "typedSlot");
            let hidden = membership(&mut r, "Outer", "hidden");
            let local = membership(&mut r, "Outer::typedSlot", "Local");
            let inherited_type = membership(&mut r, "BaseType", "Inherited");
            let secret = membership(&mut r, "Outer::hidden", "Secret");
            let recursive = visible(&mut r, outer, true, false);
            assert_eq!(recursive, vec![plain, typed, local, inherited_type]);
            let recursive_all = visible(&mut r, outer, true, true);
            assert_eq!(
                recursive_all,
                vec![plain, typed, hidden, local, inherited_type, secret]
            );
            let consumer = r.resolve_qualified("Consumer").unwrap();
            let imported = invoke(
                &mut r,
                consumer,
                "Root-Namespaces-Namespace-importedMemberships_Namespace",
                &[DerivedValue::Elements(vec![])],
            );
            // Outer::** is a recursive MembershipImport: the selected Outer
            // Membership precedes traversal and survives namespace exclusion.
            let outer_membership = r.property(outer, "owningRelationship").unwrap();
            let outer_membership = r
                .element_by_id(outer_membership["@id"].as_str().unwrap())
                .unwrap();
            assert_eq!(
                imported,
                vec![outer_membership, plain, typed, local, inherited_type]
            );
            let excluded = invoke(
                &mut r,
                consumer,
                "Root-Namespaces-Namespace-importedMemberships_Namespace",
                &[DerivedValue::Elements(vec![outer])],
            );
            assert_eq!(excluded, vec![outer_membership]);
            let ids: Vec<Vec<_>> = [
                inherited_members,
                inheritable,
                nonprivate,
                public,
                leaf_members,
                recursive,
                recursive_all,
                imported,
                excluded,
            ]
            .into_iter()
            .map(|members| members.into_iter().map(|e| r.element_id(e)).collect())
            .collect();
            if let Some(expected) = &expected_ids {
                assert_eq!(&ids, expected, "{format:?} replay {mode}");
            } else {
                expected_ids = Some(ids);
            }
        }
    }
}
