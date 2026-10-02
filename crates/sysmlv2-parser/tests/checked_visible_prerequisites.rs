//! Visible package imports on prerequisite owners preserve selected contribution identity.
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
fn edges(r: &mut ResolvedModel, name: &str) -> Vec<(String, String)> {
    let e = r.resolve_qualified(name).unwrap();
    let rows = r
        .implied_relationships(e)
        .into_iter()
        .filter(|&e| r.element_type(e) == "Redefinition")
        .collect::<Vec<_>>();
    rows.into_iter()
        .map(|e| {
            (
                r.element_id(e).to_string(),
                r.property(e, "redefinedFeature").unwrap()["@id"]
                    .as_str()
                    .unwrap()
                    .to_owned(),
            )
        })
        .collect()
}
fn id(r: &mut ResolvedModel, name: &str) -> String {
    let e = r.resolve_qualified(name).unwrap();
    r.element_id(e).to_string()
}
fn membership(r: &mut ResolvedModel, name: &str) -> ElementRef {
    let e = r.resolve_qualified(name).unwrap();
    let value = r.property(e, "owningRelationship").unwrap();
    r.element_by_id(value["@id"].as_str().unwrap()).unwrap()
}
fn named_membership(r: &mut ResolvedModel, owner: &str, name: &str) -> ElementRef {
    let owner = r.resolve_qualified(owner).unwrap();
    r.owned_relationships(owner)
        .into_iter()
        .find(|&m| r.membership_member_name(m).as_deref() == Some(name))
        .unwrap()
}
#[test]
fn canonical_visible_prerequisites_preserve_actual_library_imports_and_replay() {
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
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(95).unwrap(), 95).unwrap());
        for early_foreign in [true, false] {
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
                let catalogs="
                    package PublicNamed {class Named;}
                    package PublicNamespace {class ViaNamespace; alias NamedAlias for PublicNamed::Named;}
                    package ProtectedNamed {class Hidden;}
                    package ProtectedNamespace {class ViaProtected;}
                    package AncestorCatalog {class AncestorMarker;}
                    package FeatureCatalog {feature packageFeature;}
                    class Tools {feature slot;}
                    package FeatureAliases {alias typeSlotAlias for Tools::slot;}
                ";
                let mut foreign = String::new();
                let mut consumers = String::new();
                for (family, kind, role) in [
                    ("End", "class", "end feature"),
                    ("Input", "behavior", "in"),
                    ("Result", "function", "return"),
                ] {
                    foreign.push_str(&format!(
                        "{kind} Base{family} {{public import AncestorCatalog::*; {role} original;}}
                        {kind} Foreign{family} specializes Base{family} {{
                            public import PublicNamed::Named;
                            public import PublicNamespace::*;
                            protected import ProtectedNamed::Hidden;
                            protected import ProtectedNamespace::*;
                            public import FeatureCatalog::*;
                            public import FeatureAliases::typeSlotAlias;
                            {role} selected;
                        }}"
                    ));
                    consumers.push_str(&format!(
                        "{kind} Provider{family} {{public import Foreign{family}::selected;}}
                        {kind} Bridge{family} specializes Provider{family};
                        {kind} Child{family} specializes Bridge{family} {{{role} replacement;}}
                        {kind} RealChild{family} specializes Foreign{family};"
                    ));
                }
                let negatives="
                    class OtherRole {end feature outside;}
                    package RoleAliases {alias outsideAlias for OtherRole::outside;}
                    class NestedRoleOwner specializes BaseEnd {public import RoleAliases::*; end feature nested;}
                    class NestedProvider {public import NestedRoleOwner::nested;}
                    class NestedChild specializes NestedProvider;
                    package RecursiveCatalog {package Inner {class Item;}}
                    class RecursiveOwner specializes BaseEnd {public import RecursiveCatalog::**; end feature recursiveEnd;}
                    class RecursiveProvider {public import RecursiveOwner::recursiveEnd;}
                    class RecursiveChild specializes RecursiveProvider;
                ";
                let source = format!(
                    "{catalogs} {} {} {negatives}",
                    if early_foreign { &foreign } else { &consumers },
                    if early_foreign { &consumers } else { &foreign }
                );
                let unit = model.add_source("checked-visible-prerequisites.kerml", &source);
                assert!(
                    unit.diagnostics.is_empty(),
                    "{format:?} early={early_foreign} mode={mode}: {:?}",
                    unit.diagnostics
                );
                let mut r = ResolvedModel::build(&model);
                let cold_owner = r.resolve_qualified("ChildResult").unwrap();
                let cold = inherited(&mut r, cold_owner);
                if format == GraphFormat::CanonicalV3 {
                    assert_eq!(cold.unwrap(), vec![], "early={early_foreign} mode={mode}");
                } else {
                    assert!(matches!(cold, Err(OperationError::Incomplete { .. })));
                }
                let mut identities = Vec::<Vec<String>>::new();
                for family in ["End", "Input", "Result"] {
                    let foreign_name = format!("Foreign{family}::selected");
                    let selected = id(&mut r, &foreign_name);
                    let own_name = format!("Child{family}::replacement");
                    let foreign_edges = edges(&mut r, &foreign_name);
                    let child_edges = edges(&mut r, &own_name);
                    let child = r.resolve_qualified(&format!("Child{family}")).unwrap();
                    let real = r.resolve_qualified(&format!("RealChild{family}")).unwrap();
                    if format == GraphFormat::CanonicalV3 {
                        assert_eq!(foreign_edges.len(), 1);
                        assert_eq!(
                            foreign_edges[0].1,
                            id(&mut r, &format!("Base{family}::original"))
                        );
                        // An imported end, input or result is a slot one
                        // inheritance step later, which the child's own takes
                        // over.
                        let inherited_child = inherited(&mut r, child).unwrap();
                        assert_eq!(child_edges.len(), 1, "{family}");
                        assert_eq!(child_edges[0].1, selected, "{family}");
                        assert!(
                            inherited_child.is_empty(),
                            "proof-only foreign imports must not contribute: {family}"
                        );
                        identities.push(
                            inherited_child
                                .into_iter()
                                .map(|e| r.element_id(e).to_string())
                                .collect(),
                        );
                        let wanted = vec![
                            membership(&mut r, &foreign_name),
                            membership(&mut r, "PublicNamed::Named"),
                            membership(&mut r, "PublicNamespace::ViaNamespace"),
                            named_membership(&mut r, "PublicNamespace", "NamedAlias"),
                            membership(&mut r, "FeatureCatalog::packageFeature"),
                            named_membership(&mut r, "FeatureAliases", "typeSlotAlias"),
                            membership(&mut r, "ProtectedNamed::Hidden"),
                            membership(&mut r, "ProtectedNamespace::ViaProtected"),
                            membership(&mut r, "AncestorCatalog::AncestorMarker"),
                        ];
                        let inherited_real = inherited(&mut r, real).unwrap();
                        assert_eq!(
                            inherited_real, wanted,
                            "real inheritance contributes public/protected imports in order: {family} early={early_foreign} mode={mode}"
                        );
                        identities.push(
                            inherited_real
                                .into_iter()
                                .map(|e| r.element_id(e).to_string())
                                .collect(),
                        );
                        // Package-owned Feature and alias-to-Type Feature retain
                        // their memberships but create no FeatureMembership slot.
                        let report = r.type_feature_report(real).projections.unwrap();
                        for name in ["FeatureCatalog::packageFeature", "Tools::slot"] {
                            let e = r.resolve_qualified(name).unwrap();
                            assert!(!report.features.contains(&e));
                        }
                    } else {
                        assert!(matches!(
                            inherited(&mut r, child),
                            Err(OperationError::Incomplete { .. })
                        ));
                    }
                    for rows in [foreign_edges, child_edges] {
                        identities.push(
                            rows.into_iter()
                                .flat_map(|(id, target)| [id, target])
                                .collect(),
                        );
                    }
                }
                for owner in ["NestedChild", "RecursiveChild"] {
                    let e = r.resolve_qualified(owner).unwrap();
                    assert!(
                        matches!(inherited(&mut r, e), Err(OperationError::Incomplete { .. })),
                        "nested external role or recursive lookup remains qualified: {owner}"
                    );
                }
                if let Some(expected) = &expected {
                    assert_eq!(
                        &identities, expected,
                        "{format:?} early={early_foreign} mode={mode}"
                    );
                } else {
                    expected = Some(identities);
                }
            }
        }
    }
}
