//! Canonical import planning widens complete selectors without changing Legacy publication.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, OperationError, Reference, ResolvedModel},
    libcache::LibraryCache,
    model::{GraphFormat, Model},
    prepared::PreparedLibrary,
};

const OP: &str = "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean";
fn inherited(
    r: &mut ResolvedModel,
    owner: ElementRef,
    excluded: Vec<ElementRef>,
) -> Result<Vec<ElementRef>, OperationError> {
    let report = r.invoke_operation(
        owner,
        OP,
        &[
            DerivedValue::Elements(excluded),
            DerivedValue::Elements(vec![]),
            DerivedValue::Bool(true),
        ],
    )?;
    let DerivedValue::References(values) = report.value else {
        panic!("expected memberships")
    };
    Ok(values
        .into_iter()
        .map(|value| match value {
            Reference::Element(e) => e,
            _ => panic!("expected loaded membership identity"),
        })
        .collect())
}
fn member(r: &mut ResolvedModel, owner: &str, name: &str) -> ElementRef {
    let owner = r.resolve_qualified(owner).unwrap();
    r.owned_relationships(owner)
        .into_iter()
        .find(|&m| r.membership_member_name(m).as_deref() == Some(name))
        .unwrap_or_else(|| panic!("missing {name}"))
}
fn implied_redefinitions(r: &mut ResolvedModel, name: &str) -> Vec<(String, String)> {
    let owner = r.resolve_qualified(name).unwrap();
    r.implied_relationships(owner)
        .into_iter()
        .filter(|&e| r.element_type(e) == "Redefinition")
        .collect::<Vec<_>>()
        .into_iter()
        .map(|e| {
            let id = r.element_id(e).to_string();
            let target = r.property(e, "redefinedFeature").unwrap()["@id"]
                .as_str()
                .unwrap()
                .to_owned();
            (id, target)
        })
        .collect()
}
#[test]
fn canonical_package_and_direct_member_import_planning_preserves_actual_library_replay() {
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
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(83).unwrap(), 83).unwrap());
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
            let unit = model.add_source(
                "checked-import-planning.kerml",
                "
                package External {class Scalar;}
                package Leaf {alias scalarAlias for External::Scalar;}
                package Middle {
                    package Nested {alias nestedAlias for External::Scalar;}
                    public import Leaf::*;
                }
                class TransitiveProvider {public import Middle::*;}
                class TransitiveChild specializes TransitiveProvider;
                class RecursiveProvider {public import Middle::**;}
                class RecursiveChild specializes RecursiveProvider;
                class Ancestor {feature seed;}
                class Declaring specializes Ancestor {
                    feature selected redefines Ancestor::seed;
                    feature unrelated;
                }
                class DirectProvider {
                    public import Declaring::selected;
                    public import Ancestor::seed;
                }
                class DirectChild specializes DirectProvider;
                class RedefinedChild specializes DirectProvider {
                    feature replacement redefines Declaring::selected;
                }
                package MarkerLeaf {class Marker;}
                package Reexport {public import MarkerLeaf::*;}
                class BaseOwner {public import Reexport::*; end feature original;}
                class Child specializes BaseOwner {end feature replacement;}
                class EndBase {end feature baseEnd;}
                class EndOwner specializes EndBase {end feature importedEnd;}
                class EndProvider {public import EndOwner::importedEnd;}
                class EndBridge specializes EndProvider;
                class EndChild specializes EndBridge {end feature childEnd;}
            ",
            );
            assert!(
                unit.diagnostics.is_empty(),
                "{format:?} replay {mode}: {:?}",
                unit.diagnostics
            );
            let mut r = ResolvedModel::build(&model);
            let transitive = r.resolve_qualified("TransitiveChild").unwrap();
            let recursive = r.resolve_qualified("RecursiveChild").unwrap();
            let direct = r.resolve_qualified("DirectChild").unwrap();
            let redefined = r.resolve_qualified("RedefinedChild").unwrap();
            let child = r.resolve_qualified("Child").unwrap();
            let middle = r.resolve_qualified("Middle").unwrap();
            let leaf = r.resolve_qualified("Leaf").unwrap();
            let selected = member(&mut r, "Declaring", "selected");
            let nested = member(&mut r, "Middle", "Nested");
            let scalar = member(&mut r, "Leaf", "scalarAlias");
            let marker = member(&mut r, "MarkerLeaf", "Marker");
            let mut identities = Vec::new();
            if format == GraphFormat::CanonicalV3 {
                let cases = [
                    (transitive, vec![], vec![nested, scalar]),
                    (transitive, vec![leaf], vec![nested]),
                    (transitive, vec![middle], vec![]),
                    (direct, vec![], vec![selected]),
                    (redefined, vec![], vec![]),
                    (child, vec![], vec![marker]),
                ];
                for (owner, excluded, expected) in cases {
                    let actual = inherited(&mut r, owner, excluded).unwrap_or_else(|e| {
                        panic!("{format:?} replay {mode} owner {owner:?}: {e:?}")
                    });
                    assert_eq!(actual, expected, "{format:?} replay {mode} owner {owner:?}");
                    identities.push(
                        actual
                            .into_iter()
                            .map(|e| r.element_id(e).to_string())
                            .collect::<Vec<_>>(),
                    );
                }
                let features = r.type_feature_report(direct).projections.unwrap();
                let imported_feature = r.resolve_qualified("Declaring::selected").unwrap();
                let seed = r.resolve_qualified("Ancestor::seed").unwrap();
                let unrelated = r.resolve_qualified("Declaring::unrelated").unwrap();
                assert!(features.inherited_features.contains(&imported_feature));
                assert!(!features.inherited_features.contains(&seed));
                assert!(!features.features.contains(&unrelated));
            } else {
                for owner in [transitive, recursive, direct, redefined, child] {
                    assert!(
                        matches!(
                            inherited(&mut r, owner, vec![]),
                            Err(OperationError::Incomplete { .. })
                        ),
                        "{format:?} replay {mode} owner {owner:?}"
                    );
                }
            }
            // The central selector can traverse these packages, but the shared
            // Type scope provider still qualifies recursive name dependencies.
            // Exclusions cannot turn that incomplete provider into a certificate.
            for excluded in [vec![], vec![middle]] {
                assert!(
                    matches!(
                        inherited(&mut r, recursive, excluded),
                        Err(OperationError::Incomplete { .. })
                    ),
                    "{format:?} replay {mode}"
                );
            }
            let edges = implied_redefinitions(&mut r, "Child::replacement");
            let original = r.resolve_qualified("BaseOwner::original").unwrap();
            if format == GraphFormat::CanonicalV3 {
                assert_eq!(edges.len(), 1, "{format:?} replay {mode}");
                assert_eq!(edges[0].1, r.element_id(original).to_string());
            } else {
                assert!(edges.is_empty(), "Legacy publication must remain unchanged");
            }
            identities.push(
                edges
                    .iter()
                    .flat_map(|(id, target)| [id.clone(), target.clone()])
                    .collect(),
            );
            // Canonical can now schedule this exact ordinary end's owner as
            // a prerequisite without making that owner an inherited base.
            let end_child = r.resolve_qualified("EndChild").unwrap();
            let end_edges = implied_redefinitions(&mut r, "EndChild::childEnd");
            if format == GraphFormat::CanonicalV3 {
                assert!(inherited(&mut r, end_child, vec![]).unwrap().is_empty());
                let selected = r.resolve_qualified("EndOwner::importedEnd").unwrap();
                assert_eq!(end_edges.len(), 1, "{format:?} replay {mode}");
                assert_eq!(end_edges[0].1, r.element_id(selected).to_string());
            } else {
                assert!(matches!(
                    inherited(&mut r, end_child, vec![]),
                    Err(OperationError::Incomplete { .. })
                ));
                assert!(end_edges.is_empty());
            }
            identities.push(
                end_edges
                    .into_iter()
                    .flat_map(|(id, target)| [id, target])
                    .collect(),
            );
            let owner_edges = implied_redefinitions(&mut r, "EndOwner::importedEnd");
            let base_end = r.resolve_qualified("EndBase::baseEnd").unwrap();
            assert_eq!(owner_edges.len(), 1, "{format:?} replay {mode}");
            assert_eq!(owner_edges[0].1, r.element_id(base_end).to_string());
            identities.push(
                owner_edges
                    .into_iter()
                    .flat_map(|(id, target)| [id, target])
                    .collect(),
            );
            if let Some(expected) = &expected_ids {
                assert_eq!(&identities, expected, "{format:?} replay {mode}");
            } else {
                expected_ids = Some(identities);
            }
        }
    }
}
