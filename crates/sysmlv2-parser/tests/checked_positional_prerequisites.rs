//! Foreign end prerequisites order the existing reduction without adding inheritance.
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
    let owner = r.resolve_qualified(name).unwrap();
    let rows = r
        .implied_relationships(owner)
        .into_iter()
        .filter(|&e| r.element_type(e) == "Redefinition")
        .collect::<Vec<_>>();
    rows.into_iter()
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
fn id(r: &mut ResolvedModel, name: &str) -> String {
    let e = r.resolve_qualified(name).unwrap();
    r.element_id(e).to_string()
}
#[test]
fn canonical_foreign_end_prerequisites_preserve_actual_library_order_and_replay() {
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
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(89).unwrap(), 89).unwrap());
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
                let foreign = "class Foreign specializes BaseOwner {end feature a; class Unrelated;} package Aliases {alias selected for Foreign::a;}";
                let consumers = "
                    class DirectProvider {public import Foreign::a;}
                    class DirectChild specializes DirectProvider;
                    class DirectGrand specializes DirectChild {end feature d;}
                    class AliasProvider {public import Aliases::selected;}
                    class AliasChild specializes AliasProvider,BaseOwner;
                    class AliasGrand specializes AliasChild {end feature g;}
                    class SiblingGrand specializes AliasChild,Foreign {end feature s;}
                ";
                let mixed = "
                    class OtherForeign {end feature outside;}
                    class MixedOwner specializes BaseOwner {
                        end feature a;
                        feature ordinary redefines OtherForeign::outside;
                    }
                    class MixedProvider {public import MixedOwner::a;}
                    class MixedChild specializes MixedProvider {end feature m;}
                ";
                let source = format!(
                    "class BaseOwner {{end feature b;}} {} {} {mixed}",
                    if early_foreign { foreign } else { consumers },
                    if early_foreign { consumers } else { foreign }
                );
                let unit = model.add_source("checked-prerequisites.kerml", &source);
                assert!(
                    unit.diagnostics.is_empty(),
                    "{format:?} early={early_foreign} mode={mode}: {:?}",
                    unit.diagnostics
                );
                let mut r = ResolvedModel::build(&model);
                let direct = r.resolve_qualified("DirectGrand").unwrap();
                // The first checked query must establish prerequisites itself;
                // no prior implied relationship read may warm the proof.
                let cold = inherited(&mut r, direct);
                if format == GraphFormat::CanonicalV3 {
                    assert_eq!(cold.unwrap(), vec![], "early={early_foreign} mode={mode}");
                } else {
                    assert!(matches!(cold, Err(OperationError::Incomplete { .. })));
                }
                let alias_child = r.resolve_qualified("AliasChild").unwrap();
                let alias_grand = r.resolve_qualified("AliasGrand").unwrap();
                let sibling = r.resolve_qualified("SiblingGrand").unwrap();
                let alias_owner = r.resolve_qualified("Aliases").unwrap();
                let selected = r
                    .owned_relationships(alias_owner)
                    .into_iter()
                    .find(|&m| r.membership_member_name(m).as_deref() == Some("selected"))
                    .unwrap();
                let a_id = id(&mut r, "Foreign::a");
                let b_id = id(&mut r, "BaseOwner::b");
                let foreign_edges = edges(&mut r, "Foreign::a");
                assert_eq!(
                    foreign_edges.len(),
                    1,
                    "{format:?} early={early_foreign} mode={mode}"
                );
                assert_eq!(foreign_edges[0].1, b_id);
                let direct_edges = edges(&mut r, "DirectGrand::d");
                let alias_edges = edges(&mut r, "AliasGrand::g");
                let sibling_edges = edges(&mut r, "SiblingGrand::s");
                let mut identities = Vec::<Vec<String>>::new();
                if format == GraphFormat::CanonicalV3 {
                    assert_eq!(direct_edges.len(), 1, "early={early_foreign} mode={mode}");
                    assert_eq!(direct_edges[0].1, a_id);
                    assert!(
                        alias_edges.is_empty(),
                        "alias suppression cannot create a positional slot"
                    );
                    assert_eq!(sibling_edges.len(), 1, "early={early_foreign} mode={mode}");
                    assert_eq!(
                        sibling_edges[0].1, a_id,
                        "sibling must inherit Foreign::a, never the suppressed BaseOwner::b"
                    );
                    for (owner, want) in [
                        (direct, vec![]),
                        (alias_child, vec![selected]),
                        (alias_grand, vec![selected]),
                    ] {
                        let actual = inherited(&mut r, owner).unwrap_or_else(|e| {
                            panic!("early={early_foreign} mode={mode} {owner:?}: {e:?}")
                        });
                        assert_eq!(actual, want, "early={early_foreign} mode={mode}");
                        identities.push(
                            actual
                                .into_iter()
                                .map(|e| r.element_id(e).to_string())
                                .collect(),
                        );
                    }
                    let alias_features = r.type_feature_report(alias_child).projections.unwrap();
                    assert!(!alias_features.inherited_features.iter().any(|&e| {
                        let id = r.element_id(e).to_string();
                        id == a_id || id == b_id
                    }));
                    let direct_features = r.type_feature_report(direct).projections.unwrap();
                    let own = r.resolve_qualified("DirectGrand::d").unwrap();
                    assert!(direct_features.features.contains(&own));
                    assert!(
                        !direct_features.inherited_features.iter().any(|&e| r
                            .element_id(e)
                            .to_string()
                            == a_id
                            || r.element_id(e).to_string() == b_id)
                    );
                    // The foreign owner's unrelated class can contribute only
                    // through the genuine sibling base, never a prerequisite.
                    let unrelated = r.resolve_qualified("Foreign::Unrelated").unwrap();
                    let unrelated = r.property(unrelated, "owningRelationship").unwrap();
                    let unrelated = r.element_by_id(unrelated["@id"].as_str().unwrap()).unwrap();
                    assert_eq!(inherited(&mut r, sibling).unwrap(), vec![unrelated]);
                } else {
                    for owner in [direct, alias_child, alias_grand, sibling] {
                        assert!(
                            matches!(
                                inherited(&mut r, owner),
                                Err(OperationError::Incomplete { .. })
                            ),
                            "early={early_foreign} mode={mode}"
                        );
                    }
                    assert!(
                        direct_edges.is_empty(),
                        "Legacy direct foreign end publication is unchanged"
                    );
                }
                let mixed = r.resolve_qualified("MixedChild").unwrap();
                assert!(
                    matches!(
                        inherited(&mut r, mixed),
                        Err(OperationError::Incomplete { .. })
                    ),
                    "mixed owner source closure must remain qualified"
                );
                assert!(edges(&mut r, "MixedChild::m").is_empty());
                for rows in [foreign_edges, direct_edges, alias_edges, sibling_edges] {
                    identities.push(
                        rows.into_iter()
                            .flat_map(|(id, target)| [id, target])
                            .collect(),
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
