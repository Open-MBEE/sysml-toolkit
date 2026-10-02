//! Foreign imported positional roles cannot be proved by unrelated root order.
use super::*;
use crate::model::{GraphFormat, Model};

const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;}";
fn fixture(
    format: GraphFormat,
    early_foreign: bool,
    ancestor: bool,
    indirect: bool,
    sibling: bool,
) -> ResolvedModel {
    let mut model = Model::with_graph_format(format);
    let library = model.add_library_source("import-dependency-library.kerml", LIB);
    assert!(library.diagnostics.is_empty(), "{:?}", library.diagnostics);
    let foreign = if indirect {
        "class ForeignEndOwner specializes B {end feature a;} class Relay {feature selected redefines ForeignEndOwner::a;} package P {alias importedEnd for Relay::selected;}"
    } else {
        "class ForeignEndOwner specializes B {end feature a;} package P {alias importedEnd for ForeignEndOwner::a;}"
    };
    let consumer = if ancestor {
        "class Provider specializes ForeignEndOwner {public import P::importedEnd;} class Child specializes Provider,B; class Grand specializes Child {end feature g;}"
    } else if sibling {
        "class Provider {public import P::importedEnd;} class Child specializes Provider,B; class Grand specializes Child,ForeignEndOwner {end feature g;}"
    } else {
        "class Provider {public import P::importedEnd;} class Child specializes Provider,B; class Grand specializes Child {end feature g;}"
    };
    let source = format!(
        "class B {{end feature b;}} {} {}",
        if early_foreign { foreign } else { consumer },
        if early_foreign { consumer } else { foreign }
    );
    let unit = model.add_source("import-dependency.kerml", &source);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

#[test]
fn foreign_alias_dependencies_are_scheduled_only_for_the_supported_canonical_domain() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for early_foreign in [true, false] {
            for indirect in [false, true] {
                let mut r = fixture(format, early_foreign, false, indirect, false);
                let grand = r.resolve_qualified("Grand").unwrap().0;
                let provider = r.resolve_qualified("Provider").unwrap().0;
                let package = r.resolve_qualified("P").unwrap().0;
                if format == GraphFormat::CanonicalV3 {
                    let g = r.resolve_qualified("Grand::g").unwrap().0;
                    let a = r.resolve_qualified("ForeignEndOwner::a").unwrap().0;
                    let b = r.resolve_qualified("B::b").unwrap().0;
                    assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
                    let published = r.b.positional_redefinitions.as_ref().unwrap();
                    assert!(!published.targets.contains_key(&g));
                    assert!(!published.incomplete.contains(&grand));
                    assert_eq!(published.targets.get(&a), Some(&vec![b]));
                }
                // Canonical orders the foreign end owner before Provider.
                // The indirect non-end relay is a structural query fixture, not
                // a claim of whole-model Redefinition end conformance.
                for (namespaces, types) in [(vec![], vec![]), (vec![package], vec![provider])] {
                    let result = r.b.checked_type_membership_operation(
                        grand,
                        &namespaces,
                        &types,
                        true,
                        &mut 0,
                    );
                    if format == GraphFormat::CanonicalV3 && !indirect {
                        let proof = result.unwrap_or_else(|e| {
                            panic!("{format:?} early_foreign={early_foreign}: {e:?}")
                        });
                        assert_eq!(proof.inherited.len(), 1);
                        let g = r.resolve_qualified("Grand::g").unwrap().0;
                        assert!(!proof.required_positional.contains_key(&g));
                    } else {
                        assert!(
                            result.is_err(),
                            "{format:?} early_foreign={early_foreign} indirect={indirect}"
                        );
                    }
                }
                assert_eq!(
                    r.type_feature_report(ElementRef(grand)).projections.is_ok(),
                    format == GraphFormat::CanonicalV3 && !indirect
                );
            }
        }
    }
}

#[test]
fn imported_positional_owner_in_contribution_ancestry_keeps_the_ordered_proof() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for early_foreign in [true, false] {
            let mut r = fixture(format, early_foreign, true, false, false);
            let grand = r.resolve_qualified("Grand").unwrap().0;
            let g = r.resolve_qualified("Grand::g").unwrap().0;
            let a = r.resolve_qualified("ForeignEndOwner::a").unwrap().0;
            let b = r.resolve_qualified("B::b").unwrap().0;
            let proof =
                r.b.checked_type_membership_operation(grand, &[], &[], true, &mut 0)
                    .unwrap_or_else(|e| panic!("{format:?} early_foreign={early_foreign}: {e:?}"));
            assert!(proof.inherited.is_empty());
            assert_eq!(proof.required_positional.get(&a), Some(&vec![b]));
            assert!(
                !proof.required_positional.contains_key(&g),
                "suppressed ancestor ends do not create a Grand positional target"
            );
        }
    }
}

#[test]
fn canonical_prerequisites_order_the_importing_branch_before_a_sibling_contributes() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for early_foreign in [true, false] {
            let mut r = fixture(format, early_foreign, false, false, true);
            let grand = r.resolve_qualified("Grand").unwrap().0;
            let proof =
                r.b.checked_type_membership_operation(grand, &[], &[], true, &mut 0);
            if format == GraphFormat::CanonicalV3 {
                let g = r.resolve_qualified("Grand::g").unwrap().0;
                let a = r.resolve_qualified("ForeignEndOwner::a").unwrap().0;
                let proof = proof
                    .unwrap_or_else(|e| panic!("{format:?} early_foreign={early_foreign}: {e:?}"));
                assert_eq!(proof.required_positional.get(&g), Some(&vec![a]));
                assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
                assert_eq!(
                    r.b.positional_redefinitions
                        .as_ref()
                        .unwrap()
                        .targets
                        .get(&g),
                    Some(&vec![a])
                );
            } else {
                assert!(proof.is_err());
            }
        }
    }
}

#[test]
fn direct_foreign_end_prerequisites_preserve_feature_slots_and_retry() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut model = Model::with_graph_format(format);
        assert!(
            model
                .add_library_source("end-library.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        let unit = model.add_source("direct-end-prerequisite.kerml", "class BaseOwner {end feature baseEnd;} class Foreign specializes BaseOwner {end feature selected; feature unrelated;} class Provider {public import Foreign::selected;} class Intermediate specializes Provider; class Child specializes Intermediate {end feature replacement;}");
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let child = r.resolve_qualified("Child").unwrap().0;
        let replacement = r.resolve_qualified("Child::replacement").unwrap().0;
        let selected = r.resolve_qualified("Foreign::selected").unwrap().0;
        let base = r.resolve_qualified("BaseOwner::baseEnd").unwrap().0;
        let unrelated = r.resolve_qualified("Foreign::unrelated").unwrap();
        let mut exhausted = crate::eval::MAX_STEPS;
        assert!(
            r.b.checked_type_membership_operation(child, &[], &[], true, &mut exhausted)
                .is_err()
        );
        let result =
            r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0);
        if format == GraphFormat::LegacyV2 {
            assert!(result.is_err());
            continue;
        }
        let proof = result.unwrap();
        assert_eq!(proof.required_positional.get(&selected), Some(&vec![base]));
        assert_eq!(
            proof.required_positional.get(&replacement),
            Some(&vec![selected])
        );
        assert!(proof.inherited.is_empty());
        let features = r
            .type_feature_report(ElementRef(child))
            .projections
            .unwrap();
        assert!(!features.features.contains(&unrelated));
        for missing in [false, true] {
            if missing {
                let original = r.b.elements[selected].props.to_json();
                let mut without_end = crate::properties::Properties::new();
                for (key, value) in original {
                    if key != "isEnd" {
                        without_end.insert(&key, value);
                    }
                }
                r.b.elements[selected].props = without_end;
            } else {
                r.b.set(selected, "isEnd", serde_json::json!(false));
            }
            assert!(
                r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
                    .is_err()
            );
            r.b.set(selected, "isEnd", serde_json::json!(true));
        }
        r.b.set(selected, "direction", serde_json::json!("in"));
        assert!(
            r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
                .is_err()
        );
        r.b.set(selected, "direction", serde_json::Value::Null);
        assert_eq!(
            r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
                .unwrap()
                .required_positional
                .get(&replacement),
            Some(&vec![selected])
        );
    }
}

#[test]
fn foreign_owner_mixed_sources_and_cyclic_dependencies_remain_qualified() {
    for source in [
        // An unimported ordinary Feature still changes the owner's end reduction.
        "class Other {end feature otherEnd;} class Foreign {end feature selected; feature ordinary redefines Other::otherEnd;} class Provider {public import Foreign::selected;} class Child specializes Provider {end feature replacement;}",
        "class Other {end feature otherEnd;} class Foreign {end feature selected redefines Other::otherEnd;} class Provider {public import Foreign::selected;} class Child specializes Provider {end feature replacement;}",
        // Closing a prerequisite through real inheritance must not become a base.
        "class Provider {public import Foreign::selected;} class Foreign specializes Provider {end feature selected;} class Child specializes Provider {end feature replacement;}",
    ] {
        let mut model = Model::with_graph_format(GraphFormat::CanonicalV3);
        assert!(
            model
                .add_library_source("end-library.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        let unit = model.add_source("incomplete-end-prerequisite.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let child = r.resolve_qualified("Child").unwrap().0;
        let provider = r.resolve_qualified("Provider").unwrap().0;
        let replacement = r.resolve_qualified("Child::replacement").unwrap().0;
        for excluded in [vec![], vec![provider]] {
            assert!(
                r.b.checked_type_membership_operation(child, &[], &excluded, true, &mut 0)
                    .is_err(),
                "{source}"
            );
        }
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(
            !r.b.positional_redefinitions
                .as_ref()
                .unwrap()
                .targets
                .contains_key(&replacement)
        );
    }
}
