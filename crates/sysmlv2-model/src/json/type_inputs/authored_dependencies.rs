//! Authored positional sources depend only on already ordered actual ancestors.
use super::*;
use crate::model::{GraphFormat, Model};
const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
fn fixture(source: &str, format: GraphFormat) -> ResolvedModel {
    let mut model = Model::with_graph_format(format);
    assert!(
        model
            .add_library_source("authored-library.kerml", LIB)
            .diagnostics
            .is_empty()
    );
    let unit = model.add_source("authored-dependencies.kerml", source);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}
fn id(r: &mut ResolvedModel, name: &str) -> usize {
    r.resolve_qualified(name).unwrap().0
}

#[test]
fn authored_ancestor_roles_keep_checked_and_published_targets_in_order() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for early in [false, true] {
            for (declaration, role, consumer_role) in [
                ("class", "end feature", "end feature"),
                ("behavior", "in", "in"),
                ("function", "return", "return"),
            ] {
                let foreign = format!(
                    "{declaration} Original {{{role} seed;}} {declaration} Middle specializes Original {{{role} middle;}} {declaration} Foreign specializes Middle {{{role} selected redefines Middle::middle;}}"
                );
                let consumer = format!(
                    "{declaration} Provider {{public import Foreign::selected;}} {declaration} Bridge specializes Provider; {declaration} Child specializes Bridge {{{consumer_role} replacement;}}"
                );
                let source = if early {
                    format!("{foreign} {consumer}")
                } else {
                    format!("{consumer} {foreign}")
                };
                let mut r = fixture(&source, format);
                let child = id(&mut r, "Child");
                let selected = id(&mut r, "Foreign::selected");
                let middle = id(&mut r, "Middle::middle");
                let seed = id(&mut r, "Original::seed");
                let replacement = id(&mut r, "Child::replacement");
                let proof =
                    r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0);
                if format == GraphFormat::LegacyV2 {
                    assert!(proof.is_err());
                    continue;
                }
                let proof = proof.unwrap_or_else(|e| panic!("{declaration} early={early}: {e:?}"));
                assert_eq!(proof.required_positional.get(&middle), Some(&vec![seed]));
                // The authored ancestor edge supplies the requirement; no duplicate implied edge.
                assert!(!proof.required_positional.contains_key(&selected));
                // A parameter, like an end or a result, pairs with the slot
                // the import became after an inheritance step.
                assert_eq!(
                    proof.required_positional.get(&replacement),
                    Some(&vec![selected])
                );
                assert!(proof.inherited.is_empty());
                let plan = r.b.positional_redefinitions.as_ref().unwrap();
                assert!(!plan.targets.contains_key(&selected));
                assert_eq!(plan.targets.get(&middle), Some(&vec![seed]));
            }
        }
    }
}

#[test]
fn authored_role_cycles_same_owner_and_external_role_targets_stay_qualified() {
    for foreign in [
        "class Foreign {end feature selected redefines Foreign::another; end feature another;}",
        "class Other {end feature otherEnd;} class Foreign {end feature selected redefines Other::otherEnd;}",
        "class Original {end feature seed redefines Foreign::selected;} class Foreign specializes Original {end feature selected redefines Original::seed;}",
        // A future generated selected -> seed edge would close this cycle.
        // The non-end relay is structural input, not a conformant end redefinition.
        "class Root {feature relay redefines Foreign::selected;} class Original specializes Root {end feature seed redefines Root::relay;} class Foreign specializes Original {end feature selected;}",
        // A role-free authored cycle reaching a role is only structural input,
        // not a model satisfying Redefinition end conformance.
        "class Original {end feature seed;} class Foreign specializes Original {end feature selected;} class Relay {feature a redefines Relay::b,Foreign::selected; feature b redefines Relay::a;}",
    ] {
        let imported = if foreign.contains("class Relay") {
            "Relay::a"
        } else {
            "Foreign::selected"
        };
        let mut r = fixture(
            &format!(
                "{foreign} class Provider {{public import {imported};}} class Child specializes Provider {{end feature replacement;}}"
            ),
            GraphFormat::CanonicalV3,
        );
        let child = id(&mut r, "Child");
        let provider = id(&mut r, "Provider");
        for excluded in [vec![], vec![provider]] {
            assert!(
                r.b.checked_type_membership_operation(child, &[], &excluded, true, &mut 0)
                    .is_err(),
                "{foreign}"
            );
        }
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(
            r.b.positional_redefinitions
                .as_ref()
                .unwrap()
                .incomplete
                .contains(&child),
            "{foreign}"
        );
    }
}

#[test]
fn authored_prerequisite_budget_endpoint_and_carrier_damage_recover() {
    let mut r = fixture(
        "class Original {end feature seed;} class Foreign specializes Original {end feature selected redefines Original::seed;} class Other {end feature unrelated;} class Provider {public import Foreign::selected;} class Bridge specializes Provider; class Child specializes Bridge {end feature replacement;}",
        GraphFormat::CanonicalV3,
    );
    let child = id(&mut r, "Child");
    let selected = id(&mut r, "Foreign::selected");
    let replacement = id(&mut r, "Child::replacement");
    let unrelated = id(&mut r, "Other::unrelated");
    let mut exhausted = crate::eval::MAX_STEPS;
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut exhausted)
            .is_err()
    );
    let healthy =
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .unwrap();
    assert_eq!(
        healthy.required_positional.get(&replacement),
        Some(&vec![selected])
    );
    let relationship = *r.b.elements[selected]
        .owned_relationships
        .iter()
        .find(|&&e| r.b.elements[e].ty == "Redefinition")
        .unwrap();
    let original = r.b.elements[relationship].props.clone();
    let wrong = r.b.elements[unrelated].id.to_string();
    // Change the same relationship's endpoint, preserving its identity and the
    // old bootstrap target. Neither retained publication nor local domain memo
    // may turn this mismatch into complete source evidence.
    for key in ["general", "subsettedFeature", "redefinedFeature"] {
        if original.get(key).is_some() {
            r.b.set(relationship, key, serde_json::json!({"@id":wrong}));
        }
    }
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_err()
    );
    r.b.elements[relationship].props = original;
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    let owned = r.b.elements[selected].owned_relationships.clone();
    r.b.elements[selected]
        .owned_relationships
        .make_mut()
        .retain(|&e| e != relationship);
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_err()
    );
    r.b.elements[selected].owned_relationships = owned;
    let recovered =
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .unwrap();
    assert_eq!(recovered.required_positional, healthy.required_positional);
}
