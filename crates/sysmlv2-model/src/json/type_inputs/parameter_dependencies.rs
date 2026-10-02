//! Imported parameters require owner scheduling: an alias invents no parameter slot, a direct import becomes one after an inheritance step.
use super::*;
use crate::model::{GraphFormat, Model};

const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
fn fixture(source: &str, format: GraphFormat) -> ResolvedModel {
    let mut model = Model::with_graph_format(format);
    assert!(
        model
            .add_library_source("parameter-library.kerml", LIB)
            .diagnostics
            .is_empty()
    );
    let unit = model.add_source("parameter-dependencies.kerml", source);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}
fn id(r: &mut ResolvedModel, name: &str) -> usize {
    r.resolve_qualified(name).unwrap().0
}

#[test]
fn foreign_parameters_suppress_and_become_slots_only_after_inheritance() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for early in [false, true] {
            let foreign = "behavior Original {in seed;} behavior Foreign specializes Original {in selected; feature unrelated;} package P {alias selectedAlias for Foreign::selected;}";
            let consumer = "behavior Provider {public import P::selectedAlias;} behavior Child specializes Provider,Original; behavior Grand specializes Child {in replacement;} behavior DirectProvider {public import Foreign::selected;} behavior DirectBridge specializes DirectProvider; behavior DirectGrand specializes DirectBridge {in replacement;}";
            let source = if early {
                format!("{foreign} {consumer}")
            } else {
                format!("{consumer} {foreign}")
            };
            let mut r = fixture(&source, format);
            let grand = id(&mut r, "Grand");
            let direct = id(&mut r, "DirectGrand");
            let selected = id(&mut r, "Foreign::selected");
            let seed = id(&mut r, "Original::seed");
            let unrelated = id(&mut r, "Foreign::unrelated");
            let replacement = id(&mut r, "Grand::replacement");
            let direct_replacement = id(&mut r, "DirectGrand::replacement");
            let result =
                r.b.checked_type_membership_operation(grand, &[], &[], true, &mut 0);
            if format == GraphFormat::LegacyV2 {
                assert!(result.is_err());
                continue;
            }
            let proof = result.unwrap();
            assert_eq!(
                proof.inherited.iter().map(|m| m.member).collect::<Vec<_>>(),
                vec![selected]
            );
            assert_eq!(proof.required_positional.get(&selected), Some(&vec![seed]));
            assert!(!proof.required_positional.contains_key(&replacement));
            let direct_proof =
                r.b.checked_type_membership_operation(direct, &[], &[], true, &mut 0)
                    .unwrap();
            // The directly imported parameter is a slot one inheritance step
            // later, which `DirectGrand`'s own parameter takes over.
            assert!(!direct_proof.inherited.iter().any(|m| m.member == selected));
            assert_eq!(
                direct_proof.required_positional.get(&direct_replacement),
                Some(&vec![selected])
            );
            let features = r
                .type_feature_report(ElementRef(direct))
                .projections
                .unwrap();
            assert!(features.features.contains(&ElementRef(direct_replacement)));
            assert!(!features.features.contains(&ElementRef(selected)));
            assert!(!features.features.contains(&ElementRef(unrelated)));
            let plan = r.b.positional_redefinitions.as_ref().unwrap();
            assert_eq!(plan.targets.get(&selected), Some(&vec![seed]));
            assert!(!plan.targets.contains_key(&replacement));
            assert_eq!(plan.targets.get(&direct_replacement), Some(&vec![selected]));
        }
    }
}

#[test]
fn foreign_returns_create_effective_results_after_inheritance() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for early in [false, true] {
            let foreign = "function Original {in seedInput; return seed;} function Foreign specializes Original {in selectedInput; return selected; feature unrelated;}";
            let consumer = "function Provider {public import Foreign::selected;} function Bridge specializes Provider; function Grand specializes Bridge {in localInput; return replacement;}";
            let source = if early {
                format!("{foreign} {consumer}")
            } else {
                format!("{consumer} {foreign}")
            };
            let mut r = fixture(&source, format);
            let grand = id(&mut r, "Grand");
            let selected = id(&mut r, "Foreign::selected");
            let seed = id(&mut r, "Original::seed");
            let replacement = id(&mut r, "Grand::replacement");
            let local = id(&mut r, "Grand::localInput");
            let result =
                r.b.checked_type_membership_operation(grand, &[], &[], true, &mut 0);
            if format == GraphFormat::LegacyV2 {
                assert!(result.is_err());
                continue;
            }
            let proof = result.unwrap();
            assert_eq!(proof.required_positional.get(&selected), Some(&vec![seed]));
            assert_eq!(
                proof.required_positional.get(&replacement),
                Some(&vec![selected])
            );
            assert!(!proof.required_positional.contains_key(&local));
            assert!(proof.inherited.is_empty());
            assert_eq!(
                r.function_result_report(ElementRef(grand)).result,
                Ok(Some(ElementRef(replacement)))
            );
        }
    }
}

#[test]
fn parameter_prerequisite_role_damage_and_budget_are_retryable() {
    let mut r = fixture(
        "behavior Original {in seed;} behavior Foreign specializes Original {in selected;} behavior Provider {public import Foreign::selected;} behavior Child specializes Provider;",
        GraphFormat::CanonicalV3,
    );
    let child = id(&mut r, "Child");
    let selected = id(&mut r, "Foreign::selected");
    let membership = r.b.elements[selected].owning_relationship.unwrap();
    let mut exhausted = crate::eval::MAX_STEPS;
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut exhausted)
            .is_err()
    );
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    r.b.elements[membership].ty = "ParameterMembership";
    r.b.elements[selected]
        .props
        .entries
        .make_mut()
        .retain(|(key, _)| key.name() != "direction");
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    for value in [
        serde_json::Value::Null,
        serde_json::json!("out"),
        serde_json::json!("bad"),
    ] {
        r.b.set(selected, "direction", value);
        assert!(
            r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
                .is_err()
        );
    }
    r.b.set(selected, "direction", serde_json::json!("in"));
    r.b.set(selected, "isEnd", serde_json::json!(true));
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_err()
    );
    r.b.set(selected, "isEnd", serde_json::json!(false));
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    r.b.elements[membership].ty = "SubjectMembership";
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_err()
    );
}

#[test]
fn return_prerequisite_direction_damage_cannot_change_role_defaults() {
    let mut r = fixture(
        "function Foreign {return selected;} function Provider {public import Foreign::selected;} function Child specializes Provider;",
        GraphFormat::CanonicalV3,
    );
    let child = id(&mut r, "Child");
    let selected = id(&mut r, "Foreign::selected");
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    for value in [
        serde_json::Value::Null,
        serde_json::json!("in"),
        serde_json::json!("inout"),
    ] {
        r.b.set(selected, "direction", value);
        assert!(
            r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
                .is_err()
        );
    }
    r.b.elements[selected]
        .props
        .entries
        .make_mut()
        .retain(|(key, _)| key.name() != "direction");
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    let carrier = r.b.elements[selected].owning_relationship.take().unwrap();
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_err()
    );
    r.b.elements[selected].owning_relationship = Some(carrier);
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
}

#[test]
fn ambiguous_results_mixed_sources_and_nested_foreign_roles_stay_qualified() {
    for foreign in [
        "function Foreign {return selected; return another;}",
        "behavior Other {in outside;} function Foreign {return selected; feature ordinary redefines Other::outside;}",
        "function Other {return outside;} function Foreign {return selected redefines Other::outside;}",
        "class Extra {end feature value;} package P {alias role for Extra::value;} function Foreign {public import P::role; return selected;}",
    ] {
        let mut r = fixture(
            &format!(
                "{foreign} function Provider {{public import Foreign::selected;}} function Child specializes Provider;"
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
    }
}

#[test]
fn inherited_result_ambiguity_does_not_invalidate_independent_parameter_evidence() {
    let mut r = fixture(
        "function First {return firstResult;} function Second {return secondResult;} function Foreign specializes First,Second {in selected;} behavior Provider {public import Foreign::selected;} behavior Child specializes Provider; function Descendant specializes Foreign {return replacement;}",
        GraphFormat::CanonicalV3,
    );
    let child = id(&mut r, "Child");
    let selected = id(&mut r, "Foreign::selected");
    let descendant = id(&mut r, "Descendant");
    let replacement = id(&mut r, "Descendant::replacement");
    let proof =
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .unwrap();
    assert_eq!(
        proof.inherited.iter().map(|m| m.member).collect::<Vec<_>>(),
        vec![selected]
    );
    assert_eq!(
        r.type_input_report(ElementRef(child)).inputs,
        Ok(vec![ElementRef(selected)])
    );
    // Imported input evidence needs no unique effective result. A descendant
    // actually pairing its own return with that ambiguous result must refuse.
    assert!(
        r.b.checked_type_membership_operation(descendant, &[], &[], true, &mut 0)
            .is_err()
    );
    assert!(
        !r.b.positional_redefinitions
            .as_ref()
            .unwrap()
            .targets
            .contains_key(&replacement)
    );
}
