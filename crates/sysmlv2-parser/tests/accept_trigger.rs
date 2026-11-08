//! An accept action's trigger (`accept x at t` / `after d` / `when c`) is
//! the value of its payload parameter (pilot `TriggerValuePart`: the
//! payload's FeatureValue owns the TriggerInvocationExpression, whose
//! argument sits under a ParameterMembership as a parameter Feature owning
//! a FeatureValue, like every other argument), not a second parameter of
//! the accept. So the accept's parameters are the payload and, after it,
//! the `via` receiver; `payloadArgument = argument(1)` is the trigger and
//! `receiverArgument = argument(2)` the receiver, read literally. A legacy
//! payload that owned the trigger as a parameter member beside the payload
//! still lifts (#64).

#![cfg(feature = "json")]

use serde_json::{Value, json};
use sysmlv2_parser::json::to_compact_json;
use sysmlv2_parser::json::{Derived, DerivedValue, ElementRef, Reference, ResolvedModel};
use sysmlv2_parser::lift::from_compact_json;
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::parse_source;
use sysmlv2_parser::print::print_source;

/// The issue's model, plus a triggered accept with a receiver.
const SOURCE: &str = "package Trigger {
    attribute deadline;
    attribute ready : ScalarValues::Boolean;
    item def T;
    part def Peer { port p; }
    part peer : Peer;
    action a { accept at deadline; }
    action b { accept after 5; }
    action c { accept when ready; }
    action d { accept x : T at deadline via peer.p; }
}";

fn emit(src: &str) -> Vec<Value> {
    let parse = parse_source(src);
    assert!(parse.diagnostics.is_empty(), "{:?}", parse.diagnostics);
    let Value::Array(elements) = to_compact_json(&parse.unit) else {
        panic!("expected a flat JSON array")
    };
    elements
}

fn by_id<'a>(elements: &'a [Value], id: &Value) -> &'a Value {
    let id = id["@id"].as_str().expect("an {\"@id\"} reference");
    elements
        .iter()
        .find(|e| e["@id"] == id)
        .unwrap_or_else(|| panic!("dangling @id {id}"))
}

fn owned<'a>(elements: &'a [Value], e: &Value) -> Vec<&'a Value> {
    e["ownedRelationship"]
        .as_array()
        .expect("ownedRelationship")
        .iter()
        .map(|r| by_id(elements, r))
        .collect()
}

fn member<'a>(elements: &'a [Value], rel: &Value) -> &'a Value {
    by_id(elements, &rel["ownedRelatedElement"][0])
}

/// The accept action owned by the action `action_name` of the package.
fn accept_of<'a>(elements: &'a [Value], action_name: &str) -> &'a Value {
    let action = elements
        .iter()
        .find(|e| e["@type"] == "ActionUsage" && e["declaredName"] == action_name)
        .unwrap_or_else(|| panic!("no action {action_name}"));
    owned(elements, action)
        .into_iter()
        .map(|rel| member(elements, rel))
        .find(|e| e["@type"] == "AcceptActionUsage")
        .unwrap_or_else(|| panic!("no accept in {action_name}"))
}

/// The accept's parameter memberships, in order.
fn parameters<'a>(elements: &'a [Value], accept: &Value) -> Vec<&'a Value> {
    owned(elements, accept)
        .into_iter()
        .filter(|rel| rel["@type"] == "ParameterMembership")
        .collect()
}

#[test]
fn the_trigger_is_the_payload_parameters_value() {
    let elements = emit(SOURCE);
    for (action, kind, argument_type) in [
        ("a", "at", "FeatureReferenceExpression"),
        ("b", "after", "LiteralInteger"),
        ("c", "when", "FeatureReferenceExpression"),
        ("d", "at", "FeatureReferenceExpression"),
    ] {
        let accept = accept_of(&elements, action);
        let params = parameters(&elements, accept);
        let expected = if action == "d" { 2 } else { 1 };
        assert_eq!(params.len(), expected, "{action}: parameters");
        // The payload, with the trigger as its value.
        let payload = member(&elements, params[0]);
        assert_eq!(payload["@type"], "ReferenceUsage", "{action}");
        assert_eq!(payload["direction"], "inout", "{action}");
        let values: Vec<&Value> = owned(&elements, payload)
            .into_iter()
            .filter(|rel| rel["@type"] == "FeatureValue")
            .collect();
        assert_eq!(values.len(), 1, "{action}: the payload's value");
        let trigger = member(&elements, values[0]);
        assert_eq!(trigger["@type"], "TriggerInvocationExpression", "{action}");
        assert_eq!(trigger["kind"], kind, "{action}");
        assert_eq!(
            trigger["owningRelationship"],
            json!({ "@id": values[0]["@id"] })
        );
        // Its argument: a parameter Feature owning a FeatureValue, as every
        // other argument is wrapped.
        let arguments = parameters(&elements, trigger);
        assert_eq!(arguments.len(), 1, "{action}: the trigger's argument");
        let wrapper = member(&elements, arguments[0]);
        assert_eq!(wrapper["@type"], "Feature", "{action}");
        assert_eq!(wrapper["direction"], "in", "{action}");
        let wrapped: Vec<&Value> = owned(&elements, wrapper)
            .into_iter()
            .filter(|rel| rel["@type"] == "FeatureValue")
            .collect();
        assert_eq!(wrapped.len(), 1, "{action}: the argument's value");
        assert_eq!(
            member(&elements, wrapped[0])["@type"],
            argument_type,
            "{action}"
        );
        // No TriggerInvocationExpression is a parameter member of the accept.
        assert!(
            params
                .iter()
                .all(|rel| member(&elements, rel)["@type"] != "TriggerInvocationExpression"),
            "{action}: the trigger is not a parameter"
        );
        if action == "d" {
            let receiver = member(&elements, params[1]);
            assert_eq!(receiver["direction"], "in");
            let value = owned(&elements, receiver)
                .into_iter()
                .find(|rel| rel["@type"] == "FeatureValue")
                .expect("the receiver's value");
            assert_eq!(member(&elements, value)["@type"], "FeatureChainExpression");
        }
    }
    assert_eq!(
        elements
            .iter()
            .filter(|e| e["@type"] == "TriggerInvocationExpression")
            .count(),
        4
    );
}

fn build(src: &str) -> ResolvedModel {
    let mut model = Model::new();
    model.add_source("m.sysml", src);
    assert!(!model.has_errors(), "test model must parse clean");
    ResolvedModel::build(&model)
}

fn one(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Option<ElementRef> {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::Element(x))
        | Derived::Value(DerivedValue::Reference(Reference::Element(x))) => Some(x),
        Derived::Value(DerivedValue::Null) => None,
        other => panic!("{name}: expected a single in-model reference, got {other:?}"),
    }
}

fn many(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Vec<ElementRef> {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::Elements(v)) => v,
        Derived::Value(DerivedValue::References(v)) => v
            .into_iter()
            .map(|x| match x {
                Reference::Element(x) => x,
                other => panic!("{name}: a target outside the model: {other:?}"),
            })
            .collect(),
        other => panic!("{name}: expected a reference list, got {other:?}"),
    }
}

fn accept_in(r: &mut ResolvedModel, action: &str) -> ElementRef {
    let action = r
        .resolve_qualified(action)
        .unwrap_or_else(|| panic!("no element {action}"));
    many(r, action, "ownedMember")
        .into_iter()
        .find(|&e| r.element_type(e) == "AcceptActionUsage")
        .expect("an accept")
}

#[test]
fn the_derived_reads_find_the_trigger_in_the_payload() {
    let mut r = build(SOURCE);
    for (action, kind, argument_type) in [
        ("Trigger::a", "at", "FeatureReferenceExpression"),
        ("Trigger::b", "after", "LiteralInteger"),
        ("Trigger::c", "when", "FeatureReferenceExpression"),
        ("Trigger::d", "at", "FeatureReferenceExpression"),
    ] {
        let accept = accept_in(&mut r, action);
        let with_receiver = action == "Trigger::d";
        // The parameters: the payload and, with `via`, the receiver.
        let parameters = many(&mut r, accept, "parameter");
        assert_eq!(
            parameters.len(),
            if with_receiver { 2 } else { 1 },
            "{action}"
        );
        assert_eq!(r.element_type(parameters[0]), "ReferenceUsage", "{action}");
        assert_eq!(many(&mut r, accept, "input"), parameters, "{action}");
        let payload = one(&mut r, accept, "payloadParameter").expect("payload");
        assert_eq!(payload, parameters[0], "{action}");
        // `payloadArgument = argument(1)`: the trigger, the payload's value.
        let trigger = one(&mut r, accept, "payloadArgument").expect("payload argument");
        assert_eq!(
            r.element_type(trigger),
            "TriggerInvocationExpression",
            "{action}"
        );
        assert_eq!(r.owner(trigger), Some(payload), "{action}");
        assert_eq!(
            r.property(trigger, "kind").unwrap(),
            Value::String(kind.to_owned()),
            "{action}"
        );
        // `receiverArgument = argument(2)`: the `via` expression, else none.
        let receiver = one(&mut r, accept, "receiverArgument");
        assert_eq!(receiver.is_some(), with_receiver, "{action}");
        if let Some(receiver) = receiver {
            assert_eq!(r.element_type(receiver), "FeatureChainExpression");
        }
        // The trigger's own argument, through its wrapped parameter.
        let arguments = many(&mut r, trigger, "argument");
        assert_eq!(arguments.len(), 1, "{action}");
        assert_eq!(r.element_type(arguments[0]), argument_type, "{action}");
        let wrapper = many(&mut r, trigger, "input");
        assert_eq!(wrapper.len(), 1, "{action}");
        assert_eq!(r.element_type(wrapper[0]), "Feature", "{action}");
    }
}

/// Parse, lower, lift and print; the lifted text re-lowers to the same
/// elements with the same ids.
fn round_trip(src: &str) -> String {
    let parsed = parse_source(src);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let json = to_compact_json(&parsed.unit);
    let lifted = from_compact_json(&json).expect("lift");
    assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
    let text = print_source(&lifted.unit);
    let reparsed = parse_source(&text);
    assert!(
        reparsed.diagnostics.is_empty(),
        "{text}\n{:?}",
        reparsed.diagnostics
    );
    assert_eq!(to_compact_json(&reparsed.unit), json, "{text}");
    text
}

#[test]
fn the_text_round_trips_for_each_trigger_kind() {
    // The lift spells references root-qualified (`$::Trigger::deadline`).
    let text = round_trip(SOURCE)
        .replace("$::Trigger::Peer::", "")
        .replace("$::Trigger::", "");
    for spelling in [
        "accept at deadline;",
        "accept after 5;",
        "accept when ready;",
        "accept x : T at deadline via peer.p;",
    ] {
        assert!(text.contains(spelling), "{spelling} in\n{text}");
    }
    // A payload with a written value stays one.
    let text = round_trip("package P { item def T; action a { accept x : T = 1; } }")
        .replace("$::P::", "");
    assert!(text.contains("accept x : T = 1;"), "{text}");
}

/// The legacy shape of `package P { action a { accept sig at clock; } }`:
/// the trigger a parameter member of the accept beside the payload, its
/// argument the bare expression under the trigger's ParameterMembership.
fn legacy_shape(mut elements: Vec<Value>) -> Vec<Value> {
    let accept = elements
        .iter()
        .position(|e| e["@type"] == "AcceptActionUsage")
        .expect("accept");
    let accept_id = elements[accept]["@id"].clone();
    let index = |elements: &[Value], id: &Value| {
        elements
            .iter()
            .position(|e| e["@id"] == id["@id"])
            .expect("element")
    };
    let payload_membership = index(&elements, &elements[accept]["ownedRelationship"][0]);
    let payload = index(
        &elements,
        &elements[payload_membership]["ownedRelatedElement"][0],
    );
    let value = elements[payload]["ownedRelationship"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| index(&elements, r))
        .find(|&r| elements[r]["@type"] == "FeatureValue")
        .expect("the payload's value");
    let trigger = index(&elements, &elements[value]["ownedRelatedElement"][0]);
    let trigger_id = elements[trigger]["@id"].clone();
    let argument_membership = index(&elements, &elements[trigger]["ownedRelationship"][0]);
    let wrapper = index(
        &elements,
        &elements[argument_membership]["ownedRelatedElement"][0],
    );
    let wrapper_value = index(&elements, &elements[wrapper]["ownedRelationship"][0]);
    let expression = index(
        &elements,
        &elements[wrapper_value]["ownedRelatedElement"][0],
    );
    // The trigger's parameter membership, beside the payload's.
    let membership_id = json!({ "@id": "legacy-trigger-membership" });
    elements.push(json!({
        "@id": "legacy-trigger-membership",
        "@type": "ParameterMembership",
        "isImplied": false,
        "ownedRelatedElement": [{ "@id": trigger_id }],
        "ownedRelationship": [],
        "owningRelatedElement": { "@id": accept_id },
    }));
    let accept_rels = elements[accept]["ownedRelationship"]
        .as_array_mut()
        .unwrap();
    accept_rels.insert(1, membership_id.clone());
    elements[trigger]["owningRelationship"] = membership_id;
    // The argument, bare under the trigger's parameter membership.
    let argument_membership_id = elements[argument_membership]["@id"].clone();
    elements[argument_membership]["ownedRelatedElement"] =
        json!([{ "@id": elements[expression]["@id"] }]);
    elements[expression]["owningRelationship"] = json!({ "@id": argument_membership_id });
    // The payload's value, the wrapper and its value are gone.
    let value_id = elements[value]["@id"].clone();
    elements[payload]["ownedRelationship"]
        .as_array_mut()
        .unwrap()
        .retain(|r| r["@id"] != value_id);
    let removed: Vec<Value> = [value, wrapper, wrapper_value]
        .iter()
        .map(|&i| elements[i]["@id"].clone())
        .collect();
    elements.retain(|e| !removed.contains(&e["@id"]));
    elements
}

#[test]
fn a_legacy_payload_with_the_trigger_as_a_parameter_member_still_lifts() {
    let src = "package P { action a { accept sig at clock; } }";
    let elements = emit(src);
    let legacy = legacy_shape(elements.clone());
    assert_eq!(legacy.len(), elements.len() - 2);
    let lifted = from_compact_json(&Value::Array(legacy)).expect("lift");
    assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
    let text = print_source(&lifted.unit);
    assert!(text.contains("accept sig at clock;"), "{text}");
    // Re-lowered, the legacy payload takes the current shape.
    let reparsed = parse_source(&text);
    assert!(
        reparsed.diagnostics.is_empty(),
        "{:?}",
        reparsed.diagnostics
    );
    assert_eq!(to_compact_json(&reparsed.unit), Value::Array(elements));
}

/// The compact form of `package Clean { attribute deadline; action a { accept at deadline; } action q; }`
/// as the 0.11.3 CLI wrote it: the trigger a parameter member of the
/// accept, its argument bare under the trigger's ParameterMembership.
const LEGACY_0_11_3: &str = include_str!("fixtures/accept-trigger-0.11.3.json");

#[test]
fn a_payload_written_by_the_previous_release_lifts() {
    let legacy: Value = serde_json::from_str(LEGACY_0_11_3).expect("fixture");
    let elements = legacy.as_array().expect("an element array");
    // The fixture is the legacy shape: the trigger owned by a parameter
    // membership of the accept, its argument the expression itself.
    let trigger = elements
        .iter()
        .find(|e| e["@type"] == "TriggerInvocationExpression")
        .expect("trigger");
    let membership = by_id(elements, &trigger["owningRelationship"]);
    assert_eq!(membership["@type"], "ParameterMembership");
    assert_eq!(
        by_id(elements, &membership["owningRelatedElement"])["@type"],
        "AcceptActionUsage"
    );
    assert_eq!(
        member(elements, owned(elements, trigger)[0])["@type"],
        "FeatureReferenceExpression"
    );
    let lifted = from_compact_json(&legacy).expect("lift");
    assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
    let text = print_source(&lifted.unit).replace("$::Clean::", "");
    assert!(text.contains("accept at deadline;"), "{text}");
    assert!(text.contains("action q;"), "{text}");
    // Re-lowered, it takes the current shape.
    let reparsed = parse_source(&text);
    assert!(
        reparsed.diagnostics.is_empty(),
        "{:?}",
        reparsed.diagnostics
    );
    let Value::Array(current) = to_compact_json(&reparsed.unit) else {
        panic!("expected a flat JSON array")
    };
    let accept = current
        .iter()
        .find(|e| e["@type"] == "AcceptActionUsage")
        .expect("accept");
    let payload = member(&current, parameters(&current, accept)[0]);
    assert!(payload_value_is_trigger(&current, payload));
}

fn payload_value_is_trigger(elements: &[Value], payload: &Value) -> bool {
    owned(elements, payload)
        .into_iter()
        .filter(|rel| rel["@type"] == "FeatureValue")
        .any(|rel| member(elements, rel)["@type"] == "TriggerInvocationExpression")
}
