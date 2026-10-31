//! A target transition's source (`if g then b;`, `else c;` after a
//! `decide`, a state body's `accept T then s2;` / `if g then s3;`): the last
//! action before it in its owner's body that can stand as a predecessor, or
//! the written source of the last transition before it. The model carries
//! it as an implied Membership of the transition, after its written
//! relationships, so `source`, `sourceFeature()` and the transition
//! succession's source end agree, and the full form writes no
//! self-reference. A plain `then` after a guarded transition leaves the
//! same predecessor, past the transition; parameters and connectors other
//! than flows and messages stand as no predecessor (public mirror issue #13).

#![cfg(feature = "json")]

use serde_json::Value;
use sysmlv2_parser::{
    full::model_to_full_json,
    json::{ClosurePolicy, Derived, DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

const SOURCE_FEATURE: &str = "Systems-States-TransitionUsage-sourceFeature_";
const SUPERTYPES: &str = "Core-Types-Type-supertypes_Boolean";

/// The reporter's reproduction, its related case (`then c;` after the
/// guarded branch) and the state shorthand forms.
const SOURCE: &str = "package Repro {
    action def Basic {
        attribute x = 1;
        action a;
        action b;
        action c;
        first a then d;
        decide d;
            if x > 0 then b;
            else c;
    }
    action def Related {
        attribute g = true;
        action b; action c; action e;
        decide d;
            if g then b;
            then c;
            else e;
    }
    state def SM {
        state s1; state s2; state s3;
        accept T then s2;
        if g then s3;
        attribute g = true;
    }
    item def T;
    action def Skipped {
        action a;
        in item p;
        then b;
        action b;
        action c;
        connect b to c;
        then e;
        action e;
        decide d;
        in item q;
        if true then a;
        else b;
    }
}";

fn model_with_library() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("repro.sysml", SOURCE);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}

fn model_without_library() -> ResolvedModel {
    let mut model = Model::new();
    let unit = model.add_source("repro.sysml", SOURCE);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

fn named(r: &mut ResolvedModel, path: &str) -> ElementRef {
    r.resolve_qualified(path)
        .unwrap_or_else(|| panic!("no {path}"))
}

fn qualified(r: &mut ResolvedModel, e: ElementRef) -> String {
    r.element_qualified_name(e)
        .unwrap_or_else(|| format!("<{}>", r.element_type(e)))
}

fn owned(r: &mut ResolvedModel, kind: &str, owner: ElementRef) -> Vec<ElementRef> {
    r.elements_of_metaclass(kind)
        .into_iter()
        .filter(|&e| r.owner(e) == Some(owner))
        .collect()
}

/// The transitions of `owner` in declaration order, with their targets.
fn transitions(r: &mut ResolvedModel, owner: ElementRef) -> Vec<(ElementRef, String)> {
    owned(r, "TransitionUsage", owner)
        .into_iter()
        .map(|t| {
            let target = r.transition_parts(t).target.expect("a target");
            (t, qualified(r, target))
        })
        .collect()
}

/// A derived single reference, as a qualified name.
fn reference(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Option<String> {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::Reference(Reference::Element(t))) => Some(qualified(r, t)),
        Derived::Value(DerivedValue::Null) => None,
        other => panic!("{name}: {other:?}"),
    }
}

/// A derived reference list, as qualified names.
fn references(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Vec<String> {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::References(list)) => list
            .into_iter()
            .map(|reference| match reference {
                Reference::Element(t) => qualified(r, t),
                other => panic!("{name}: {other:?}"),
            })
            .collect(),
        other => panic!("{name}: {other:?}"),
    }
}

/// The transition's succession and the plain successions of a body.
fn successions(r: &mut ResolvedModel, owner: ElementRef) -> Vec<ElementRef> {
    owned(r, "SuccessionAsUsage", owner)
}

/// The implied memberships of `e`: (metaclass, member).
fn implied_memberships(r: &mut ResolvedModel, e: ElementRef) -> Vec<(String, String)> {
    let mut out = Vec::new();
    for edge in r.implied_relationships(e) {
        if r.element_type(edge) != "Membership" {
            continue;
        }
        let (_, targets) = r.relationship_ends(edge);
        for target in targets {
            match target {
                Reference::Element(t) => out.push(("Membership".to_string(), qualified(r, t))),
                other => panic!("{other:?}"),
            }
        }
    }
    out
}

fn direct_bases(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    let what = qualified(r, e);
    r.property(e, "feature")
        .unwrap_or_else(|err| panic!("{what}.feature: {err}"));
    match r
        .invoke_operation(e, SUPERTYPES, &[DerivedValue::Bool(false)])
        .unwrap_or_else(|err| panic!("{what} supertypes: {err}"))
        .value
    {
        DerivedValue::References(list) => list
            .into_iter()
            .map(|reference| match reference {
                Reference::Element(t) => qualified(r, t),
                other => panic!("{other:?}"),
            })
            .collect(),
        other => panic!("{other:?}"),
    }
}

/// Every reader of a target transition's source agrees: `source`, the
/// `sourceFeature()` body, `transition_parts`, the implied Membership and
/// the transition succession's source end, all the decision node.
#[test]
fn decision_branches_leave_the_decision_node_through_an_implied_membership() {
    let mut r = model_with_library();
    let basic = named(&mut r, "Repro::Basic");
    let branches = transitions(&mut r, basic);
    assert_eq!(
        branches.iter().map(|(_, t)| t.as_str()).collect::<Vec<_>>(),
        ["Repro::Basic::b", "Repro::Basic::c"]
    );
    for (transition, target) in branches {
        assert_eq!(
            reference(&mut r, transition, "source").as_deref(),
            Some("Repro::Basic::d"),
            "{target}"
        );
        let d = named(&mut r, "Repro::Basic::d");
        assert_eq!(r.transition_parts(transition).source, Some(d));
        assert_eq!(r.implicit_transition_source(transition), Some(d));
        let what = qualified(&mut r, transition);
        let source_feature = r
            .invoke_operation(transition, SOURCE_FEATURE, &[])
            .unwrap_or_else(|e| panic!("{what} sourceFeature: {e}"))
            .value;
        assert_eq!(
            source_feature,
            DerivedValue::Reference(Reference::Element(d)),
            "{target}"
        );
        // One implied Membership, the source its member (its place after
        // every written relationship is pinned on the full form below: the
        // ids of unnamed members are positional).
        assert_eq!(
            implied_memberships(&mut r, transition),
            [("Membership".to_string(), "Repro::Basic::d".to_string())],
            "{target}"
        );
        // The transition succession leaves the same source.
        let succession = successions(&mut r, transition);
        assert_eq!(succession.len(), 1, "{target}");
        assert_eq!(
            reference(&mut r, succession[0], "sourceFeature").as_deref(),
            Some("Repro::Basic::d"),
            "{target}"
        );
        assert_eq!(
            references(&mut r, succession[0], "targetFeature"),
            std::slice::from_ref(&target),
            "{target}"
        );
        // The transition is a decision transition of its action.
        assert_eq!(
            direct_bases(&mut r, transition),
            ["Actions::Action::decisionTransitions"],
            "{target}"
        );
    }
}

/// Without a library the source still answers — no row, no self-reference.
#[test]
fn the_source_answers_without_a_library() {
    let mut r = model_without_library();
    let basic = named(&mut r, "Repro::Basic");
    for (transition, target) in transitions(&mut r, basic) {
        assert_eq!(
            reference(&mut r, transition, "source").as_deref(),
            Some("Repro::Basic::d"),
            "{target}"
        );
        let succession = successions(&mut r, transition);
        assert_eq!(
            reference(&mut r, succession[0], "sourceFeature").as_deref(),
            Some("Repro::Basic::d"),
            "{target}"
        );
    }
}

/// The full form: `source` is the decision node on both branches, never
/// the transition's own id; the implied Membership is listed under the
/// transition after its written relationships and references the decision
/// node; each succession's `sourceFeature` is the decision node.
#[test]
fn the_full_form_writes_the_source_and_the_implied_membership() {
    for with_library in [false, true] {
        let mut model = Model::new();
        if with_library {
            model
                .load_library_dir(&sysmlv2_testkit::library_dir())
                .unwrap();
        }
        model.add_source("repro.sysml", SOURCE);
        let full = model_to_full_json(&model);
        let elements = full.as_array().unwrap();
        let by_id: std::collections::HashMap<&str, &Value> = elements
            .iter()
            .map(|e| (e["@id"].as_str().unwrap(), e))
            .collect();
        let name = |v: &Value| -> String {
            let id = v["@id"].as_str().unwrap();
            by_id[id]["qualifiedName"]
                .as_str()
                .map(str::to_string)
                .unwrap_or_else(|| by_id[id]["@type"].as_str().unwrap().to_string())
        };
        let basic = elements
            .iter()
            .find(|e| e["qualifiedName"] == "Repro::Basic")
            .expect("Repro::Basic");
        let basic_transitions: Vec<&Value> = elements
            .iter()
            .filter(|e| e["@type"] == "TransitionUsage" && e["owner"]["@id"] == basic["@id"])
            .collect();
        assert_eq!(basic_transitions.len(), 2, "library {with_library}");
        for transition in basic_transitions {
            let id = transition["@id"].as_str().unwrap();
            assert_ne!(transition["source"]["@id"], id, "self-reference");
            assert_eq!(name(&transition["source"]), "Repro::Basic::d");
            let relationships = transition["ownedRelationship"].as_array().unwrap();
            let memberships: Vec<&Value> = relationships
                .iter()
                .map(|r| by_id[r["@id"].as_str().unwrap()])
                .filter(|r| r["@type"] == "Membership")
                .collect();
            assert_eq!(memberships.len(), 1, "library {with_library}");
            let membership = memberships[0];
            assert_eq!(membership["isImplied"], true);
            assert_eq!(name(&membership["memberElement"]), "Repro::Basic::d");
            assert_eq!(membership["membershipOwningNamespace"]["@id"], id);
            assert_eq!(membership["owningRelatedElement"]["@id"], id);
            assert_eq!(membership["memberName"], "d");
            assert_eq!(membership["visibility"], "public");
            let position = relationships
                .iter()
                .position(|r| r["@id"] == membership["@id"])
                .unwrap();
            assert!(
                relationships[..position]
                    .iter()
                    .all(|r| by_id[r["@id"].as_str().unwrap()]["isImplied"] != true
                        || by_id[r["@id"].as_str().unwrap()]["@type"] != "Membership"),
                "the implied membership follows the written relationships"
            );
            assert!(
                relationships[..position]
                    .iter()
                    .filter(|r| by_id[r["@id"].as_str().unwrap()]["isImplied"] != true)
                    .count()
                    >= 2,
                "the written relationships come first"
            );
            let succession = relationships
                .iter()
                .map(|r| by_id[r["@id"].as_str().unwrap()])
                .filter(|r| r["@type"] == "OwningMembership")
                .find_map(|r| {
                    let member = by_id[r["memberElement"]["@id"].as_str().unwrap()];
                    (member["@type"] == "SuccessionAsUsage").then_some(member)
                })
                .expect("the transition succession");
            assert_eq!(name(&succession["sourceFeature"]), "Repro::Basic::d");
        }
    }
}

/// A `then` after a guarded branch leaves the decision node, not the
/// transition before it; the branches leave it too.
#[test]
fn a_then_after_a_guarded_branch_leaves_the_decision_node() {
    let mut r = model_with_library();
    let related = named(&mut r, "Repro::Related");
    let plain = successions(&mut r, related);
    assert_eq!(plain.len(), 1);
    assert_eq!(
        reference(&mut r, plain[0], "sourceFeature").as_deref(),
        Some("Repro::Related::d")
    );
    assert_eq!(
        references(&mut r, plain[0], "targetFeature"),
        ["Repro::Related::c"]
    );
    for (transition, target) in transitions(&mut r, related) {
        assert_eq!(
            reference(&mut r, transition, "source").as_deref(),
            Some("Repro::Related::d"),
            "{target}"
        );
    }
}

/// A state body's shorthand transitions (`accept T then s2;`, `if g then
/// s3;`) leave the last state before them, and are its `stateTransitions`.
#[test]
fn state_shorthand_transitions_leave_the_last_state() {
    let mut r = model_with_library();
    let sm = named(&mut r, "Repro::SM");
    let shorthand = transitions(&mut r, sm);
    assert_eq!(
        shorthand
            .iter()
            .map(|(_, t)| t.as_str())
            .collect::<Vec<_>>(),
        ["Repro::SM::s2", "Repro::SM::s3"]
    );
    for (transition, target) in shorthand {
        assert_eq!(
            reference(&mut r, transition, "source").as_deref(),
            Some("Repro::SM::s3"),
            "{target}"
        );
        assert_eq!(
            implied_memberships(&mut r, transition),
            [("Membership".to_string(), "Repro::SM::s3".to_string())],
            "{target}"
        );
        let succession = successions(&mut r, transition);
        assert_eq!(
            reference(&mut r, succession[0], "sourceFeature").as_deref(),
            Some("Repro::SM::s3"),
            "{target}"
        );
        assert_eq!(
            direct_bases(&mut r, transition),
            ["States::StateAction::stateTransitions"],
            "{target}"
        );
    }
}

/// Parameters and connectors other than flows and messages stand as no
/// predecessor: a `then` after an `in` parameter leaves the action before
/// it; one after a connection leaves the action before the connection; a
/// target transition after a parameter leaves the decision node before it.
#[test]
fn parameters_and_connectors_are_no_predecessors() {
    let mut r = model_with_library();
    let skipped = named(&mut r, "Repro::Skipped");
    let plain = successions(&mut r, skipped);
    let mut sources: Vec<(String, Option<String>)> = plain
        .iter()
        .map(|&s| {
            let target = references(&mut r, s, "targetFeature");
            (target[0].clone(), reference(&mut r, s, "sourceFeature"))
        })
        .collect();
    sources.sort();
    assert_eq!(
        sources,
        [
            (
                "Repro::Skipped::b".to_string(),
                Some("Repro::Skipped::a".to_string())
            ),
            (
                "Repro::Skipped::e".to_string(),
                Some("Repro::Skipped::c".to_string())
            ),
        ]
    );
    for (transition, target) in transitions(&mut r, skipped) {
        assert_eq!(
            reference(&mut r, transition, "source").as_deref(),
            Some("Repro::Skipped::d"),
            "{target}"
        );
        assert_eq!(
            direct_bases(&mut r, transition),
            ["Actions::Action::decisionTransitions"],
            "{target}"
        );
    }
}
