//! A bare `then t;` in a state body (SysML.xtext `TargetTransitionUsage`):
//! after a behavior usage or a transition it is a transition whose source
//! is the last action before it, a state's `stateTransitions` (or an
//! action's `decisionTransitions`); after an entry action, after a
//! structure usage, with a multiplicity, or in an action body it is the
//! succession it is everywhere else.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

const SOURCE: &str = "package Tt {
    attribute def Sig;
    state def T {
        entry; then s1;
        state s1; then s2;
        state s2; then s1; then s2;
        part p; then s2;
        action a; then s1;
        accept sig : Sig then s2;
    }
    action def A { action a; then b; action b; }
    state def U { state s1; then [1] s2; state s2; }
}";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("thens.sysml", SOURCE);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}

fn named(r: &mut ResolvedModel, path: &str) -> ElementRef {
    r.resolve_qualified(path)
        .unwrap_or_else(|| panic!("no {path}"))
}

fn owned(r: &mut ResolvedModel, kind: &str, owner: ElementRef) -> Vec<ElementRef> {
    r.elements_of_metaclass(kind)
        .into_iter()
        .filter(|&e| r.owner(e) == Some(owner))
        .collect()
}

/// The complete direct bases, the member lists answering first.
fn direct(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    r.property(e, "feature")
        .unwrap_or_else(|err| panic!("{e:?}.feature: {err}"));
    match r
        .invoke_operation(
            e,
            "Core-Types-Type-supertypes_Boolean",
            &[DerivedValue::Bool(false)],
        )
        .unwrap_or_else(|err| panic!("supertypes: {err}"))
        .value
    {
        DerivedValue::References(list) => list
            .into_iter()
            .map(|reference| match reference {
                Reference::Element(e) => r.element_qualified_name(e).unwrap_or_default(),
                other => panic!("{other:?}"),
            })
            .collect(),
        other => panic!("{other:?}"),
    }
}

#[test]
fn bare_thens_after_states_and_actions_are_transitions() {
    let mut r = model();
    let t = named(&mut r, "Tt::T");
    let (s1, s2, a) = (
        named(&mut r, "Tt::T::s1"),
        named(&mut r, "Tt::T::s2"),
        named(&mut r, "Tt::T::a"),
    );
    // `then s2` after `state s1`, `then s1; then s2` after `state s2`,
    // `then s1` after `action a`, and the triggered target transition.
    let transitions = owned(&mut r, "TransitionUsage", t);
    assert_eq!(transitions.len(), 5);
    let sources: Vec<Option<ElementRef>> = transitions
        .iter()
        .map(|&e| r.transition_parts(e).source)
        .collect();
    assert_eq!(sources, [Some(s1), Some(s2), Some(s2), Some(a), Some(a)]);
    for &e in &transitions[..3] {
        assert_eq!(direct(&mut r, e), ["States::StateAction::stateTransitions"]);
    }
    for &e in &transitions[3..] {
        assert_eq!(direct(&mut r, e), ["Actions::Action::decisionTransitions"]);
    }
    // `then s1` after `entry;` and `then s2` after `part p;` are
    // successions, as the grammar has them.
    let successions = owned(&mut r, "SuccessionAsUsage", t);
    assert_eq!(successions.len(), 2);
    // An action body's `then b;` and a `then [1] s2;` are successions.
    let a_def = named(&mut r, "Tt::A");
    assert_eq!(owned(&mut r, "TransitionUsage", a_def).len(), 0);
    assert_eq!(owned(&mut r, "SuccessionAsUsage", a_def).len(), 1);
    let u = named(&mut r, "Tt::U");
    assert_eq!(owned(&mut r, "TransitionUsage", u).len(), 0);
    assert_eq!(owned(&mut r, "SuccessionAsUsage", u).len(), 1);
}
