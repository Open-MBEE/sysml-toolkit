//! The checked member lists on the receivers the review's fifth batch
//! opened, over the standard library: features whose written bases name a
//! chain (`:> a.x`, `::> a.o`, a connector end's `a.o`, `perform a.go`),
//! the control nodes, loops and ifs whose kind roles the library nests
//! under `Action`, transitions, successions and the bodies of loops and
//! ifs, and a typing through a conjugated port definition, whose members
//! turn around. What still refuses does so for a named reason: an operator
//! expression's operands.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

const LISTS: [&str; 6] = [
    "feature",
    "inheritedMembership",
    "featureMembership",
    "member",
    "membership",
    "importedMembership",
];
const ALL_SUPERTYPES: &str = "Core-Types-Type-allSupertypes_";
const SUPERTYPES: &str = "Core-Types-Type-supertypes_Boolean";

const SOURCE: &str = "package Ch {
    port def Out { out attribute v : ScalarValues::Real; }
    part def Box {
        port o : Out;
        port i : ~Out;
        attribute x : ScalarValues::Real;
        action go;
    }
    part def Sys {
        part a : Box;
        part b : Box;
        connect a.o to b.i;
        connection c : Mount connect a.o to b.i;
        attribute z :> a.x;
        perform a.go;
        ref port rp ::> a.o;
    }
    connection def Mount { end port s : Out; end port t : ~Out; }
    attribute def Sig;
    state def S {
        entry; then s1;
        state s1;
        state s2;
        transition t first s1 accept sig : Sig then s2;
    }
    action def A {
        action a1;
        action a2;
        merge m;
        decide d;
        fork f;
        join j;
        while true { action w; }
        for i in 1..3 { action fi; }
        if true { action t1; } else { action e1; }
        loop { action u1; } until true;
    }
}";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("chain.sysml", SOURCE);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}

fn qualified(r: &mut ResolvedModel, e: ElementRef) -> String {
    r.element_qualified_name(e)
        .unwrap_or_else(|| format!("<{}>", r.element_type(e)))
}

fn ids(r: &mut ResolvedModel, value: &serde_json::Value) -> Vec<String> {
    value
        .as_array()
        .unwrap_or_else(|| panic!("{value}"))
        .iter()
        .map(|v| {
            let e = r.element_by_id(v["@id"].as_str().unwrap()).unwrap();
            qualified(r, e)
        })
        .collect()
}

/// Every member list answers; the qualified names of the features.
fn features(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    for property in LISTS {
        let what = qualified(r, e);
        r.property(e, property)
            .unwrap_or_else(|err| panic!("{what}.{property}: {err}"));
    }
    let value = r.property(e, "feature").unwrap();
    ids(r, &value)
}

fn supertypes(
    r: &mut ResolvedModel,
    e: ElementRef,
    operation: &str,
    arguments: &[DerivedValue],
) -> Vec<String> {
    let what = qualified(r, e);
    match r
        .invoke_operation(e, operation, arguments)
        .unwrap_or_else(|err| panic!("{what} {operation}: {err}"))
        .value
    {
        DerivedValue::References(list) => list
            .into_iter()
            .map(|reference| match reference {
                Reference::Element(e) => qualified(r, e),
                other => panic!("{other:?}"),
            })
            .collect(),
        other => panic!("{other:?}"),
    }
}

fn named(r: &mut ResolvedModel, path: &str) -> ElementRef {
    r.resolve_qualified(path)
        .unwrap_or_else(|| panic!("no {path}"))
}

/// The elements of `kind` whose owner is `owner`, in declaration order.
fn owned(r: &mut ResolvedModel, kind: &str, owner: ElementRef) -> Vec<ElementRef> {
    r.elements_of_metaclass(kind)
        .into_iter()
        .filter(|&e| r.owner(e) == Some(owner))
        .collect()
}

#[test]
fn features_whose_bases_name_a_chain_answer() {
    let mut r = model();
    let sys = named(&mut r, "Ch::Sys");
    // `attribute z :> a.x`: the chain's last link is the base.
    let z = named(&mut r, "Ch::Sys::z");
    features(&mut r, z);
    let supers = supertypes(&mut r, z, ALL_SUPERTYPES, &[]);
    for expected in ["Ch::Box::x", "ScalarValues::Real", "Base::dataValues"] {
        assert!(
            supers.iter().any(|n| n == expected),
            "{expected} in {supers:?}"
        );
    }
    // `ref port rp ::> a.o` inherits the port's features through the chain.
    let rp = named(&mut r, "Ch::Sys::rp");
    let listed = features(&mut r, rp);
    assert!(listed.iter().any(|n| n == "Ch::Out::v"), "{listed:?}");
    // `perform a.go` is an action with its own features.
    let go = named(&mut r, "Ch::Sys::go");
    let listed = features(&mut r, go);
    assert!(
        listed.iter().any(|n| n == "Actions::Action::subactions"),
        "{listed:?}"
    );
    // The connector ends of `connect a.o to b.i`: the first references a
    // chain and answers with the port's features.
    let connector = owned(&mut r, "ConnectionUsage", sys)
        .into_iter()
        .find(|&e| r.element_qualified_name(e).is_none())
        .expect("the unnamed connection");
    let ends = owned(&mut r, "ReferenceUsage", connector);
    assert_eq!(ends.len(), 2);
    let listed = features(&mut r, ends[0]);
    assert!(listed.iter().any(|n| n == "Ch::Out::v"), "{listed:?}");
    // The typed connection's ends answer the same way.
    let s = named(&mut r, "Ch::Sys::c::s");
    let listed = features(&mut r, s);
    assert!(listed.iter().any(|n| n == "Ch::Out::v"), "{listed:?}");
}

#[test]
fn a_typing_through_a_conjugated_port_definition_answers_with_directions_turned() {
    let mut r = model();
    let sys = named(&mut r, "Ch::Sys");
    let v = named(&mut r, "Ch::Out::v");
    // `port i : ~Out` inherits the port definition's features through its
    // conjugated definition, whose members are the original's turned
    // around: `out v` is an input of `i`.
    let i = named(&mut r, "Ch::Box::i");
    let listed = features(&mut r, i);
    assert!(listed.iter().any(|n| n == "Ch::Out::v"), "{listed:?}");
    let report = r.type_feature_report(i).projections.unwrap();
    assert_eq!(report.inputs, [v]);
    assert!(report.outputs.is_empty(), "{:?}", report.outputs);
    // The plain `port o : Out` keeps it an output.
    let o = named(&mut r, "Ch::Box::o");
    let report = r.type_feature_report(o).projections.unwrap();
    assert_eq!(report.outputs, [v]);
    assert!(report.inputs.is_empty(), "{:?}", report.inputs);
    // The end that references `b.i` through a chain, and the typed end
    // `t : ~Out`, see the same turned direction.
    let connector = owned(&mut r, "ConnectionUsage", sys)
        .into_iter()
        .find(|&e| r.element_qualified_name(e).is_none())
        .expect("the unnamed connection");
    let ends = owned(&mut r, "ReferenceUsage", connector);
    let listed = features(&mut r, ends[1]);
    assert!(listed.iter().any(|n| n == "Ch::Out::v"), "{listed:?}");
    assert_eq!(
        r.type_feature_report(ends[1]).projections.unwrap().inputs,
        [v]
    );
    let t = named(&mut r, "Ch::Mount::t");
    features(&mut r, t);
    assert_eq!(r.type_feature_report(t).projections.unwrap().inputs, [v]);
}

#[test]
fn control_nodes_take_the_action_roles_the_library_nests() {
    let mut r = model();
    for (node, role) in [
        ("Ch::A::m", "Actions::Action::merges"),
        ("Ch::A::d", "Actions::Action::decisions"),
        ("Ch::A::f", "Actions::Action::forks"),
        ("Ch::A::j", "Actions::Action::joins"),
    ] {
        let e = named(&mut r, node);
        assert_eq!(
            supertypes(&mut r, e, SUPERTYPES, &[DerivedValue::Bool(false)]),
            [role],
            "{node}"
        );
        let listed = features(&mut r, e);
        assert!(
            listed.iter().any(|n| n == "Actions::Action::subactions"),
            "{node}: {listed:?}"
        );
    }
}

#[test]
fn transitions_loops_and_ifs_answer() {
    let mut r = model();
    let t = named(&mut r, "Ch::S::t");
    features(&mut r, t);
    let supers = supertypes(&mut r, t, ALL_SUPERTYPES, &[]);
    assert!(
        supers.iter().any(|n| n == "Actions::transitionActions"),
        "{supers:?}"
    );
    // The state-owned transition whose source is a state takes
    // `States::StateAction::stateTransitions` from its owner.
    assert!(
        supers
            .iter()
            .any(|n| n == "States::StateAction::stateTransitions"),
        "{supers:?}"
    );
    let a = named(&mut r, "Ch::A");
    for (kind, role, count) in [
        ("WhileLoopActionUsage", "Actions::whileLoopActions", 2),
        ("ForLoopActionUsage", "Actions::forLoopActions", 1),
        ("IfActionUsage", "Actions::ifThenActions", 1),
    ] {
        let loops = owned(&mut r, kind, a);
        assert_eq!(loops.len(), count, "{kind}");
        for e in loops {
            features(&mut r, e);
            let supers = supertypes(&mut r, e, ALL_SUPERTYPES, &[]);
            assert!(supers.iter().any(|n| n == role), "{kind}: {supers:?}");
        }
    }
}

#[test]
fn loop_and_if_bodies_are_in_parameters_whose_members_answer() {
    let mut r = model();
    let a = named(&mut r, "Ch::A");
    let loops: Vec<ElementRef> = [
        "WhileLoopActionUsage",
        "ForLoopActionUsage",
        "IfActionUsage",
    ]
    .into_iter()
    .flat_map(|kind| owned(&mut r, kind, a))
    .collect();
    assert_eq!(loops.len(), 4);
    let mut bodies = 0;
    for owner in loops {
        for body in owned(&mut r, "ActionUsage", owner) {
            bodies += 1;
            // A body is an `in` parameter of its loop or if (KerML
            // `validateParameterMembershipParameterDirection`).
            assert_eq!(r.property(body, "direction").unwrap(), "in");
            let listed = features(&mut r, body);
            assert!(
                listed.iter().any(|n| n == "Actions::Action::subactions"),
                "{listed:?}"
            );
            // The action written in the body is one of its features and
            // answers its own lists.
            let nested = owned(&mut r, "ActionUsage", body);
            assert_eq!(nested.len(), 1);
            let name = r.property(nested[0], "declaredName").unwrap();
            assert!(
                ["w", "fi", "t1", "e1", "u1"].contains(&name.as_str().unwrap()),
                "{name}"
            );
            features(&mut r, nested[0]);
        }
    }
    // while, for, then, else, loop-until.
    assert_eq!(bodies, 5);
}

#[test]
fn succession_ends_and_the_library_ends_they_redefine_answer() {
    let mut r = model();
    let s = named(&mut r, "Ch::S");
    let t = named(&mut r, "Ch::S::t");
    // `entry; then s1;` and the transition's `then s2`.
    let mut successions = owned(&mut r, "SuccessionAsUsage", s);
    successions.extend(owned(&mut r, "SuccessionAsUsage", t));
    assert_eq!(successions.len(), 2);
    for succession in successions {
        features(&mut r, succession);
        let ends = owned(&mut r, "ReferenceUsage", succession);
        assert_eq!(ends.len(), 2);
        for end in ends {
            features(&mut r, end);
        }
    }
    // The library ends a succession's ends redefine cross each other's
    // chains; their closure is certified through those chains.
    for end in [
        "Occurrences::HappensBefore::earlierOccurrence",
        "Occurrences::HappensBefore::laterOccurrence",
    ] {
        let e = named(&mut r, end);
        let supers = supertypes(&mut r, e, ALL_SUPERTYPES, &[]);
        assert!(
            supers.iter().any(|n| n == "Base::things"),
            "{end}: {supers:?}"
        );
    }
    // A library step with intersections, audited against its subsettings.
    let step = named(&mut r, "Performances::Performance::subperformances");
    let listed = features(&mut r, step);
    assert!(!listed.is_empty());
}

#[test]
fn an_operator_expressions_operands_answer_through_its_callee() {
    let mut r = model();
    let a = named(&mut r, "Ch::A");
    let for_loop = owned(&mut r, "ForLoopActionUsage", a)[0];
    // The `seq` parameter answers, and so do the operands of its `1..3`
    // value: the operator's typing by its function is the planner's row,
    // and each operand redefines the function's input at its position.
    let seq = owned(&mut r, "ReferenceUsage", for_loop)
        .into_iter()
        .find(|&e| r.property(e, "declaredName").unwrap().is_null())
        .expect("the seq parameter");
    features(&mut r, seq);
    let range = r
        .elements_of_metaclass("OperatorExpression")
        .into_iter()
        .find(|&e| r.owner(e) == Some(seq))
        .expect("the range expression");
    features(&mut r, range);
    let operands = owned(&mut r, "Feature", range);
    assert_eq!(operands.len(), 2);
    for operand in operands {
        features(&mut r, operand);
    }
}

#[test]
fn body_parameters_carry_their_direction_on_the_wire_and_lift_unspelled() {
    use serde_json::Value;
    use sysmlv2_parser::{
        json::to_compact_json, lift::from_compact_json, parser::parse_source, print::print_source,
    };
    let source = "package L {
    action def A {
        while true { action w; }
        for i in 1..3 { action fi; }
        if true { action t1; } else { action e1; }
        loop { action u1; } until true;
    }
}";
    let parse = parse_source(source);
    assert!(parse.diagnostics.is_empty(), "{:?}", parse.diagnostics);
    let Value::Array(elements) = to_compact_json(&parse.unit) else {
        panic!("a flat array")
    };
    // Every body parameter is an `in` parameter of its loop or if.
    let bodies: Vec<&Value> = elements
        .iter()
        .filter(|e| {
            e["@type"] == "ActionUsage"
                && e["owningRelationship"]
                    .as_object()
                    .and_then(|r| r.get("@id"))
                    .and_then(Value::as_str)
                    .is_some_and(|id| {
                        elements
                            .iter()
                            .any(|r| r["@id"] == id && r["@type"] == "ParameterMembership")
                    })
        })
        .collect();
    assert_eq!(bodies.len(), 5, "{bodies:?}");
    for body in bodies {
        assert_eq!(body["direction"], "in", "{body}");
    }
    // The text never spells it: a body prints as its block, never as a
    // directed action.
    let lifted = from_compact_json(&Value::Array(elements)).expect("lift");
    assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
    let text = print_source(&lifted.unit);
    assert!(!text.contains("in action"), "{text}");
    assert!(!text.contains("in {"), "{text}");
    for written in [
        "while true {",
        "for i in 1 .. 3 {",
        "if true {",
        "} else {",
        "loop {",
        "} until true;",
    ] {
        assert!(text.contains(written), "{written} in {text}");
    }
}
