//! The usage-structure operations through `invoke_operation` (SysML 8.3.9,
//! 8.3.16, 8.3.17) over the standard library: `ActionUsage::isSubactionUsage`,
//! `inputParameters`, `inputParameter` and `argument`,
//! `AcceptActionUsage::isTriggerAction`, `StateUsage::isSubstateUsage`,
//! `TransitionUsage::sourceFeature` and `triggerPayloadParameter`, and
//! `Usage::referencedFeatureTarget`; and the Kernel feature bodies
//! `Feature::isCartesianProduct`, `asCartesianProduct` and
//! `FeatureChainExpression::sourceTargetFeature`.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

const IS_SUBACTION: &str = "Systems-Actions-ActionUsage-isSubactionUsage_";
const INPUT_PARAMETERS: &str = "Systems-Actions-ActionUsage-inputParameters_";
const INPUT_PARAMETER: &str = "Systems-Actions-ActionUsage-inputParameter_Integer";
const ARGUMENT: &str = "Systems-Actions-ActionUsage-argument_Integer";
const IS_TRIGGER: &str = "Systems-Actions-AcceptActionUsage-isTriggerAction_";
const IS_SUBSTATE: &str = "Systems-States-StateUsage-isSubstateUsage_Boolean";
const SOURCE_FEATURE: &str = "Systems-States-TransitionUsage-sourceFeature_";
const TRIGGER_PAYLOAD: &str = "Systems-States-TransitionUsage-triggerPayloadParameter_";
const REFERENCED_TARGET: &str = "Systems-DefinitionAndUsage-Usage-referencedFeatureTarget_";
const IS_CARTESIAN: &str = "Core-Features-Feature-isCartesianProduct_";
const AS_CARTESIAN: &str = "Core-Features-Feature-asCartesianProduct_";
const SOURCE_TARGET: &str = "Kernel-Expressions-FeatureChainExpression-sourceTargetFeature_";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "ops.sysml",
        "package Ops {
            attribute def Sig;
            port def Out { out attribute v : ScalarValues::Real; }
            part def Box { port o : Out; action go; attribute mass : ScalarValues::Real; }
            part def Sys {
                part a : Box;
                part b : Box;
                connect a.o to b.o;
                ref port rp ::> a.o;
                perform a.go;
                part pa : Box;
                attribute m : ScalarValues::Real = a.mass;
            }
            action def Act { in x : ScalarValues::Real; out y : ScalarValues::Real; action sub; }
            action def Caller {
                action c : Act { in :>> x = 2.0; }
                accept plain : Sig;
            }
            state def Machine {
                entry; then s1;
                state s1 { entry action e1; do action d1; exit action x1; }
                state s2;
                transition t first s1 accept sig : Sig then s2;
                transition quiet first s2 then s1;
                state par parallel { state p1; }
            }
            part def Veh { action go; state st; }
        }",
    );
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

fn call(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    operation: &str,
    arguments: &[DerivedValue],
) -> DerivedValue {
    let what = qualified(r, receiver);
    r.invoke_operation(receiver, operation, arguments)
        .unwrap_or_else(|e| panic!("{what} {operation}: {e}"))
        .value
}

fn truth(
    r: &mut ResolvedModel,
    receiver: &str,
    operation: &str,
    arguments: &[DerivedValue],
) -> bool {
    let receiver = named(r, receiver);
    match call(r, receiver, operation, arguments) {
        DerivedValue::Bool(answer) => answer,
        other => panic!("{other:?}"),
    }
}

/// A single reference's qualified name, or `None` for null.
fn one(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    operation: &str,
    arguments: &[DerivedValue],
) -> Option<String> {
    match call(r, receiver, operation, arguments) {
        DerivedValue::Null => None,
        DerivedValue::Reference(Reference::Element(e)) => Some(qualified(r, e)),
        other => panic!("{other:?}"),
    }
}

fn many(r: &mut ResolvedModel, receiver: ElementRef, operation: &str) -> Vec<String> {
    match call(r, receiver, operation, &[]) {
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

fn integer(i: i64) -> DerivedValue {
    DerivedValue::Literal(i.to_string())
}

fn owned(r: &mut ResolvedModel, kind: &str, owner: ElementRef) -> Vec<ElementRef> {
    r.elements_of_metaclass(kind)
        .into_iter()
        .filter(|&e| r.owner(e) == Some(owner))
        .collect()
}

#[test]
fn subactions_and_substates_follow_their_owner_and_membership() {
    let mut r = model();
    // A composite action in an action definition or usage is a subaction;
    // an action a part owns is not.
    assert!(truth(&mut r, "Ops::Act::sub", IS_SUBACTION, &[]));
    assert!(truth(&mut r, "Ops::Caller::c", IS_SUBACTION, &[]));
    assert!(!truth(&mut r, "Ops::Veh::go", IS_SUBACTION, &[]));
    // A state's entry, do and exit actions are performed actions, which
    // the lowering writes as references (`isComposite` false): none is a
    // subaction here, the do action included, which the body would admit
    // were it composite.
    for action in ["e1", "d1", "x1"] {
        let e = named(&mut r, &format!("Ops::Machine::s1::{action}"));
        assert_eq!(r.element_type(e), "PerformActionUsage");
        assert_eq!(r.property(e, "isComposite").unwrap(), false);
        assert!(!truth(
            &mut r,
            &format!("Ops::Machine::s1::{action}"),
            IS_SUBACTION,
            &[]
        ));
    }
    // A performed action is a reference, not composite.
    assert!(!truth(&mut r, "Ops::Sys::go", IS_SUBACTION, &[]));
    // Substates: the owner's parallelism must match the question.
    assert!(truth(
        &mut r,
        "Ops::Machine::s1",
        IS_SUBSTATE,
        &[DerivedValue::Bool(false)]
    ));
    assert!(!truth(
        &mut r,
        "Ops::Machine::s1",
        IS_SUBSTATE,
        &[DerivedValue::Bool(true)]
    ));
    assert!(truth(
        &mut r,
        "Ops::Machine::par::p1",
        IS_SUBSTATE,
        &[DerivedValue::Bool(true)]
    ));
    assert!(!truth(
        &mut r,
        "Ops::Machine::par::p1",
        IS_SUBSTATE,
        &[DerivedValue::Bool(false)]
    ));
    assert!(!truth(
        &mut r,
        "Ops::Veh::st",
        IS_SUBSTATE,
        &[DerivedValue::Bool(false)]
    ));
}

#[test]
fn input_parameters_are_the_owned_inputs_and_arguments_their_values() {
    let mut r = model();
    let c = named(&mut r, "Ops::Caller::c");
    // `c : Act { in :>> x = 2.0; }` owns its redefinition of `x`; the
    // inherited `Act::x` is not its own.
    assert_eq!(many(&mut r, c, INPUT_PARAMETERS), ["Ops::Caller::c::x"]);
    assert_eq!(
        one(&mut r, c, INPUT_PARAMETER, &[integer(1)]).as_deref(),
        Some("Ops::Caller::c::x")
    );
    assert_eq!(one(&mut r, c, INPUT_PARAMETER, &[integer(2)]), None);
    assert_eq!(one(&mut r, c, INPUT_PARAMETER, &[integer(0)]), None);
    // The argument is the value expression bound to the parameter.
    let value = match call(&mut r, c, ARGUMENT, &[integer(1)]) {
        DerivedValue::Reference(Reference::Element(e)) => e,
        other => panic!("{other:?}"),
    };
    assert_eq!(r.element_type(value), "LiteralRational");
    assert_eq!(one(&mut r, c, ARGUMENT, &[integer(2)]), None);
    // An action without inputs of its own.
    let sub = named(&mut r, "Ops::Act::sub");
    assert!(many(&mut r, sub, INPUT_PARAMETERS).is_empty());
    assert_eq!(one(&mut r, sub, ARGUMENT, &[integer(1)]), None);
}

#[test]
fn transitions_know_their_source_trigger_and_payload() {
    let mut r = model();
    let t = named(&mut r, "Ops::Machine::t");
    let quiet = named(&mut r, "Ops::Machine::quiet");
    assert_eq!(
        one(&mut r, t, SOURCE_FEATURE, &[]).as_deref(),
        Some("Ops::Machine::s1")
    );
    assert_eq!(
        one(&mut r, quiet, SOURCE_FEATURE, &[]).as_deref(),
        Some("Ops::Machine::s2")
    );
    // The trigger's accept action is a trigger action; its payload
    // parameter is the transition's trigger payload parameter.
    let accept = owned(&mut r, "AcceptActionUsage", t);
    assert_eq!(accept.len(), 1);
    assert_eq!(
        call(&mut r, accept[0], IS_TRIGGER, &[]),
        DerivedValue::Bool(true)
    );
    let payload = match call(&mut r, t, TRIGGER_PAYLOAD, &[]) {
        DerivedValue::Reference(Reference::Element(e)) => e,
        other => panic!("{other:?}"),
    };
    assert_eq!(r.element_type(payload), "ReferenceUsage");
    assert_eq!(r.property(payload, "declaredName").unwrap(), "sig");
    assert_eq!(r.owner(payload), Some(accept[0]));
    assert_eq!(one(&mut r, quiet, TRIGGER_PAYLOAD, &[]), None);
    // An accept action outside a transition is no trigger action (the
    // name `plain` is its payload parameter's; the action is anonymous).
    let caller = named(&mut r, "Ops::Caller");
    let plain = owned(&mut r, "AcceptActionUsage", caller);
    assert_eq!(plain.len(), 1);
    assert_eq!(
        call(&mut r, plain[0], IS_TRIGGER, &[]),
        DerivedValue::Bool(false)
    );
}

#[test]
fn referenced_feature_targets_follow_the_reference_to_a_chains_last_link() {
    let mut r = model();
    let sys = named(&mut r, "Ops::Sys");
    let rp = named(&mut r, "Ops::Sys::rp");
    assert_eq!(
        one(&mut r, rp, REFERENCED_TARGET, &[]).as_deref(),
        Some("Ops::Box::o")
    );
    let go = named(&mut r, "Ops::Sys::go");
    assert_eq!(
        one(&mut r, go, REFERENCED_TARGET, &[]).as_deref(),
        Some("Ops::Box::go")
    );
    let connector = owned(&mut r, "ConnectionUsage", sys)
        .into_iter()
        .find(|&e| r.element_qualified_name(e).is_none())
        .expect("the connection");
    for end in owned(&mut r, "ReferenceUsage", connector) {
        assert_eq!(
            one(&mut r, end, REFERENCED_TARGET, &[]).as_deref(),
            Some("Ops::Box::o")
        );
    }
    // A usage without a reference subsetting has no target.
    let pa = named(&mut r, "Ops::Sys::pa");
    assert_eq!(one(&mut r, pa, REFERENCED_TARGET, &[]), None);
}

#[test]
fn typing_features_include_a_referenced_chain() {
    const TYPING_FEATURES: &str = "Core-Features-Feature-typingFeatures_";
    let mut r = model();
    // `perform a.go` and `ref port rp ::> a.o` subset the chains their
    // reference subsettings name: the chain feature is the first typing
    // feature, and its links are the chain as written.
    for (receiver, last) in [
        ("Ops::Sys::go", "Ops::Box::go"),
        ("Ops::Sys::rp", "Ops::Box::o"),
    ] {
        let e = named(&mut r, receiver);
        let chain = match call(&mut r, e, TYPING_FEATURES, &[]) {
            DerivedValue::References(list) => match list.first() {
                Some(Reference::Element(chain)) => *chain,
                other => panic!("{receiver}: {other:?}"),
            },
            other => panic!("{receiver}: {other:?}"),
        };
        assert_eq!(r.element_type(chain), "Feature", "{receiver}");
        let links = r.property(chain, "chainingFeature").unwrap();
        let links: Vec<String> = links
            .as_array()
            .unwrap()
            .iter()
            .map(|v| {
                let e = r.element_by_id(v["@id"].as_str().unwrap()).unwrap();
                qualified(&mut r, e)
            })
            .collect();
        assert_eq!(links, ["Ops::Sys::a", last], "{receiver}");
    }
}

#[test]
fn cartesian_products_read_the_featuring_types_and_the_type() {
    let mut r = model();
    // A part typed once and featured once is the product of the two.
    let a = named(&mut r, "Ops::Sys::a");
    assert_eq!(call(&mut r, a, IS_CARTESIAN, &[]), DerivedValue::Bool(true));
    assert_eq!(many(&mut r, a, AS_CARTESIAN), ["Ops::Sys", "Ops::Box"]);
    // A port of a part: featured by the part, typed by the port definition.
    let o = named(&mut r, "Ops::Box::o");
    assert_eq!(call(&mut r, o, IS_CARTESIAN, &[]), DerivedValue::Bool(true));
    assert_eq!(many(&mut r, o, AS_CARTESIAN), ["Ops::Box", "Ops::Out"]);
    // An untyped action's one type is the library's `Action`, through
    // the `actions` role its kind subsets: the product of its part and
    // that class.
    let go = named(&mut r, "Ops::Box::go");
    assert_eq!(
        call(&mut r, go, IS_CARTESIAN, &[]),
        DerivedValue::Bool(true)
    );
    assert_eq!(
        many(&mut r, go, AS_CARTESIAN),
        ["Ops::Box", "Actions::Action"]
    );
}

#[test]
fn a_chain_expressions_source_target_feature_is_the_source_parameters_nested_feature() {
    let mut r = model();
    // `a.mass`: the source parameter the lowering writes owns no nested
    // feature of its own, so the body answers nothing over this graph.
    let m = named(&mut r, "Ops::Sys::m");
    let chain = r
        .elements_of_metaclass("FeatureChainExpression")
        .into_iter()
        .find(|&e| r.owner(e) == Some(m))
        .expect("the chain expression");
    assert_eq!(one(&mut r, chain, SOURCE_TARGET, &[]), None);
}
