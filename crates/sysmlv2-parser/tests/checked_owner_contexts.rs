//! The checked member lists (`feature`, `inheritedMembership`,
//! `featureMembership`, `member`, `membership`, `importedMembership`) on
//! the behaviour, requirement, case, connector, flow and metadata owner
//! contexts, their parameters, ends, subjects, actors, subactions and
//! constraints, over the standard library: every definition and feature
//! kind is a receiver; what still refuses does so for a named reason.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, ElementRef, ResolvedModel},
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

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "ctx.sysml",
        "package Ctx {
            port def P { in attribute a : ScalarValues::Real; out attribute b : ScalarValues::Real; }
            part def Wheel { attribute radius : ScalarValues::Real; }
            action def Act2;
            action def Act { in item x : ScalarValues::Real; out item y : ScalarValues::Real; action step1 : Act2; }
            calc def Area { in attribute w : ScalarValues::Real; in attribute h : ScalarValues::Real; return attribute area : ScalarValues::Real = w * h; }
            constraint def Con { in attribute v : ScalarValues::Real; }
            requirement def Req { subject s : Sys; attribute limit : ScalarValues::Real; require constraint { limit > 0.0 } }
            connection def Mount { end part wheel : Wheel[1]; end part hub : Sys; }
            interface def Pipe { end port p1 : P; end port p2 : ~P; }
            allocation def Alloc { end part logical : Sys; end part physical : Wheel; }
            flow def Transfer;
            case def C { subject s : Sys; objective obj { } actor user : Wheel; }
            use case def UC { subject s : Sys; actor user : Wheel; }
            state def St { entry action init : Act2; state s1; }
            metadata def Tag { attribute level : ScalarValues::Integer; }
            part def Sys {
                part w : Wheel;
                part w2 : Wheel;
                port p : P;
                action act : Act;
                requirement req : Req;
                constraint con : Con;
                calc area : Area;
                state st : St;
                perform action go : Act2;
                exhibit state run : St;
                satisfy requirement req2 : Req by w;
                connection m : Mount connect w to w2;
                interface pipe : Pipe connect p to p;
                allocation al : Alloc allocate w to w2;
                flow of ScalarValues::Real from p.b to p.a;
                event occurrence e;
                item i;
                attribute mass : ScalarValues::Real = 1.0;
            }
            part def Tagged { @Tag { level = 1; } }
            part sys : Sys;
        }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}

fn names(r: &mut ResolvedModel, e: ElementRef, property: &str) -> Vec<String> {
    let value = r
        .property(e, property)
        .unwrap_or_else(|err| panic!("{property}: {err}"));
    value
        .as_array()
        .unwrap_or_else(|| panic!("{value}"))
        .iter()
        .map(|v| {
            let e = r.element_by_id(v["@id"].as_str().unwrap()).unwrap();
            r.element_qualified_name(e).unwrap_or_default()
        })
        .collect()
}

fn answers(r: &mut ResolvedModel, path: &str) {
    let e = r.resolve_qualified(path).unwrap();
    answers_element(r, e, path);
}

fn answers_element(r: &mut ResolvedModel, e: ElementRef, what: &str) {
    for property in LISTS {
        r.property(e, property)
            .unwrap_or_else(|err| panic!("{what}.{property}: {err}"));
    }
}

#[test]
fn every_definition_kind_answers_the_member_lists() {
    let mut r = model();
    for path in [
        "Ctx::P",
        "Ctx::Act",
        "Ctx::Area",
        "Ctx::Con",
        "Ctx::Req",
        "Ctx::Mount",
        "Ctx::Pipe",
        "Ctx::Alloc",
        "Ctx::Transfer",
        "Ctx::C",
        "Ctx::UC",
        "Ctx::St",
        "Ctx::Tag",
        "Ctx::Sys",
    ] {
        answers(&mut r, path);
    }
    // Own members first, in declaration order, then the library's; a
    // requirement's constraint and a state's subactions are among them.
    let req = r.resolve_qualified("Ctx::Req").unwrap();
    let features = names(&mut r, req, "feature");
    assert_eq!(&features[..2], ["Ctx::Req::s", "Ctx::Req::limit"]);
    assert_eq!(
        features[2], "",
        "the require constraint is anonymous: {features:?}"
    );
    // The requirement's own subject hides the library's `subj`.
    assert!(
        features
            .iter()
            .any(|n| n == "Requirements::RequirementCheck::actors")
    );
    assert!(
        !features
            .iter()
            .any(|n| n == "Requirements::RequirementCheck::subj")
    );
    let st = r.resolve_qualified("Ctx::St").unwrap();
    let features = names(&mut r, st, "feature");
    assert_eq!(&features[..2], ["Ctx::St::init", "Ctx::St::s1"]);
    // The state's entry action redefines the library's `entryAction`,
    // which it hides; the `doAction` and `exitAction` it does not write
    // stay in view.
    assert!(
        !features
            .iter()
            .any(|n| n == "States::StateAction::entryAction")
    );
    assert!(
        features
            .iter()
            .any(|n| n == "States::StateAction::doAction")
    );
    let transfer = r.resolve_qualified("Ctx::Transfer").unwrap();
    let features = names(&mut r, transfer, "feature");
    assert_eq!(features[0], "Flows::MessageAction::payload");
}

#[test]
fn every_usage_kind_answers_the_member_lists() {
    let mut r = model();
    for path in [
        "Ctx::Sys::w",
        "Ctx::Sys::p",
        "Ctx::Sys::act",
        "Ctx::Sys::req",
        "Ctx::Sys::con",
        "Ctx::Sys::area",
        "Ctx::Sys::st",
        "Ctx::Sys::go",
        "Ctx::Sys::run",
        "Ctx::Sys::req2",
        "Ctx::Sys::e",
        "Ctx::Sys::i",
        "Ctx::Sys::mass",
        "Ctx::sys",
    ] {
        answers(&mut r, path);
    }
    // A usage inherits its definition's features first.
    let act = r.resolve_qualified("Ctx::Sys::act").unwrap();
    let features = names(&mut r, act, "feature");
    assert_eq!(
        &features[..3],
        ["Ctx::Act::x", "Ctx::Act::y", "Ctx::Act::step1"]
    );
    // A satisfy usage's own subject stands before the requirement's members.
    let satisfy = r.resolve_qualified("Ctx::Sys::req2").unwrap();
    let features = names(&mut r, satisfy, "feature");
    assert_eq!(features[0], "Ctx::Sys::req2::s");
    assert!(
        features.iter().any(|n| n == "Ctx::Req::limit"),
        "{features:?}"
    );
    // A flow's payload and ends are its own features.
    let sys = r.resolve_qualified("Ctx::Sys").unwrap();
    let flow = r
        .elements_of_metaclass("FlowUsage")
        .into_iter()
        .find(|&e| r.owner(e) == Some(sys))
        .expect("the flow");
    let features = names(&mut r, flow, "feature");
    assert_eq!(
        &features[..3],
        ["", "", ""],
        "payload and two ends: {features:?}"
    );
    assert!(features.iter().any(|n| n == "Flows::Message::payload"));
}

#[test]
fn connector_usages_and_their_ends_answer_the_member_lists() {
    let mut r = model();
    for path in [
        "Ctx::Sys::m",
        "Ctx::Sys::m::wheel",
        "Ctx::Sys::m::hub",
        "Ctx::Sys::pipe",
        "Ctx::Sys::pipe::p1",
        "Ctx::Sys::al",
        "Ctx::Sys::al::logical",
    ] {
        answers(&mut r, path);
    }
    let m = r.resolve_qualified("Ctx::Sys::m").unwrap();
    let features = names(&mut r, m, "feature");
    assert_eq!(&features[..2], ["Ctx::Sys::m::wheel", "Ctx::Sys::m::hub"]);
}

#[test]
fn ends_parameters_subjects_actors_and_subactions_answer_the_member_lists() {
    let mut r = model();
    for path in [
        "Ctx::P::a",
        "Ctx::P::b",
        "Ctx::Act::x",
        "Ctx::Act::y",
        "Ctx::Act::step1",
        "Ctx::Area::w",
        "Ctx::Area::area",
        "Ctx::Con::v",
        "Ctx::Req::s",
        "Ctx::Req::limit",
        "Ctx::Mount::wheel",
        "Ctx::Mount::hub",
        "Ctx::Pipe::p1",
        "Ctx::Alloc::logical",
        "Ctx::C::s",
        "Ctx::C::obj",
        "Ctx::C::user",
        "Ctx::UC::user",
        "Ctx::St::init",
        "Ctx::St::s1",
        "Ctx::Tag::level",
    ] {
        answers(&mut r, path);
    }
    // An end inherits its type's features; a subject its type's; an
    // objective the library requirement's.
    let wheel = r.resolve_qualified("Ctx::Mount::wheel").unwrap();
    assert_eq!(names(&mut r, wheel, "feature")[0], "Ctx::Wheel::radius");
    let subject = r.resolve_qualified("Ctx::Req::s").unwrap();
    assert_eq!(names(&mut r, subject, "feature")[0], "Ctx::Sys::w");
    let objective = r.resolve_qualified("Ctx::C::obj").unwrap();
    let features = names(&mut r, objective, "feature");
    assert!(
        features
            .iter()
            .any(|n| n == "Requirements::RequirementCheck::subj"),
        "{features:?}"
    );
    // A parameter typed by a data type has the data value's features.
    let x = r.resolve_qualified("Ctx::Act::x").unwrap();
    let features = names(&mut r, x, "feature");
    assert!(
        features.iter().any(|n| n == "Items::Item::self"),
        "{features:?}"
    );
}

#[test]
fn the_remaining_refusals_are_named() {
    let mut r = model();
    // A type plain metadata annotates answers like any other (semantic
    // metadata keeps one out: `checked_metadata_receivers`); a
    // requirement's constraint answers, its result expression being a
    // member like any feature.
    let req = r.resolve_qualified("Ctx::Req").unwrap();
    let constraint = r
        .elements_of_metaclass("ConstraintUsage")
        .into_iter()
        .find(|&e| r.owner(e) == Some(req))
        .expect("the require constraint");
    answers_element(&mut r, constraint, "require constraint");
    let tagged = r.resolve_qualified("Ctx::Tagged").unwrap();
    answers_element(&mut r, tagged, "plain metadata owner");
    // A usage typed by a conjugated port definition answers through the
    // original's scope, its directions turned: `P`'s `in a` and `out b`
    // are `p2 : ~P`'s output and input.
    let p2 = r.resolve_qualified("Ctx::Pipe::p2").unwrap();
    answers_element(&mut r, p2, "conjugated typing");
    let a = r.resolve_qualified("Ctx::P::a").unwrap();
    let b = r.resolve_qualified("Ctx::P::b").unwrap();
    let report = r.type_feature_report(p2).projections.unwrap();
    assert_eq!(report.inputs, [b]);
    assert_eq!(report.outputs, [a]);
    // A flow's ends answer: the lowering records their nested redefinition
    // (`from p.b` redefines `b`) for the positional-source check too.
    let sys = r.resolve_qualified("Ctx::Sys").unwrap();
    let flow = r
        .elements_of_metaclass("FlowUsage")
        .into_iter()
        .find(|&e| r.owner(e) == Some(sys))
        .expect("the flow");
    answers_element(&mut r, flow, "flow");
    let ends = r.elements_of_metaclass("FlowEnd");
    assert_eq!(ends.len(), 2);
    for end in ends {
        answers_element(&mut r, end, "flow end");
    }
}
