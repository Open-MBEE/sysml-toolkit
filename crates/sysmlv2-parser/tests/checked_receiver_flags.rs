//! Variations, individuals and portions as receivers of the checked member
//! lists: a variation definition or usage has no base of its own beyond its
//! kind's (its variants specialize it); an individual definition is an
//! `Occurrences::Life`; a snapshot is an `Occurrences::Occurrence::snapshots`,
//! a time slice a `timeSlices`, and a KerML portion typed by a class in a
//! class a `portions`.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

const SYSML: &str = "package Rf {
    part def P;
    variation part def V { variant part a : P; variant part b : P; }
    part v : V;
    variation part w : P { variant part x : P; variant part y : P; }
    individual part def Car;
    individual part car : Car;
    part def Occ { snapshot part snap : Occ; timeslice part slice : Occ; }
}";

const KERML: &str = "package Rk {
    class K { portion feature p : K; composite feature c : K; }
}";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for (name, text) in [("flags.sysml", SYSML), ("flags.kerml", KERML)] {
        let unit = model.add_source(name, text);
        assert!(
            unit.diagnostics.is_empty(),
            "{name}: {:?}",
            unit.diagnostics
        );
    }
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

/// The complete direct bases, the member lists answering first.
fn direct(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    let what = r.element_qualified_name(e).unwrap_or_default();
    r.property(e, "feature")
        .unwrap_or_else(|err| panic!("{what}.feature: {err}"));
    match r
        .invoke_operation(
            e,
            "Core-Types-Type-supertypes_Boolean",
            &[DerivedValue::Bool(false)],
        )
        .unwrap_or_else(|err| panic!("{what} supertypes: {err}"))
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
fn variations_answer_with_their_kind_roles_alone() {
    let mut r = model();
    for (path, bases) in [
        ("Rf::V", vec!["Parts::Part"]),
        ("Rf::w", vec!["Rf::P", "Parts::parts"]),
        ("Rf::V::a", vec!["Rf::P", "Parts::parts", "Rf::V"]),
    ] {
        let e = named(&mut r, path);
        assert_eq!(direct(&mut r, e), bases, "{path}");
    }
    // The variation's own members are its variants; its own features none
    // of them.
    let v = named(&mut r, "Rf::V");
    let members = r.property(v, "ownedMember").unwrap();
    assert_eq!(members.as_array().map(Vec::len), Some(2), "{members}");
    let features = r.property(v, "ownedFeature").unwrap();
    assert_eq!(features.as_array().map(Vec::len), Some(0), "{features}");
}

#[test]
fn individual_definitions_are_lives() {
    let mut r = model();
    let car = named(&mut r, "Rf::Car");
    assert_eq!(direct(&mut r, car), ["Parts::Part", "Occurrences::Life"]);
    // An individual usage has its definition's and its kind's bases.
    let usage = named(&mut r, "Rf::car");
    assert_eq!(direct(&mut r, usage), ["Rf::Car", "Parts::parts"]);
}

#[test]
fn snapshots_time_slices_and_portions_take_their_roles() {
    let mut r = model();
    for (path, role) in [
        ("Rf::Occ::snap", "Occurrences::Occurrence::snapshots"),
        ("Rf::Occ::slice", "Occurrences::Occurrence::timeSlices"),
        ("Rk::K::p", "Occurrences::Occurrence::portions"),
    ] {
        let e = named(&mut r, path);
        let bases = direct(&mut r, e);
        assert!(bases.contains(&role.to_string()), "{path}: {bases:?}");
    }
    // A composite feature of a class is a suboccurrence, not a portion.
    let c = named(&mut r, "Rk::K::c");
    let bases = direct(&mut r, c);
    assert!(
        !bases.contains(&"Occurrences::Occurrence::portions".to_string()),
        "{bases:?}"
    );
}
