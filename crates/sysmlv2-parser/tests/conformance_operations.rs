//! The conformance operations through `invoke_operation` (KerML 8.3.3.1.10)
//! over the standard library: `specializes`, `isCompatibleWith`,
//! `supertypes(false)` and `allSupertypes` follow the implied library
//! specializations the written model never spells, beside the toolkit's
//! own `conforms` (written only) and `conforms_with_implied`.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

const SPECIALIZES: &str = "Core-Types-Type-specializes_Type";
const COMPATIBLE: &str = "Core-Types-Type-isCompatibleWith_Type";
const ALL: &str = "Core-Types-Type-allSupertypes_";
const SUPERTYPES: &str = "Core-Types-Type-supertypes_Boolean";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "conform.sysml",
        "package Conform {
            part def Engine;
            part def Diesel :> Engine;
            part motor : Diesel;
            port def Plug;
            port def Socket :> Plug;
        }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

fn names(r: &mut ResolvedModel, value: DerivedValue) -> Vec<String> {
    let DerivedValue::References(refs) = value else {
        panic!("{value:?}")
    };
    refs.into_iter()
        .map(|reference| match reference {
            Reference::Element(e) => r.element_qualified_name(e).unwrap(),
            other => panic!("{other:?}"),
        })
        .collect()
}

#[test]
fn specializes_and_compatibility_follow_the_implied_library_bases() {
    let mut r = model();
    let diesel = r.resolve_qualified("Conform::Diesel").unwrap();
    let engine = r.resolve_qualified("Conform::Engine").unwrap();
    let socket = r.resolve_qualified("Conform::Socket").unwrap();
    let truth = |r: &mut ResolvedModel, receiver: ElementRef, general: &str, expected: bool| {
        let general = r.resolve_qualified(general).unwrap();
        for operation in [SPECIALIZES, COMPATIBLE] {
            let answer = r
                .invoke_operation(receiver, operation, &[DerivedValue::Element(general)])
                .unwrap_or_else(|e| panic!("{operation}: {e}"));
            assert_eq!(answer.value, DerivedValue::Bool(expected), "{operation}");
        }
    };
    for general in [
        "Conform::Engine",
        "Conform::Diesel",
        "Parts::Part",
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ] {
        truth(&mut r, diesel, general, true);
    }
    truth(&mut r, engine, "Conform::Diesel", false);
    truth(&mut r, diesel, "Ports::Port", false);
    truth(&mut r, socket, "Ports::Port", true);
    truth(&mut r, socket, "Parts::Part", false);
    // A usage: its definition and the implied library feature.
    let motor = r.resolve_qualified("Conform::motor").unwrap();
    for (general, expected) in [
        ("Conform::Diesel", true),
        ("Parts::Part", true),
        ("Base::Anything", true),
        ("Ports::Port", false),
    ] {
        truth(&mut r, motor, general, expected);
    }
    let value = r
        .invoke_operation(motor, SUPERTYPES, &[DerivedValue::Bool(false)])
        .unwrap()
        .value;
    assert_eq!(names(&mut r, value), ["Conform::Diesel", "Parts::parts"]);
    // The written closure says false where the implied one says true.
    let part = r.resolve_qualified("Parts::Part").unwrap();
    assert!(!r.conforms(diesel, part));
    assert!(r.conforms_with_implied(diesel, part));
}

#[test]
fn supertypes_and_their_closure_list_the_implied_bases() {
    let mut r = model();
    let diesel = r.resolve_qualified("Conform::Diesel").unwrap();
    let engine = r.resolve_qualified("Conform::Engine").unwrap();
    let direct = |r: &mut ResolvedModel, receiver: ElementRef, exclude_implied: bool| {
        let value = r
            .invoke_operation(receiver, SUPERTYPES, &[DerivedValue::Bool(exclude_implied)])
            .unwrap()
            .value;
        names(r, value)
    };
    assert_eq!(direct(&mut r, diesel, false), ["Conform::Engine"]);
    assert_eq!(direct(&mut r, diesel, true), ["Conform::Engine"]);
    assert_eq!(direct(&mut r, engine, false), ["Parts::Part"]);
    assert_eq!(direct(&mut r, engine, true), Vec::<String>::new());
    let value = r.invoke_operation(diesel, ALL, &[]).unwrap().value;
    let all = names(&mut r, value);
    assert_eq!(
        all[..3],
        ["Conform::Diesel", "Conform::Engine", "Parts::Part"]
    );
    for name in [
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ] {
        assert!(all.contains(&name.to_owned()), "{name} in {all:?}");
    }
    let unique: std::collections::HashSet<_> = all.iter().collect();
    assert_eq!(unique.len(), all.len());
}
