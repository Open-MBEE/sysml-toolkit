//! The specialization-structure operations through `invoke_operation`
//! (KerML 8.3.3.1.10, 8.3.3.3.4) over the standard library:
//! `Type::specializesFromLibrary` and `multiplicities`,
//! `Feature::redefines`, `redefinesFromLibrary`, `subsetsChain` and
//! `typingFeatures`.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

const SPECIALIZES_LIB: &str = "Core-Types-Type-specializesFromLibrary_String";
const MULTIPLICITIES: &str = "Core-Types-Type-multiplicities_";
const REDEFINES: &str = "Core-Features-Feature-redefines_Feature";
const REDEFINES_LIB: &str = "Core-Features-Feature-redefinesFromLibrary_String";
const SUBSETS_CHAIN: &str = "Core-Features-Feature-subsetsChain_Feature_Feature";
const TYPING_FEATURES: &str = "Core-Features-Feature-typingFeatures_";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "spec.sysml",
        "package Spec {
            part def Wheel;
            part def Rover { part wheels : Wheel[4]; part spare : Wheel; }
            part def Buggy :> Rover { part :>> wheels[3]; }
            part rover : Rover;
            part def Train { part cars : Rover[2..*]; part lead : Rover :> cars; }
            part def Linked { part a : Rover; part b : Wheel :> a.wheels; }
            connection def Mount { end part wheel : Wheel; end part hub : Rover; }
        }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let unit = model.add_source(
        "conj.kerml",
        "package Conj { classifier A { feature f; } classifier B ~ A; feature g : A; feature h ~ g; }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

fn element(r: &mut ResolvedModel, path: &str) -> DerivedValue {
    DerivedValue::Element(r.resolve_qualified(path).unwrap())
}

fn truth(
    r: &mut ResolvedModel,
    receiver: &str,
    operation: &str,
    arguments: &[DerivedValue],
) -> bool {
    let receiver = r.resolve_qualified(receiver).unwrap();
    match r
        .invoke_operation(receiver, operation, arguments)
        .unwrap_or_else(|e| panic!("{operation}: {e}"))
        .value
    {
        DerivedValue::Bool(answer) => answer,
        other => panic!("{other:?}"),
    }
}

fn listed(r: &mut ResolvedModel, receiver: &str, operation: &str) -> Vec<String> {
    let receiver = r.resolve_qualified(receiver).unwrap();
    match r
        .invoke_operation(receiver, operation, &[])
        .unwrap_or_else(|e| panic!("{operation}: {e}"))
        .value
    {
        DerivedValue::References(list) => list
            .into_iter()
            .map(|reference| match reference {
                Reference::Element(e) => spell(r, e),
                other => panic!("{other:?}"),
            })
            .collect(),
        other => panic!("{other:?}"),
    }
}

/// A qualified name, or for an anonymous multiplicity range its owner's
/// name and the range's bounds as the evaluator reads them.
fn spell(r: &mut ResolvedModel, e: ElementRef) -> String {
    if let Some(name) = r.element_qualified_name(e) {
        return name;
    }
    let owner = r
        .owner(e)
        .and_then(|o| r.element_qualified_name(o))
        .unwrap_or_default();
    format!("{owner}[{}]", r.element_type(e))
}

#[test]
fn redefines_and_the_library_lookups_follow_the_owned_redefinitions() {
    let mut r = model();
    let wheels = element(&mut r, "Spec::Rover::wheels");
    assert!(truth(
        &mut r,
        "Spec::Buggy::wheels",
        REDEFINES,
        std::slice::from_ref(&wheels)
    ));
    assert!(!truth(&mut r, "Spec::Rover::spare", REDEFINES, &[wheels]));
    // A connection definition's first end redefines the binary connection's
    // source by position; the link's end is two redefinitions away.
    for (name, expected) in [
        ("Connections::BinaryConnection::source", true),
        ("Links::BinaryLink::source", false),
        ("Links::Link::participant", false),
        ("Nope::Missing", false),
    ] {
        let argument = [DerivedValue::Str(name.into())];
        assert_eq!(
            truth(&mut r, "Spec::Mount::wheel", REDEFINES_LIB, &argument),
            expected,
            "{name}"
        );
    }
    for (receiver, name, expected) in [
        ("Spec::Wheel", "Parts::Part", true),
        ("Spec::Wheel", "Items::Item", true),
        ("Spec::Wheel", "Ports::Port", false),
        ("Spec::Wheel", "Nope::Missing", false),
        ("Spec::rover", "Parts::parts", true),
    ] {
        let argument = [DerivedValue::Str(name.into())];
        assert_eq!(
            truth(&mut r, receiver, SPECIALIZES_LIB, &argument),
            expected,
            "{receiver} {name}"
        );
    }
}

#[test]
fn subsets_chain_reads_the_chain_a_subsetting_names() {
    let mut r = model();
    let a = element(&mut r, "Spec::Linked::a");
    let wheels = element(&mut r, "Spec::Rover::wheels");
    let spare = element(&mut r, "Spec::Rover::spare");
    // The chain among the written supertypes is a witness; the absence of
    // one needs the complete closure, which the chain's last link
    // certifies for a feature whose scope names a chain.
    assert!(truth(
        &mut r,
        "Spec::Linked::b",
        SUBSETS_CHAIN,
        &[a.clone(), wheels.clone()]
    ));
    assert!(!truth(
        &mut r,
        "Spec::Linked::b",
        SUBSETS_CHAIN,
        &[a.clone(), spare]
    ));
    assert!(!truth(
        &mut r,
        "Spec::Linked::a",
        SUBSETS_CHAIN,
        &[a, wheels]
    ));
}

#[test]
fn typing_features_are_the_written_then_implied_subsettings() {
    let mut r = model();
    for (receiver, expected) in [
        ("Spec::Rover::wheels", vec!["Items::Item::subparts"]),
        ("Spec::Rover::spare", vec!["Items::Item::subparts"]),
        ("Spec::Buggy::wheels", vec!["Spec::Rover::wheels"]),
        ("Spec::Train::lead", vec!["Spec::Train::cars"]),
        ("Spec::rover", vec!["Parts::parts"]),
        (
            "Spec::Mount::wheel",
            vec!["Parts::parts", "Connections::BinaryConnection::source"],
        ),
        // A conjugated feature answers its original; a Kernel feature the
        // generic role.
        ("Conj::h", vec!["Conj::g"]),
        ("Conj::g", vec!["Base::things"]),
    ] {
        assert_eq!(
            listed(&mut r, receiver, TYPING_FEATURES),
            expected,
            "{receiver}"
        );
    }
    // A feature subsetting a chain (`b :> a.wheels`) answers the chain
    // feature itself, as its one subsetted feature.
    let b = r.resolve_qualified("Spec::Linked::b").unwrap();
    let chain = match r.invoke_operation(b, TYPING_FEATURES, &[]).unwrap().value {
        DerivedValue::References(list) => match list.as_slice() {
            [Reference::Element(chain)] => *chain,
            other => panic!("{other:?}"),
        },
        other => panic!("{other:?}"),
    };
    assert_eq!(r.element_type(chain), "Feature");
    let links = r.property(chain, "chainingFeature").unwrap();
    let links: Vec<String> = links
        .as_array()
        .unwrap()
        .iter()
        .map(|v| {
            let e = r.element_by_id(v["@id"].as_str().unwrap()).unwrap();
            r.element_qualified_name(e).unwrap()
        })
        .collect();
    assert_eq!(links, ["Spec::Linked::a", "Spec::Rover::wheels"]);
}

#[test]
fn multiplicities_stop_at_the_nearest_declared_ones() {
    let mut r = model();
    for (receiver, expected) in [
        (
            "Spec::Rover::wheels",
            vec!["Spec::Rover::wheels[MultiplicityRange]"],
        ),
        (
            "Spec::Buggy::wheels",
            vec!["Spec::Buggy::wheels[MultiplicityRange]"],
        ),
        (
            "Spec::Train::cars",
            vec!["Spec::Train::cars[MultiplicityRange]"],
        ),
        (
            "Spec::Train::lead",
            vec!["Spec::Train::cars[MultiplicityRange]"],
        ),
        ("Spec::rover", vec!["Parts::parts[MultiplicityRange]"]),
        ("Spec::Rover", vec![]),
        // An end feature owns its default multiplicity (SysML 7.6.3), the
        // nearest declared one; the library ends' ranges lie behind it.
        (
            "Spec::Mount::wheel",
            vec!["Spec::Mount::wheel[Multiplicity]"],
        ),
        ("Conj::h", vec!["Base::things[MultiplicityRange]"]),
    ] {
        assert_eq!(
            listed(&mut r, receiver, MULTIPLICITIES),
            expected,
            "{receiver}"
        );
    }
}
