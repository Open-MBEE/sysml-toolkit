//! The checked member lists (`feature`, `inheritedMembership`,
//! `featureMembership`, `member`, `membership`, `importedMembership`) and
//! the Namespace resolution bodies on usage receivers: a part, item or
//! attribute usage owned by a definition, by another usage or by a package,
//! with or without a value, over the standard library; ends and
//! parameters too, whose positional targets come from their owner's
//! certificate, an end whose reference is a chain among them, through a
//! conjugated port definition included.

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

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "needs.sysml",
        "package Needs {
            port def Out { out attribute v : ScalarValues::Real; }
            part def Box {
                port o : Out;
                port i : ~Out;
                attribute x : ScalarValues::Real = 1.0 + 2.0;
                attribute y : ScalarValues::Real;
            }
            part def Sys {
                part a : Box;
                part b : Box { attribute z : ScalarValues::Real; part c : Box; }
                connect a.o to b.i;
            }
            requirement def R { subject s : Sys; }
            part sys : Sys;
            part scout : Sys { part :>> a; }
            item def Cargo;
            item freight : Cargo;
        }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}

fn ids(r: &mut ResolvedModel, value: &serde_json::Value) -> Vec<String> {
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

fn membership_of(r: &mut ResolvedModel, e: ElementRef) -> DerivedValue {
    let id = r.property(e, "owningRelationship").unwrap()["@id"]
        .as_str()
        .expect("an owned feature has an owning membership")
        .to_owned();
    DerivedValue::Reference(Reference::Element(r.element_by_id(&id).unwrap()))
}

#[test]
fn usage_receivers_answer_the_member_lists() {
    let mut r = model();
    for path in [
        "Needs::Sys::a",
        "Needs::Sys::b",
        "Needs::Sys::b::c",
        "Needs::Sys::b::z",
        "Needs::Box::x",
        "Needs::Box::y",
        "Needs::sys",
        "Needs::scout",
        "Needs::freight",
    ] {
        let e = r.resolve_qualified(path).unwrap();
        for property in LISTS {
            r.property(e, property)
                .unwrap_or_else(|err| panic!("{path}.{property}: {err}"));
        }
    }
    // The typing definition's features come first, in declaration order,
    // and the library's follow.
    let a = r.resolve_qualified("Needs::Sys::a").unwrap();
    let features = r.property(a, "feature").unwrap();
    let names = ids(&mut r, &features);
    assert_eq!(
        &names[..4],
        [
            "Needs::Box::o",
            "Needs::Box::i",
            "Needs::Box::x",
            "Needs::Box::y"
        ]
    );
    assert!(names.iter().any(|n| n == "Parts::Part::self"), "{names:?}");
    assert!(
        names
            .iter()
            .any(|n| n == "Occurrences::Occurrence::suboccurrences"),
        "{names:?}"
    );
    // A valued attribute's value expression is one of its members and
    // none of its features.
    let x = r.resolve_qualified("Needs::Box::x").unwrap();
    let expression = r
        .elements_of_metaclass("OperatorExpression")
        .into_iter()
        .find(|&e| r.owner(e) == Some(x))
        .expect("the value expression");
    let expression = r.element_id(expression).to_string();
    let members = r.property(x, "member").unwrap();
    assert!(
        members
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v["@id"] == expression)
    );
    let features = r.property(x, "feature").unwrap();
    assert!(
        !features
            .as_array()
            .unwrap()
            .iter()
            .any(|v| v["@id"] == expression)
    );
}

#[test]
fn usage_receivers_answer_the_resolution_bodies() {
    let mut r = model();
    const RESOLVE: &str = "Root-Namespaces-Namespace-resolve_String";
    const LOCAL: &str = "Root-Namespaces-Namespace-resolveLocal_String";
    let scout = r.resolve_qualified("Needs::scout").unwrap();
    let sys = r.resolve_qualified("Needs::sys").unwrap();
    let redefining = r
        .elements_of_metaclass("PartUsage")
        .into_iter()
        .find(|&e| r.owner(e) == Some(scout))
        .expect("the redefining part");
    let inherited_a = r.resolve_qualified("Needs::Sys::a").unwrap();
    let inherited_b = r.resolve_qualified("Needs::Sys::b").unwrap();
    // An owned member answers before the inherited one of its name; a name
    // the usage does not redefine answers through its typing.
    let expected = membership_of(&mut r, redefining);
    for operation in [RESOLVE, LOCAL] {
        assert_eq!(
            r.invoke_operation(scout, operation, &[DerivedValue::Str("a".into())])
                .unwrap_or_else(|e| panic!("{operation}: {e}"))
                .value,
            expected
        );
    }
    let expected = membership_of(&mut r, inherited_b);
    assert_eq!(
        r.invoke_operation(scout, RESOLVE, &[DerivedValue::Str("b".into())])
            .unwrap()
            .value,
        expected
    );
    let expected = membership_of(&mut r, inherited_a);
    assert_eq!(
        r.invoke_operation(sys, LOCAL, &[DerivedValue::Str("a".into())])
            .unwrap()
            .value,
        expected
    );
}

#[test]
fn ends_and_parameters_answer_the_member_lists() {
    let mut r = model();
    let subject = r.resolve_qualified("Needs::R::s").unwrap();
    let sys = r.resolve_qualified("Needs::Sys").unwrap();
    let ends: Vec<ElementRef> = r
        .elements_of_metaclass("ReferenceUsage")
        .into_iter()
        .filter(|&e| {
            r.owner(e).is_some_and(|owner| {
                r.element_type(owner) == "ConnectionUsage" && r.owner(owner) == Some(sys)
            })
        })
        .collect();
    assert_eq!(ends.len(), 2, "the connector's ends");
    for property in LISTS {
        r.property(subject, property)
            .unwrap_or_else(|err| panic!("subject.{property}: {err}"));
    }
    // The subject inherits its type's features.
    let features = r.property(subject, "feature").unwrap();
    let names = ids(&mut r, &features);
    assert!(names.iter().any(|n| n == "Needs::Sys::a"), "{names:?}");
    // Both connector ends reference a chain (`a.o`, `b.i`): their scopes'
    // providers are proved through the chain's last link, so each end
    // inherits the port's features — the second through the conjugated
    // port definition `~Out`, whose `out v` is its input.
    let v = r.resolve_qualified("Needs::Out::v").unwrap();
    for end in &ends {
        let features = r.property(*end, "feature").unwrap();
        let names = ids(&mut r, &features);
        assert!(names.iter().any(|n| n == "Needs::Out::v"), "{names:?}");
    }
    assert_eq!(
        r.type_feature_report(ends[0]).projections.unwrap().outputs,
        [v]
    );
    assert_eq!(
        r.type_feature_report(ends[1]).projections.unwrap().inputs,
        [v]
    );
}
