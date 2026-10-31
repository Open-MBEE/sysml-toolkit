//! `Element::effectiveName()` / `effectiveShortName()` through
//! `invoke_operation` answer what the `name` and `shortName` properties
//! derive (KerML 8.3.2.1, 8.3.3.3.4), for features named by what they
//! redefine as well as declared ones, so the Namespace resolution bodies
//! answer on ordinary types.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, OperationError, Reference, ResolvedModel},
    model::Model,
};

const NAME: &str = "Core-Features-Feature-effectiveName_";
const SHORT: &str = "Core-Features-Feature-effectiveShortName_";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "names.sysml",
        "package Names {
            part def Wheel;
            part def Rover { part drives : Wheel[4]; }
            part def Scout :> Rover { part :>> drives[6]; }
            part def Plain { part wheels : Wheel; }
            requirement def Power;
            requirement power : Power;
            part scout : Scout { satisfy power by scout; }
            requirement def Charged { subject battery : Wheel; }
            requirement charged : Charged { subject :>> battery; }
        }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

fn undeclared(r: &mut ResolvedModel, metaclass: &str) -> Vec<ElementRef> {
    r.elements_of_metaclass(metaclass)
        .into_iter()
        .filter(|&e| {
            !r.is_library_element(e)
                && r.element_properties(e)
                    .get("declaredName")
                    .is_none_or(|v| v.is_null())
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
fn effective_names_answer_as_the_name_property_does() {
    let mut r = model();
    // `part :>> drives[6];` is named by the feature it redefines.
    let redefining = undeclared(&mut r, "PartUsage");
    assert_eq!(redefining.len(), 1, "{redefining:?}");
    let drives = redefining[0];
    assert_eq!(
        r.property(drives, "name").unwrap(),
        serde_json::json!("drives")
    );
    assert_eq!(
        r.invoke_operation(drives, NAME, &[]).unwrap().value,
        DerivedValue::Str("drives".into())
    );
    assert_eq!(
        r.invoke_operation(drives, SHORT, &[]).unwrap().value,
        DerivedValue::Null
    );
    // `satisfy power by scout;` has no naming feature: null, not refused.
    let satisfy = undeclared(&mut r, "SatisfyRequirementUsage");
    assert_eq!(satisfy.len(), 1);
    assert_eq!(
        r.property(satisfy[0], "name").unwrap(),
        serde_json::Value::Null
    );
    assert_eq!(
        r.invoke_operation(satisfy[0], NAME, &[]).unwrap().value,
        DerivedValue::Null
    );
    // `subject :>> battery;` names itself after the redefined subject,
    // not the library's `subj`.
    let subjects = undeclared(&mut r, "ReferenceUsage");
    let battery = subjects
        .iter()
        .copied()
        .find(|&e| r.property(e, "name").unwrap() == serde_json::json!("battery"))
        .expect("the redefining subject");
    assert_eq!(
        r.invoke_operation(battery, NAME, &[]).unwrap().value,
        DerivedValue::Str("battery".into())
    );
}

#[test]
fn resolution_answers_on_namespaces_with_redefinition_named_members() {
    let mut r = model();
    let drives = undeclared(&mut r, "PartUsage")[0];
    let expected = membership_of(&mut r, drives);
    // On the definition, and on the usage `Names::scout`, which inherits
    // the same member through its typing.
    for namespace in ["Names::Scout", "Names::scout"] {
        let ns = r.resolve_qualified(namespace).unwrap();
        for operation in [
            "Root-Namespaces-Namespace-resolve_String",
            "Root-Namespaces-Namespace-resolveLocal_String",
        ] {
            let answer = r
                .invoke_operation(ns, operation, &[DerivedValue::Str("drives".into())])
                .unwrap_or_else(|e| panic!("{namespace} {operation}: {e}"));
            assert_eq!(answer.value, expected, "{namespace} {operation}");
        }
    }
    let plain = r.resolve_qualified("Names::Plain").unwrap();
    let wheels = r.resolve_qualified("Names::Plain::wheels").unwrap();
    assert_eq!(
        r.invoke_operation(
            plain,
            "Root-Namespaces-Namespace-resolve_String",
            &[DerivedValue::Str("wheels".into())]
        )
        .unwrap()
        .value,
        membership_of(&mut r, wheels)
    );
}

/// The positional names the naming rule confers (`subj`, `obj`,
/// `result`, `viewRendering`, `payload`, `accepter`, the binary ends)
/// come from library features that declare no short name, which is
/// what lets `effectiveShortName()` answer null for a feature named
/// that way without consulting the library element.
#[test]
fn positional_role_features_declare_no_short_names() {
    let mut r = model();
    for name in [
        "Requirements::RequirementCheck::subj",
        "Cases::Case::subj",
        "Cases::Case::obj",
        "Performances::Evaluation::result",
        "Views::View::viewRendering",
        "Transfers::Transfer::payload",
        "Actions::TransitionAction::accepter",
        "Links::BinaryLink::source",
        "Links::BinaryLink::target",
        "Links::SelfLink::thisThing",
        "Links::SelfLink::sameThing",
        "Occurrences::HappensBefore::earlierOccurrence",
        "Occurrences::HappensBefore::laterOccurrence",
    ] {
        let e = r
            .resolve_qualified(name)
            .unwrap_or_else(|| panic!("{name} is in the library"));
        assert_eq!(
            r.property(e, "declaredShortName").unwrap(),
            serde_json::Value::Null,
            "{name}"
        );
    }
}

#[test]
fn an_unresolved_naming_feature_is_refused_not_null() {
    let mut model = Model::new();
    model.add_source(
        "m.kerml",
        "class A { feature x; } class B specializes A { feature :>> x; feature :>> missing; }",
    );
    let mut r = ResolvedModel::build(&model);
    let features = undeclared(&mut r, "Feature");
    let (named, unknown): (Vec<_>, Vec<_>) = features
        .into_iter()
        .partition(|&e| r.property(e, "name").unwrap() == serde_json::json!("x"));
    assert_eq!((named.len(), unknown.len()), (1, 1));
    assert_eq!(
        r.invoke_operation(named[0], NAME, &[]).unwrap().value,
        DerivedValue::Str("x".into())
    );
    assert!(matches!(
        r.invoke_operation(unknown[0], NAME, &[]),
        Err(OperationError::Incomplete { .. })
    ));
}
