//! The featuring and crossing operations through `invoke_operation`
//! (KerML 8.3.3.3.4) over the standard library: `isFeaturingType`,
//! `isFeaturedWithin`, `canAccess`, `ownedCrossFeature`,
//! `isOwnedCrossFeature`, and the second way of `Feature::isCompatibleWith`
//! that `canAccess` completes.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{DerivedValue, Reference, ResolvedModel},
    model::Model,
};

const FEATURING_TYPE: &str = "Core-Features-Feature-isFeaturingType_Type";
const FEATURED_WITHIN: &str = "Core-Features-Feature-isFeaturedWithin_Type";
const CAN_ACCESS: &str = "Core-Features-Feature-canAccess_Feature";
const OWNED_CROSS: &str = "Core-Features-Feature-ownedCrossFeature_";
const IS_OWNED_CROSS: &str = "Core-Features-Feature-isOwnedCrossFeature_";
const COMPATIBLE: &str = "Core-Types-Type-isCompatibleWith_Type";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "access.sysml",
        "package Access {
            part def Wheel { attribute radius : ScalarValues::Real; }
            part def Rover {
                part wheels : Wheel[4];
                attribute mass : ScalarValues::Real;
            }
            part def Buggy :> Rover { part :>> wheels[3]; }
            part def Scout :> Buggy {
                attribute payload : ScalarValues::Real = mass + 1.0;
                part spares :>> Rover::wheels;
            }
            part rover : Rover;
            connection def Mount { end [1] part wheel : Wheel; end part hub : Rover; }
        }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let unit = model.add_source(
        "kern.kerml",
        "package Kern { class A { feature x; var feature v; } class B specializes A; }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

fn truth(r: &mut ResolvedModel, receiver: &str, operation: &str, argument: Option<&str>) -> bool {
    let receiver = r.resolve_qualified(receiver).unwrap();
    let argument = match argument {
        Some(name) => DerivedValue::Element(r.resolve_qualified(name).unwrap()),
        None => DerivedValue::Null,
    };
    match r
        .invoke_operation(receiver, operation, &[argument])
        .unwrap_or_else(|e| panic!("{operation}: {e}"))
        .value
    {
        DerivedValue::Bool(answer) => answer,
        other => panic!("{other:?}"),
    }
}

#[test]
fn featuring_types_and_featured_within_follow_ownership_and_specialization() {
    let mut r = model();
    // A nonvariable feature's featuring type is its owning type.
    assert!(truth(&mut r, "Kern::A::x", FEATURING_TYPE, Some("Kern::A")));
    assert!(!truth(
        &mut r,
        "Kern::A::x",
        FEATURING_TYPE,
        Some("Kern::B")
    ));
    // A variable feature's is a snapshots feature of the owner, never a
    // class other than Occurrence itself.
    assert!(!truth(
        &mut r,
        "Kern::A::v",
        FEATURING_TYPE,
        Some("Kern::A")
    ));
    // A part's attribute may vary in time, so its owner is not its
    // featuring type by this rule either; a constant one's would be.
    assert!(!truth(
        &mut r,
        "Access::Rover::mass",
        FEATURING_TYPE,
        Some("Access::Rover")
    ));
    // Featured within: the type specializes every featuring type.
    assert!(truth(
        &mut r,
        "Access::Rover::wheels",
        FEATURED_WITHIN,
        Some("Access::Buggy")
    ));
    assert!(truth(
        &mut r,
        "Access::Rover::wheels",
        FEATURED_WITHIN,
        Some("Access::Rover")
    ));
    assert!(!truth(
        &mut r,
        "Access::Rover::wheels",
        FEATURED_WITHIN,
        Some("Access::Wheel")
    ));
    assert!(!truth(
        &mut r,
        "Access::Rover::wheels",
        FEATURED_WITHIN,
        None
    ));
    // A package-level part is featured by nothing, that is within Anything
    // and within every type.
    assert!(truth(&mut r, "Access::rover", FEATURED_WITHIN, None));
    assert!(truth(
        &mut r,
        "Access::rover",
        FEATURED_WITHIN,
        Some("Access::Wheel")
    ));
}

#[test]
fn access_follows_the_featuring_types_and_completes_feature_compatibility() {
    let mut r = model();
    // payload is featured by Scout, which specializes Rover, where mass is.
    assert!(truth(
        &mut r,
        "Access::Scout::payload",
        CAN_ACCESS,
        Some("Access::Rover::mass")
    ));
    assert!(!truth(
        &mut r,
        "Access::Wheel::radius",
        CAN_ACCESS,
        Some("Access::Rover::mass")
    ));
    assert!(!truth(
        &mut r,
        "Access::rover",
        CAN_ACCESS,
        Some("Access::Rover::mass")
    ));
    // spares and Buggy's wheels both redefine Rover's wheels, own nothing,
    // and spares (in Scout, which specializes Buggy) can access the other:
    // compatible the second way, and not the other way round.
    assert!(truth(
        &mut r,
        "Access::Scout::spares",
        COMPATIBLE,
        Some("Access::Buggy::wheels")
    ));
    assert!(!truth(
        &mut r,
        "Access::Buggy::wheels",
        COMPATIBLE,
        Some("Access::Scout::spares")
    ));
}

#[test]
fn owned_cross_features_are_the_end_prefix_declarations() {
    let mut r = model();
    let wheel = r.resolve_qualified("Access::Mount::wheel").unwrap();
    let hub = r.resolve_qualified("Access::Mount::hub").unwrap();
    let wheels = r.resolve_qualified("Access::Rover::wheels").unwrap();
    let cross = match r.invoke_operation(wheel, OWNED_CROSS, &[]).unwrap().value {
        DerivedValue::Reference(Reference::Element(cross)) => cross,
        other => panic!("{other:?}"),
    };
    assert_eq!(r.element_type(cross), "ReferenceUsage");
    assert_eq!(r.owner(cross), Some(wheel));
    assert_eq!(
        r.invoke_operation(cross, IS_OWNED_CROSS, &[])
            .unwrap()
            .value,
        DerivedValue::Bool(true)
    );
    for end in [hub, wheels] {
        assert_eq!(
            r.invoke_operation(end, OWNED_CROSS, &[]).unwrap().value,
            DerivedValue::Null
        );
        assert_eq!(
            r.invoke_operation(end, IS_OWNED_CROSS, &[]).unwrap().value,
            DerivedValue::Bool(false)
        );
    }
}
