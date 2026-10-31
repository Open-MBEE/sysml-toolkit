//! The naming operations through `invoke_operation` over the standard
//! library: `namingFeature` and its SysML overrides, `escapedName`, `path`,
//! `allRedefinedFeatures`, `directionOf` and `directionFor`.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "naming.sysml",
        "package Names {
            part def Wheel;
            part def Rover { part drives : Wheel[4]; }
            part def Scout :> Rover { part :>> drives[6]; }
            requirement def Charged { subject battery : Wheel; }
            requirement charged : Charged { subject :>> battery; }
            requirement def Bare { subject : Wheel; }
            action def Step { in item load : Wheel; out item done : Wheel; }
            action def Stride :> Step;
            port def Plug { in item power : Wheel; }
            part scout : Scout;
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

fn reference(value: DerivedValue) -> ElementRef {
    match value {
        DerivedValue::Reference(Reference::Element(e)) => e,
        other => panic!("{other:?}"),
    }
}

#[test]
fn naming_features_follow_redefinitions_and_the_library_roles() {
    let mut r = model();
    const NAMING: &str = "Core-Features-Feature-namingFeature_";
    // `part :>> drives[6];` is named by Rover's drives.
    let drives = undeclared(&mut r, "PartUsage");
    assert_eq!(drives.len(), 1);
    let answer = r.invoke_operation(drives[0], NAMING, &[]).unwrap();
    assert_eq!(
        answer.effective,
        "Systems-DefinitionAndUsage-Usage-namingFeature_"
    );
    let target = reference(answer.value);
    assert_eq!(
        r.element_qualified_name(target).as_deref(),
        Some("Names::Rover::drives")
    );
    // `subject :>> battery;` by the redefined subject; the bare subject by
    // the library's `subj`, the positional redefinition target.
    let subjects = undeclared(&mut r, "ReferenceUsage");
    let mut found = Vec::new();
    for subject in subjects {
        let answer = r.invoke_operation(subject, NAMING, &[]).unwrap();
        assert_eq!(
            answer.effective,
            "Systems-DefinitionAndUsage-ReferenceUsage-namingFeature_"
        );
        let target = reference(answer.value);
        found.push(r.element_qualified_name(target).unwrap());
    }
    found.sort();
    assert_eq!(
        found,
        [
            "Names::Charged::battery",
            "Requirements::RequirementCheck::subj"
        ]
    );
    // A declared, unredefined usage has none.
    let wheel = r.resolve_qualified("Names::Rover::drives").unwrap();
    assert_eq!(
        r.invoke_operation(wheel, NAMING, &[]).unwrap().value,
        DerivedValue::Null
    );
}

#[test]
fn escaped_names_paths_and_redefinition_closures_over_the_library() {
    let mut r = model();
    let scout = r.resolve_qualified("Names::Scout").unwrap();
    assert_eq!(
        r.invoke_operation(scout, "Root-Elements-Element-escapedName_", &[])
            .unwrap()
            .value,
        DerivedValue::Str("Scout".into())
    );
    assert_eq!(
        r.invoke_operation(scout, "Root-Elements-Element-path_", &[])
            .unwrap()
            .value,
        DerivedValue::Str("Names::Scout".into())
    );
    let drives = undeclared(&mut r, "PartUsage")[0];
    assert_eq!(
        r.invoke_operation(drives, "Root-Elements-Element-path_", &[])
            .unwrap()
            .value,
        DerivedValue::Str("Names::Scout::drives".into())
    );
    let value = r
        .invoke_operation(drives, "Core-Features-Feature-allRedefinedFeatures_", &[])
        .unwrap()
        .value;
    let DerivedValue::References(refs) = value else {
        panic!("{value:?}")
    };
    let names: Vec<_> = refs
        .into_iter()
        .map(|reference| match reference {
            Reference::Element(e) => r.element_qualified_name(e).unwrap(),
            other => panic!("{other:?}"),
        })
        .collect();
    assert_eq!(names, ["Names::Scout::drives", "Names::Rover::drives"]);
}

#[test]
fn directions_are_answered_on_action_and_port_definitions() {
    let mut r = model();
    const OF: &str = "Core-Types-Type-directionOf_Feature";
    const FOR: &str = "Core-Features-Feature-directionFor_Type";
    let load = r.resolve_qualified("Names::Step::load").unwrap();
    let done = r.resolve_qualified("Names::Step::done").unwrap();
    let step = r.resolve_qualified("Names::Step").unwrap();
    let stride = r.resolve_qualified("Names::Stride").unwrap();
    let plug = r.resolve_qualified("Names::Plug").unwrap();
    let power = r.resolve_qualified("Names::Plug::power").unwrap();
    let direction = |r: &mut ResolvedModel, owner: ElementRef, feature: ElementRef| {
        r.invoke_operation(owner, OF, &[DerivedValue::Element(feature)])
            .unwrap_or_else(|e| panic!("{e}"))
            .value
    };
    assert_eq!(
        direction(&mut r, step, load),
        DerivedValue::Str("in".into())
    );
    assert_eq!(
        direction(&mut r, step, done),
        DerivedValue::Str("out".into())
    );
    assert_eq!(
        direction(&mut r, stride, load),
        DerivedValue::Str("in".into())
    );
    assert_eq!(
        direction(&mut r, plug, power),
        DerivedValue::Str("in".into())
    );
    // Not a feature of the plug: null.
    assert_eq!(direction(&mut r, plug, load), DerivedValue::Null);
    // The conjugated port definition flips it.
    let conjugate = r.resolve_qualified("Names::Plug::'~Plug'").unwrap();
    assert_eq!(
        direction(&mut r, conjugate, power),
        DerivedValue::Str("out".into())
    );
    assert_eq!(
        r.invoke_operation(power, FOR, &[DerivedValue::Element(conjugate)])
            .unwrap()
            .value,
        DerivedValue::Str("out".into())
    );
}
