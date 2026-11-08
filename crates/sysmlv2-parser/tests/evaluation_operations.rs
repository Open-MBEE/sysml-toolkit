//! The model-level evaluation operations through `invoke_operation` over
//! the standard library: `evaluate`, `checkCondition`,
//! `modelLevelEvaluable`, the `instantiatedType` bodies, the multiplicity
//! bound operations, the metadata feature operations and the metadata
//! access bodies (KerML 8.3.4.1.3, 8.3.4.8, 8.3.4.13, 8.3.4.14).

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{Derived, DerivedValue, ElementRef, OperationError, Reference, ResolvedModel},
    model::Model,
};

const EVALUATE: &str = "Kernel-Functions-Expression-evaluate_Element";
const CHECK: &str = "Kernel-Functions-Expression-checkCondition_Element";
const EVALUABLE: &str = "Kernel-Functions-Expression-modelLevelEvaluable_Feature";
const INSTANTIATED: &str = "Kernel-Expressions-InstantiationExpression-instantiatedType_";
const VALUE_OF: &str = "Kernel-Multiplicities-MultiplicityRange-valueOf_Expression";
const HAS_BOUNDS: &str =
    "Kernel-Multiplicities-MultiplicityRange-hasBounds_Integer_UnlimitedNatural";
const NODE_BOUNDS: &str =
    "Systems-Actions-ControlNode-multiplicityHasBounds_Multiplicity_Integer_UnlimitedNatural";
const EVALUATE_FEATURE: &str = "Kernel-Metadata-MetadataFeature-evaluateFeature_Feature";
const SEMANTIC: &str = "Kernel-Metadata-MetadataFeature-isSemantic_";
const SYNTACTIC: &str = "Kernel-Metadata-MetadataFeature-isSyntactic_";
const SYNTAX_ELEMENT: &str = "Kernel-Metadata-MetadataFeature-syntaxElement_";
const METADATA_EVALUATE: &str = "Kernel-Expressions-MetadataAccessExpression-evaluate_Element";
const METACLASS_FEATURE: &str = "Kernel-Expressions-MetadataAccessExpression-metaclassFeature_";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "eval.sysml",
        "package Eval {
            part def Wheel;
            calc def Area { in x : ScalarValues::Real; return : ScalarValues::Real = x * x; }
            part def Rover {
                attribute mass : ScalarValues::Real = 2.5;
                attribute count : ScalarValues::Integer = 2 + 3;
                attribute flag : ScalarValues::Boolean = 1 < 2;
                attribute label : ScalarValues::String = \"r\";
                attribute twice : ScalarValues::Real = mass * 2;
                attribute area : ScalarValues::Real = Area(2.0);
                part wheels : Wheel[4];
                part spares : Wheel[0..*];
                part axle : Wheel[1..2];
            }
            action def Go { accept at 1.0; fork f; }
            metadata def Tag { attribute level : ScalarValues::Integer = 0; }
            metadata def Marker :> Metaobjects::SemanticMetadata;
            part tagged : Rover { @Tag { :>> level = 3; } @Marker; @KerML::Package; @SysML::PartUsage; }
            part plain : Rover { @Tag; }
            metadata def MyPart :> SysML::PartUsage;
            part mine : Rover { @MyPart; }
            attribute probe = tagged.metadata;
        }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

/// The value expression of a feature: its owned Expression.
fn value_expression(r: &mut ResolvedModel, feature: &str) -> ElementRef {
    let feature = r.resolve_qualified(feature).unwrap();
    let elements: Vec<ElementRef> = r.user_elements().collect();
    elements
        .into_iter()
        .find(|&e| {
            r.owner(e) == Some(feature)
                && (r.element_type(e).ends_with("Expression")
                    || r.element_type(e).starts_with("Literal"))
        })
        .expect("a value expression")
}
fn literals(value: DerivedValue) -> Vec<String> {
    match value {
        DerivedValue::Literals(values) => values,
        other => panic!("{other:?}"),
    }
}
fn declared_name(r: &mut ResolvedModel, value: DerivedValue) -> (String, String) {
    let DerivedValue::Reference(Reference::Element(e)) = value else {
        panic!("{value:?}")
    };
    let name = r.property(e, "declaredName").unwrap();
    let owner = r.owner(e).unwrap();
    let owner = r.property(owner, "declaredName").unwrap();
    (
        name.as_str().unwrap().to_owned(),
        owner.as_str().unwrap().to_owned(),
    )
}
fn literal(text: &str) -> DerivedValue {
    DerivedValue::Literal(text.to_owned())
}

#[test]
fn expressions_evaluate_at_model_level_from_the_target() {
    let mut r = model();
    let rover = r.resolve_qualified("Eval::Rover").unwrap();
    let target = [DerivedValue::Element(rover)];
    // A literal is its own model-level value; a computed value is returned
    // in the spelling of the literal that would carry it.
    for feature in ["Eval::Rover::mass", "Eval::Rover::label"] {
        let expression = value_expression(&mut r, feature);
        let answer = r.invoke_operation(expression, EVALUATE, &target).unwrap();
        assert_eq!(
            answer.effective,
            "Kernel-Expressions-LiteralExpression-evaluate_Element"
        );
        assert_eq!(
            answer.value,
            DerivedValue::References(vec![Reference::Element(expression)])
        );
    }
    for (feature, expected) in [("Eval::Rover::count", "5"), ("Eval::Rover::flag", "true")] {
        let expression = value_expression(&mut r, feature);
        let answer = r
            .invoke_operation(expression, EVALUATE, &target)
            .unwrap_or_else(|e| panic!("{feature}: {e}"));
        assert_eq!(
            answer.effective,
            "Kernel-Expressions-InvocationExpression-evaluate_Element"
        );
        assert_eq!(literals(answer.value), [expected], "{feature}");
    }
    // A reference to a featured feature is not model-level evaluable: the
    // evaluation is empty and the eligibility is false.
    let twice = value_expression(&mut r, "Eval::Rover::twice");
    assert_eq!(
        r.invoke_operation(twice, EVALUATE, &target).unwrap().value,
        DerivedValue::References(vec![])
    );
    let none = [DerivedValue::Elements(vec![])];
    assert_eq!(
        r.invoke_operation(twice, EVALUABLE, &none).unwrap().value,
        DerivedValue::Bool(false)
    );
    let count = value_expression(&mut r, "Eval::Rover::count");
    assert_eq!(
        r.invoke_operation(count, EVALUABLE, &none).unwrap().value,
        DerivedValue::Bool(true)
    );
    // The visited features are not tracked.
    let mass = r.resolve_qualified("Eval::Rover::mass").unwrap();
    assert!(matches!(
        r.invoke_operation(count, EVALUABLE, &[DerivedValue::Elements(vec![mass])]),
        Err(OperationError::UnsupportedConfiguration { .. })
    ));
    // A condition holds when its one value is the Boolean true.
    let flag = value_expression(&mut r, "Eval::Rover::flag");
    assert_eq!(
        r.invoke_operation(flag, CHECK, &target).unwrap().value,
        DerivedValue::Bool(true)
    );
    assert_eq!(
        r.invoke_operation(count, CHECK, &target).unwrap().value,
        DerivedValue::Bool(false)
    );
}

#[test]
fn instantiated_types_resolve_through_the_library() {
    let mut r = model();
    let count = value_expression(&mut r, "Eval::Rover::count");
    let answer = r.invoke_operation(count, INSTANTIATED, &[]).unwrap();
    assert_eq!(
        answer.effective,
        "Kernel-Expressions-OperatorExpression-instantiatedType_"
    );
    assert_eq!(
        declared_name(&mut r, answer.value),
        ("+".to_owned(), "DataFunctions".to_owned())
    );
    let flag = value_expression(&mut r, "Eval::Rover::flag");
    let answer = r.invoke_operation(flag, INSTANTIATED, &[]).unwrap().value;
    assert_eq!(
        declared_name(&mut r, answer),
        ("<".to_owned(), "DataFunctions".to_owned())
    );
    let area = value_expression(&mut r, "Eval::Rover::area");
    let function = r.resolve_qualified("Eval::Area").unwrap();
    let answer = r.invoke_operation(area, INSTANTIATED, &[]).unwrap();
    assert_eq!(answer.effective, INSTANTIATED);
    assert_eq!(
        answer.value,
        DerivedValue::Reference(Reference::Element(function))
    );
    let trigger = r.elements_of_metaclass("TriggerInvocationExpression")[0];
    let answer = r.invoke_operation(trigger, INSTANTIATED, &[]).unwrap();
    assert_eq!(
        answer.effective,
        "Systems-Actions-TriggerInvocationExpression-instantiatedType_"
    );
    assert_eq!(
        declared_name(&mut r, answer.value),
        ("TriggerAt".to_owned(), "Triggers".to_owned())
    );
}

fn range(r: &mut ResolvedModel, feature: &str) -> ElementRef {
    let feature = r.resolve_qualified(feature).unwrap();
    r.property(feature, "multiplicity").unwrap()["@id"]
        .as_str()
        .map(|id| r.element_by_id(id).unwrap())
        .expect("a multiplicity")
}
fn bound(r: &mut ResolvedModel, range: ElementRef, which: &str) -> DerivedValue {
    match r.derived(range, which) {
        Derived::Value(DerivedValue::Element(e))
        | Derived::Value(DerivedValue::Reference(Reference::Element(e))) => {
            DerivedValue::Element(e)
        }
        Derived::Value(DerivedValue::Null) => DerivedValue::Null,
        other => panic!("{which}: {other:?}"),
    }
}

#[test]
fn multiplicity_bounds_evaluate_to_naturals() {
    let mut r = model();
    let wheels = range(&mut r, "Eval::Rover::wheels");
    let spares = range(&mut r, "Eval::Rover::spares");
    let axle = range(&mut r, "Eval::Rover::axle");
    let upper = bound(&mut r, wheels, "upperBound");
    assert_eq!(
        r.invoke_operation(wheels, VALUE_OF, &[upper])
            .unwrap()
            .value,
        literal("4")
    );
    assert_eq!(
        r.invoke_operation(wheels, VALUE_OF, &[DerivedValue::Null])
            .unwrap()
            .value,
        DerivedValue::Null
    );
    let upper = bound(&mut r, spares, "upperBound");
    assert_eq!(
        r.invoke_operation(spares, VALUE_OF, &[upper])
            .unwrap()
            .value,
        literal("*")
    );
    let lower = bound(&mut r, spares, "lowerBound");
    assert_eq!(
        r.invoke_operation(spares, VALUE_OF, &[lower])
            .unwrap()
            .value,
        literal("0")
    );
    let has = |r: &mut ResolvedModel, range: ElementRef, lower: &str, upper: &str| match r
        .invoke_operation(range, HAS_BOUNDS, &[literal(lower), literal(upper)])
        .unwrap_or_else(|e| panic!("{lower}..{upper}: {e}"))
        .value
    {
        DerivedValue::Bool(answer) => answer,
        other => panic!("{other:?}"),
    };
    // A single bound is both: `[4]` is 4..4.
    assert!(has(&mut r, wheels, "4", "4"));
    assert!(!has(&mut r, wheels, "0", "4"));
    assert!(!has(&mut r, wheels, "4", "*"));
    assert!(has(&mut r, spares, "0", "*"));
    assert!(!has(&mut r, spares, "1", "*"));
    assert!(has(&mut r, axle, "1", "2"));
    assert!(!has(&mut r, axle, "2", "2"));
    // A control node checks any multiplicity it is given.
    let fork = r.elements_of_metaclass("ForkNode")[0];
    let node = |r: &mut ResolvedModel, range: ElementRef, lower: &str, upper: &str| {
        r.invoke_operation(
            fork,
            NODE_BOUNDS,
            &[DerivedValue::Element(range), literal(lower), literal(upper)],
        )
        .unwrap()
        .value
    };
    assert_eq!(node(&mut r, wheels, "4", "4"), DerivedValue::Bool(true));
    assert_eq!(node(&mut r, spares, "4", "4"), DerivedValue::Bool(false));
}

fn metadata(r: &mut ResolvedModel, owner: &str, metaclass: &str) -> ElementRef {
    let owner = r.resolve_qualified(owner).unwrap();
    let metaclass = r.resolve_qualified(metaclass).unwrap();
    let usages = r.elements_of_metaclass("MetadataUsage");
    usages
        .into_iter()
        .find(|&e| {
            r.owner(e) == Some(owner)
                && matches!(
                    r.derived(e, "metaclass"),
                    Derived::Value(DerivedValue::Reference(Reference::Element(m))) if m == metaclass
                )
        })
        .expect("the metadata usage")
}

#[test]
fn metadata_features_answer_their_kind_and_their_values() {
    let mut r = model();
    let marker = metadata(&mut r, "Eval::tagged", "Eval::Marker");
    let package = metadata(&mut r, "Eval::tagged", "KerML::Package");
    let tag = metadata(&mut r, "Eval::tagged", "Eval::Tag");
    let bare = metadata(&mut r, "Eval::plain", "Eval::Tag");
    assert_eq!(
        r.invoke_operation(marker, SEMANTIC, &[]).unwrap().value,
        DerivedValue::Bool(true)
    );
    assert_eq!(
        r.invoke_operation(package, SYNTACTIC, &[]).unwrap().value,
        DerivedValue::Bool(true)
    );
    // The level redefined in the body evaluates with the metadata feature
    // as the target; a bare annotation inherits it, which is not certified.
    let level = r.resolve_qualified("Eval::Tag::level").unwrap();
    let argument = [DerivedValue::Element(level)];
    assert_eq!(
        literals(
            r.invoke_operation(tag, EVALUATE_FEATURE, &argument)
                .unwrap()
                .value
        ),
        ["3"]
    );
    assert!(matches!(
        r.invoke_operation(bare, EVALUATE_FEATURE, &argument),
        Err(OperationError::Incomplete { .. })
    ));
}

/// KerML 8.3.4.8.8: `tagged.metadata` evaluates to the metadata features
/// the part owns that annotate it, then its metaclass feature, answered
/// by the reflective metaclass that types it (`SysML::PartUsage`), which
/// `metaclassFeature` answers alone. KerML 8.3.4.14: the reflective
/// annotation's syntax element is the part; a `KerML::Package` annotation
/// on a part represents nothing; a semantic annotation is not syntactic;
/// a metadata definition specializing a reflective metaclass is syntactic
/// through it.
#[test]
fn metadata_access_evaluates_over_the_reflection_library() {
    let mut r = model();
    let probe = value_expression(&mut r, "Eval::probe");
    let tagged = r.resolve_qualified("Eval::tagged").unwrap();
    let part_usage = r.resolve_qualified("SysML::PartUsage").unwrap();
    let tag = metadata(&mut r, "Eval::tagged", "Eval::Tag");
    let marker = metadata(&mut r, "Eval::tagged", "Eval::Marker");
    let package = metadata(&mut r, "Eval::tagged", "KerML::Package");
    let reflective = metadata(&mut r, "Eval::tagged", "SysML::PartUsage");
    let target = [DerivedValue::Element(tagged)];
    let result = r
        .invoke_operation(probe, METADATA_EVALUATE, &target)
        .unwrap();
    assert_eq!(result.effective, METADATA_EVALUATE);
    assert_eq!(
        result.value,
        DerivedValue::References(
            [tag, marker, package, reflective, part_usage]
                .map(Reference::Element)
                .to_vec()
        )
    );
    assert_eq!(
        r.invoke_operation(probe, EVALUATE, &target)
            .unwrap()
            .effective,
        METADATA_EVALUATE
    );
    assert_eq!(
        r.invoke_operation(probe, METACLASS_FEATURE, &[])
            .unwrap()
            .value,
        DerivedValue::Reference(Reference::Element(part_usage))
    );
    assert_eq!(
        r.invoke_operation(reflective, SYNTAX_ELEMENT, &[])
            .unwrap()
            .value,
        DerivedValue::Reference(Reference::Element(tagged))
    );
    assert_eq!(
        r.invoke_operation(package, SYNTAX_ELEMENT, &[])
            .unwrap()
            .value,
        DerivedValue::Null
    );
    assert_eq!(
        r.invoke_operation(tag, SYNTAX_ELEMENT, &[]).unwrap().value,
        DerivedValue::Null
    );
    // A metadata definition of the model that specializes a reflective
    // metaclass is syntactic through it: its feature represents the part.
    let mine = r.resolve_qualified("Eval::mine").unwrap();
    let my_part = metadata(&mut r, "Eval::mine", "Eval::MyPart");
    assert_eq!(
        r.invoke_operation(my_part, SYNTAX_ELEMENT, &[])
            .unwrap()
            .value,
        DerivedValue::Reference(Reference::Element(mine))
    );
}
