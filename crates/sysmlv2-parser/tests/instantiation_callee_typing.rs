//! Instantiation expressions typed by their callee (KerML 8.3.4.8,
//! `checkInvocationExpressionSpecialization`): an operator, invocation or
//! trigger expression owns an implied FeatureTyping by its
//! `instantiatedType` (a Subsetting where the callee is a feature), planned
//! as a row beside its kind role; its argument parameters redefine the
//! callee's input parameters in order
//! (`validateInvocationExpressionParameterRedefinition`); the checked reader
//! certifies `type`, `function` and `argument` through those rows (#53,
//! the instantiation part of #51). An expression whose callee does not
//! resolve keeps its kind role alone and stays out of the checked reads.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, ElementRef, Reference, ResolvedModel},
    model::{GraphFormat, Model},
};
use uuid::Uuid;

const SOURCE: &str = "package Results {
    calc def Double { in x : ScalarValues::Real; return : ScalarValues::Real = 2 * x; }
    calc def Shift { out log : ScalarValues::Real; in v : ScalarValues::Real; return : ScalarValues::Real = v; }
    calc double : Double;
    part def P {
        attribute a : ScalarValues::Real = 1.0;
        attribute call : ScalarValues::Real = Double(a);
        attribute named : ScalarValues::Real = Double(x = a);
        attribute lib : ScalarValues::Real = RealFunctions::sqrt(a);
        attribute viaUsage : ScalarValues::Real = double(a);
        attribute shifted : ScalarValues::Real = Shift(a);
        attribute power : ScalarValues::Real = a ** a;
        attribute less : ScalarValues::Boolean = a < a;
        attribute bad : ScalarValues::Real = Missing(a);
        part q : P;
        attribute chained : ScalarValues::Real = q.a;
    }
    action def Listen { accept sig : ScalarValues::Real at 3; }
}";

fn model() -> ResolvedModel {
    model_with(GraphFormat::LegacyV2)
}

fn model_with(format: GraphFormat) -> ResolvedModel {
    let mut model = Model::with_graph_format(format);
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("callees.sysml", SOURCE);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
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

/// The value expression of the feature `path` names.
fn value_of(r: &mut ResolvedModel, path: &str) -> ElementRef {
    let feature = named(r, path);
    r.members_via(feature, "FeatureValue")[0]
}

/// The implied relationships of `e` as `(metaclass, target qualified name)`.
fn implied(r: &mut ResolvedModel, e: ElementRef) -> Vec<(String, String)> {
    let rows = r.implied_relationships(e);
    let mut out = Vec::new();
    for row in rows {
        let kind = r.element_type(row).to_string();
        for target in r.relationship_ends(row).1 {
            if let Reference::Element(target) = target {
                let name = r
                    .element_qualified_name(target)
                    .unwrap_or_else(|| format!("<{}>", r.element_type(target)));
                out.push((kind.clone(), name));
            }
        }
    }
    out
}

fn implied_id(owner: ElementRef, kind: &str, target: ElementRef, r: &ResolvedModel) -> Uuid {
    Uuid::new_v5(
        &Uuid::NAMESPACE_OID,
        format!(
            "{}/implied/{kind}/{}",
            r.element_id(owner),
            r.element_id(target)
        )
        .as_bytes(),
    )
}

fn id_of(value: &serde_json::Value) -> String {
    value["@id"].as_str().unwrap().to_string()
}

#[test]
fn callee_typings_are_planned_rows_beside_the_kind_role() {
    let mut r = model();
    for (path, callee, kind) in [
        (
            "Results::Double::result",
            "DataFunctions::'*'",
            "FeatureTyping",
        ),
        ("Results::P::call", "Results::Double", "FeatureTyping"),
        ("Results::P::named", "Results::Double", "FeatureTyping"),
        ("Results::P::lib", "RealFunctions::sqrt", "FeatureTyping"),
        ("Results::P::shifted", "Results::Shift", "FeatureTyping"),
        ("Results::P::power", "DataFunctions::'**'", "FeatureTyping"),
        ("Results::P::less", "DataFunctions::'<'", "FeatureTyping"),
        ("Results::P::viaUsage", "Results::double", "Subsetting"),
        (
            "Results::P::chained",
            "ControlFunctions::'.'",
            "FeatureTyping",
        ),
    ] {
        let expression = value_of(&mut r, path);
        let rows = implied(&mut r, expression);
        assert!(
            rows.contains(&(kind.to_string(), callee.to_string())),
            "{path}: {rows:?}"
        );
        // The callee typing is the planner's row under the implied recipe,
        // beside the kind role or minimized behind it (a calc usage callee
        // reaches `Performances::evaluations` on its own).
        let target = named(&mut r, callee);
        let expected = implied_id(expression, kind, target, &r);
        assert!(
            r.implied_relationships(expression)
                .iter()
                .any(|&row| r.element_id(row) == expected),
            "{path}: no row with the implied id recipe"
        );
        if kind == "FeatureTyping" {
            assert!(
                rows.contains(&(
                    "Subsetting".to_string(),
                    "Performances::evaluations".to_string()
                )),
                "{path}: {rows:?}"
            );
        }
    }
    // The trigger expression's function is the one its kind names.
    let trigger = r
        .elements_of_metaclass("TriggerInvocationExpression")
        .into_iter()
        .find(|&e| !r.is_library_element(e))
        .expect("the accept's trigger expression");
    let rows = implied(&mut r, trigger);
    assert!(
        rows.contains(&(
            "FeatureTyping".to_string(),
            "Triggers::TriggerAt".to_string()
        )),
        "{rows:?}"
    );
    // An unresolved callee plans nothing: the kind role alone (and the
    // result the grammar gives every expression).
    let bad = value_of(&mut r, "Results::P::bad");
    assert_eq!(
        implied(&mut r, bad)
            .into_iter()
            .filter(|(kind, _)| kind != "ReturnParameterMembership")
            .collect::<Vec<_>>(),
        vec![(
            "Subsetting".to_string(),
            "Performances::evaluations".to_string()
        )]
    );
    // The library's own expressions keep their kind roles.
    let library_operator = r
        .elements_of_metaclass("OperatorExpression")
        .into_iter()
        .find(|&e| r.is_library_element(e))
        .expect("a library operator expression");
    assert!(
        implied(&mut r, library_operator)
            .iter()
            .all(|(kind, _)| kind != "FeatureTyping")
    );
}

#[test]
fn type_and_function_certify_through_the_callee_typing() {
    let mut r = model();
    for (path, callee) in [
        ("Results::Double::result", "DataFunctions::'*'"),
        ("Results::P::call", "Results::Double"),
        ("Results::P::lib", "RealFunctions::sqrt"),
        ("Results::P::chained", "ControlFunctions::'.'"),
    ] {
        let expression = value_of(&mut r, path);
        let target = named(&mut r, callee);
        let id = r.element_id(target).to_string();
        let function = r
            .property(expression, "function")
            .unwrap_or_else(|err| panic!("{path}.function: {err}"));
        assert_eq!(id_of(&function), id, "{path}");
        let types = r
            .property(expression, "type")
            .unwrap_or_else(|err| panic!("{path}.type: {err}"));
        assert_eq!(
            types
                .as_array()
                .unwrap()
                .iter()
                .map(id_of)
                .collect::<Vec<_>>(),
            vec![id],
            "{path}"
        );
        let instantiated = r.property(expression, "instantiatedType").unwrap();
        assert_eq!(id_of(&instantiated), id_of(&function), "{path}");
    }
    // A calc usage callee: typed by the usage's definition through the
    // subsetting.
    let via_usage = value_of(&mut r, "Results::P::viaUsage");
    let double = named(&mut r, "Results::Double");
    let types = r.property(via_usage, "type").unwrap();
    assert_eq!(
        types
            .as_array()
            .unwrap()
            .iter()
            .map(id_of)
            .collect::<Vec<_>>(),
        vec![r.element_id(double).to_string()]
    );
    // An unresolved callee: the checked reads refuse, the derived function
    // is none.
    let bad = value_of(&mut r, "Results::P::bad");
    assert!(r.property(bad, "type").is_err());
    assert!(r.property(bad, "function").is_err());
    assert!(matches!(
        r.derived(bad, "function"),
        sysmlv2_parser::json::Derived::Value(sysmlv2_parser::json::DerivedValue::Null)
    ));
}

#[test]
fn arguments_redefine_the_callee_inputs_in_order() {
    // A fresh model: the first read is the checked `argument`, which
    // materializes the rows it certifies through.
    let mut r = model();
    let call = value_of(&mut r, "Results::P::call");
    let x = named(&mut r, "Results::Double::x");
    let arguments = r
        .property(call, "argument")
        .unwrap_or_else(|err| panic!("call.argument: {err}"));
    assert_eq!(arguments.as_array().unwrap().len(), 1);
    let parameter = r.members_via(call, "ParameterMembership")[0];
    assert!(
        implied(&mut r, parameter)
            .contains(&("Redefinition".to_string(), "Results::Double::x".to_string()))
    );
    let report = r.invocation_binding_report(call).arguments.unwrap();
    assert_eq!(report.inputs, vec![x]);
    assert_eq!(report.bindings.len(), 1);
    assert_eq!(report.bindings[0].input, x);
    assert_eq!(report.bindings[0].parameter, parameter);
    // A named argument keeps its written redefinition and gains no
    // positional one.
    let named_call = value_of(&mut r, "Results::P::named");
    let parameter = r.members_via(named_call, "ParameterMembership")[0];
    assert!(implied(&mut r, parameter).is_empty());
    assert_eq!(
        r.property(named_call, "argument")
            .unwrap()
            .as_array()
            .unwrap()
            .len(),
        1
    );
    // A library function's inputs, by position.
    let lib = value_of(&mut r, "Results::P::lib");
    let parameter = r.members_via(lib, "ParameterMembership")[0];
    assert!(implied(&mut r, parameter).contains(&(
        "Redefinition".to_string(),
        "RealFunctions::sqrt::x".to_string()
    )));
    let product = value_of(&mut r, "Results::Double::result");
    let operands = r.members_via(product, "ParameterMembership");
    assert_eq!(operands.len(), 2);
    for (operand, input) in operands.into_iter().zip(["x", "y"]) {
        assert!(
            implied(&mut r, operand).contains(&(
                "Redefinition".to_string(),
                format!("DataFunctions::'*'::{input}")
            )),
            "{input}"
        );
    }
    // An argument pairs with the callee's inputs: an output among the
    // callee's parameters takes no position (KerML
    // `validateInvocationExpressionParameterRedefinition`).
    let shifted = value_of(&mut r, "Results::P::shifted");
    let parameter = r.members_via(shifted, "ParameterMembership")[0];
    let rows = implied(&mut r, parameter);
    assert!(
        rows.contains(&("Redefinition".to_string(), "Results::Shift::v".to_string())),
        "{rows:?}"
    );
    assert!(
        !rows.contains(&(
            "Redefinition".to_string(),
            "Results::Shift::log".to_string()
        )),
        "{rows:?}"
    );
    let v = named(&mut r, "Results::Shift::v");
    let report = r.invocation_binding_report(shifted).arguments.unwrap();
    assert_eq!(report.inputs, vec![v]);
    assert_eq!(report.bindings.len(), 1);
    // An unresolved callee: no redefinition, no arguments.
    let bad = value_of(&mut r, "Results::P::bad");
    let parameter = r.members_via(bad, "ParameterMembership")[0];
    assert!(
        implied(&mut r, parameter)
            .iter()
            .all(|(kind, _)| kind != "Redefinition")
    );
    assert!(r.property(bad, "argument").is_err());
}

#[test]
fn operator_arguments_bind_through_the_static_callee_row_on_both_formats() {
    // `argument` on an arithmetic and on a comparison operator: the
    // bindings follow the planner's typing row, whatever the graph format.
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = model_with(format);
        for (path, function) in [
            ("Results::Double::result", "DataFunctions::'*'"),
            ("Results::P::less", "DataFunctions::'<'"),
            ("Results::P::power", "DataFunctions::'**'"),
        ] {
            let operator = value_of(&mut r, path);
            let arguments = r
                .property(operator, "argument")
                .unwrap_or_else(|err| panic!("{format:?} {path}.argument: {err}"));
            assert_eq!(arguments.as_array().unwrap().len(), 2, "{format:?} {path}");
            let callee = named(&mut r, function);
            let report = r.invocation_binding_report(operator).arguments.unwrap();
            assert_eq!(report.bindings.len(), 2, "{format:?} {path}");
            assert_eq!(report.callee, callee, "{format:?} {path}");
            assert!(r.property(operator, "feature").is_ok(), "{format:?} {path}");
            let instantiated = r.property(operator, "instantiatedType").unwrap();
            assert_eq!(
                instantiated["@id"].as_str().unwrap(),
                r.element_id(callee).to_string(),
                "{format:?} {path}"
            );
        }
    }
}
