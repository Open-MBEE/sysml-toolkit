//! Instantiation and reference expressions as receivers of the checked
//! member lists (#51): an operator, invocation or reference expression whose
//! callee typing and generated result are rows certifies `feature`, `member`,
//! `membership` and `importedMembership` like any type, the parameter
//! features under it through it; a reference expression's referent may be a
//! parameter (its positional targets come from its owner's certificate) or
//! a package-level usage such as a unit. The generated result suppresses
//! the inherited `Evaluation::result`, and a first read answers what a later
//! one does. Without the library roles the result family redefines nothing,
//! and the lists refuse rather than show two results.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

/// The compatibility reader's element references as the checked reader
/// writes them.
fn derived_ids(r: &mut ResolvedModel, e: ElementRef, name: &str) -> serde_json::Value {
    let Derived::Value(value) = r.derived(e, name) else {
        panic!("{name} is not derived");
    };
    let id = |e| serde_json::json!({"@id": r.element_id(e).to_string()});
    match value {
        DerivedValue::Element(e) => id(e),
        DerivedValue::Elements(es) => serde_json::Value::Array(es.iter().map(|&e| id(e)).collect()),
        DerivedValue::Reference(Reference::Element(e)) => id(e),
        DerivedValue::References(refs) => serde_json::Value::Array(
            refs.iter()
                .map(|reference| match reference {
                    Reference::Element(e) => id(*e),
                    other => panic!("{name}: {other:?} leaves the model"),
                })
                .collect(),
        ),
        other => panic!("{name}: {other:?}"),
    }
}

const SOURCE: &str = "package Results {
    calc def Double { in x : ScalarValues::Real; return : ScalarValues::Real = 2 * x; }
    part def P {
        attribute a : ScalarValues::Real = 1.0;
        attribute call : ScalarValues::Real = Double(a);
        attribute unit = SI::kg;
        part q : Q;
        attribute chained : ScalarValues::Real = q.w;
        attribute made : Sig = new Sig(a);
    }
    part def Q { attribute w : ScalarValues::Real; }
    attribute def Sig { attribute level : ScalarValues::Real; }
}";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("receivers.sysml", SOURCE);
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

fn value_of(r: &mut ResolvedModel, path: &str) -> ElementRef {
    let feature = named(r, path);
    r.members_via(feature, "FeatureValue")[0]
}

fn ids(r: &mut ResolvedModel, e: ElementRef, property: &str) -> Vec<String> {
    let what = r.element_type(e).to_string();
    let value = r
        .property(e, property)
        .unwrap_or_else(|err| panic!("{what}.{property}: {err}"));
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|v| v["@id"].as_str().unwrap().to_string())
        .collect()
}

#[test]
fn expression_receivers_certify_the_member_lists() {
    let mut r = model();
    let call = value_of(&mut r, "Results::P::call");
    let product = value_of(&mut r, "Results::Double::result");
    let argument = r.members_via(call, "ParameterMembership")[0];
    let reference = r.members_via(argument, "FeatureValue")[0];
    assert_eq!(r.element_type(reference), "FeatureReferenceExpression");
    // The operator's operands: a literal and a reference to Double's
    // parameter `x` (a positional referent).
    let operands = r.members_via(product, "ParameterMembership");
    let to_parameter = r.members_via(operands[1], "FeatureValue")[0];
    assert_eq!(r.element_type(to_parameter), "FeatureReferenceExpression");
    // A reference to a package-level usage (a unit).
    let to_unit = value_of(&mut r, "Results::P::unit");
    assert_eq!(r.element_type(to_unit), "FeatureReferenceExpression");
    for e in [
        call,
        product,
        argument,
        operands[0],
        operands[1],
        reference,
        to_parameter,
        to_unit,
    ] {
        for property in ["feature", "member", "membership", "importedMembership"] {
            let what = r.element_type(e).to_string();
            assert!(
                r.property(e, property).is_ok(),
                "{what}.{property}: {:?}",
                r.property(e, property).err()
            );
        }
    }
    // The generated result is the expression's one result: it suppresses
    // the inherited Evaluation::result and the callee's.
    let evaluation_result = named(&mut r, "Performances::Evaluation::result");
    let double_result = named(&mut r, "Results::Double::result");
    let generated = r.property(call, "result").unwrap()["@id"]
        .as_str()
        .unwrap()
        .to_string();
    let features = ids(&mut r, call, "feature");
    assert!(features.contains(&generated));
    assert!(!features.contains(&r.element_id(evaluation_result).to_string()));
    assert!(!features.contains(&r.element_id(double_result).to_string()));
    // The callee's input is inherited by the invocation and redefined by
    // its argument, which the list shows in its place.
    let x = named(&mut r, "Results::Double::x");
    assert!(!features.contains(&r.element_id(x).to_string()));
    assert!(features.contains(&r.element_id(argument).to_string()));
}

#[test]
fn a_first_read_answers_what_a_later_one_does() {
    let mut fresh = model();
    let call = value_of(&mut fresh, "Results::P::call");
    let first = ids(&mut fresh, call, "feature");
    let mut warmed = model();
    let call = value_of(&mut warmed, "Results::P::call");
    warmed.implied_relationships(call);
    let later = ids(&mut warmed, call, "feature");
    assert_eq!(first, later);
}

#[test]
fn lists_refuse_where_the_result_family_redefines_nothing() {
    // No library: the generated result has no Evaluation::result to
    // redefine, so a list over the expression would show an unsuppressed
    // inherited result beside it; the read refuses instead.
    let mut model = Model::new();
    let unit = model.add_source(
        "bare.kerml",
        "function F {in p; return r;} feature n; feature x=F(n);",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let call = value_of(&mut r, "x");
    assert_eq!(r.element_type(call), "InvocationExpression");
    assert!(r.property(call, "feature").is_err());
    assert!(r.property(call, "result").is_ok());
}

/// A feature chain expression's `argument` is its one source operand, bound
/// through the `'.'` function's static callee row like an operator's
/// (public mirror issue #20): the checked read and the compatibility read
/// name the same reference expression.
#[test]
fn a_chain_expressions_argument_binds_through_the_dot_function() {
    let mut r = model();
    let chain = value_of(&mut r, "Results::P::chained");
    assert_eq!(r.element_type(chain), "FeatureChainExpression");
    let checked = r.property(chain, "argument").unwrap();
    let compatibility = derived_ids(&mut r, chain, "argument");
    assert_eq!(checked, compatibility);
    let arguments = checked.as_array().unwrap();
    assert_eq!(arguments.len(), 1, "{checked}");
    let argument = r
        .element_by_id(arguments[0]["@id"].as_str().unwrap())
        .unwrap();
    assert_eq!(r.element_type(argument), "FeatureReferenceExpression");
}

/// A constructor expression's `argument` on the default graph format is
/// its owned `in` parameters' feature values (public mirror issue #20):
/// the checked read and the compatibility read name the same reference
/// expression, and the constructor's `instantiatedType` is its definition.
#[test]
fn a_constructor_expressions_arguments_are_its_parameters_values() {
    let mut r = model();
    let constructor = value_of(&mut r, "Results::P::made");
    assert_eq!(r.element_type(constructor), "ConstructorExpression");
    let checked = r.property(constructor, "argument").unwrap();
    assert_eq!(checked, derived_ids(&mut r, constructor, "argument"));
    let arguments = checked.as_array().unwrap();
    assert_eq!(arguments.len(), 1, "{checked}");
    let argument = r
        .element_by_id(arguments[0]["@id"].as_str().unwrap())
        .unwrap();
    assert_eq!(r.element_type(argument), "FeatureReferenceExpression");
    let sig = named(&mut r, "Results::Sig");
    assert_eq!(
        r.property(constructor, "instantiatedType").unwrap(),
        serde_json::json!({"@id": r.element_id(sig).to_string()})
    );
}
