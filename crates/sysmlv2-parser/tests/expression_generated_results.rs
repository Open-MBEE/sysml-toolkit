//! The result parameter of an operator, invocation, trigger or chain
//! expression (KerML `EmptyResultMember`), generated like a feature
//! reference's: an implied ReturnParameterMembership owning an `out`
//! Feature, appended after every written row; the result redefines the
//! result of each direct supertype that is a Function or Expression (KerML
//! `checkFeatureResultRedefinition`: the callee's and, through
//! `Performances::evaluations`, `Evaluation::result`); a chain's result
//! subsets the chain's target (`checkFeatureChainExpressionResultSpecialization`).
//! `Expression::result` answers derived and certified on all of them
//! (#53, #54).

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, Derived, DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};
use uuid::Uuid;

const SOURCE: &str = "package Results {
    calc def Double { in x : ScalarValues::Real; return : ScalarValues::Real = 2 * x; }
    calc double : Double;
    part def P {
        attribute a : ScalarValues::Real = 1.0;
        attribute call : ScalarValues::Real = Double(a);
        attribute viaUsage : ScalarValues::Real = double(a);
        attribute bad : ScalarValues::Real = Missing(a);
        attribute cast : ScalarValues::Real = a as ScalarValues::Real;
        part q : P;
        attribute chained : ScalarValues::Real = q.a;
        attribute deep : ScalarValues::Real = q.q.a;
    }
    action def Listen { accept sig : ScalarValues::Real at 3; }
}";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("results.sysml", SOURCE);
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

fn derived_result(r: &mut ResolvedModel, e: ElementRef) -> Option<ElementRef> {
    match r.derived(e, "result") {
        Derived::Value(DerivedValue::Element(result)) => Some(result),
        _ => None,
    }
}

fn recipe(key: String) -> Uuid {
    Uuid::new_v5(&Uuid::NAMESPACE_OID, key.as_bytes())
}

#[test]
fn results_are_generated_with_the_reference_recipe_and_redefine_the_callees_results() {
    let mut r = model();
    for (path, callee_result) in [
        (
            "Results::Double::result",
            Some("DataFunctions::'*'::result"),
        ),
        ("Results::P::call", Some("Results::Double::result")),
        ("Results::P::bad", None),
    ] {
        let expression = value_of(&mut r, path);
        let result = derived_result(&mut r, expression)
            .unwrap_or_else(|| panic!("{path}: no derived result"));
        assert_eq!(r.element_type(result), "Feature", "{path}");
        assert_eq!(
            r.element_id(result),
            recipe(format!("{}/implied/ownedResult", r.element_id(expression))),
            "{path}"
        );
        let membership = r
            .implied_relationships(expression)
            .into_iter()
            .find(|&row| r.element_type(row) == "ReturnParameterMembership")
            .unwrap_or_else(|| panic!("{path}: no generated result membership"));
        assert_eq!(
            r.relationship_ends(membership).1,
            vec![Reference::Element(result)],
            "{path}"
        );
        assert_eq!(
            r.element_id(membership),
            recipe(format!(
                "{}/implied/returnMembership",
                r.element_id(expression)
            )),
            "{path}"
        );
        let rows = implied(&mut r, result);
        assert!(
            rows.contains(&(
                "Redefinition".to_string(),
                "Performances::Evaluation::result".to_string()
            )),
            "{path}: {rows:?}"
        );
        match callee_result {
            Some(callee_result) => {
                assert!(
                    rows.contains(&("Redefinition".to_string(), callee_result.to_string())),
                    "{path}: {rows:?}"
                );
                let target = named(&mut r, callee_result);
                let expected = recipe(format!(
                    "{}/implied/Redefinition/{}",
                    r.element_id(result),
                    r.element_id(target)
                ));
                assert!(
                    r.implied_relationships(result)
                        .iter()
                        .any(|&row| r.element_id(row) == expected),
                    "{path}: no redefinition with the implied id recipe"
                );
            }
            None => assert_eq!(
                rows.iter()
                    .filter(|(kind, _)| kind == "Redefinition")
                    .count(),
                1,
                "{path}: {rows:?}"
            ),
        }
        // The checked read answers the same feature.
        let certified = r
            .property(expression, "result")
            .unwrap_or_else(|err| panic!("{path}.result: {err}"));
        assert_eq!(
            certified["@id"].as_str().unwrap(),
            r.element_id(result).to_string(),
            "{path}"
        );
        let owned = r.property(expression, "ownedRelationship").unwrap();
        assert!(
            owned
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v["@id"].as_str() == Some(&r.element_id(membership).to_string())),
            "{path}"
        );
    }
    // A calc usage callee: its effective result, inherited from the
    // definition, is the only direct one once `evaluations` is minimized
    // behind the usage.
    let via_usage = value_of(&mut r, "Results::P::viaUsage");
    let result = derived_result(&mut r, via_usage).unwrap();
    assert_eq!(
        implied(&mut r, result)
            .into_iter()
            .filter(|(kind, _)| kind == "Redefinition")
            .map(|(_, name)| name)
            .collect::<Vec<_>>(),
        vec!["Results::Double::result".to_string()]
    );
    // The trigger's result redefines the trigger function's.
    let trigger = r
        .elements_of_metaclass("TriggerInvocationExpression")
        .into_iter()
        .find(|&e| !r.is_library_element(e))
        .expect("the accept's trigger expression");
    let result = derived_result(&mut r, trigger).unwrap();
    let rows = implied(&mut r, result);
    assert!(
        rows.contains(&(
            "Redefinition".to_string(),
            "Triggers::TriggerAt::timeSignal".to_string()
        )),
        "{rows:?}"
    );
}

#[test]
fn chain_results_subset_the_chains_target() {
    let mut r = model();
    for path in ["Results::P::chained", "Results::P::deep"] {
        let chain = value_of(&mut r, path);
        assert_eq!(r.element_type(chain), "FeatureChainExpression", "{path}");
        let result = derived_result(&mut r, chain).unwrap_or_else(|| panic!("{path}"));
        let rows = implied(&mut r, result);
        assert!(
            rows.contains(&("Subsetting".to_string(), "Results::P::a".to_string())),
            "{path}: {rows:?}"
        );
        assert!(
            rows.contains(&(
                "Redefinition".to_string(),
                "Performances::Evaluation::result".to_string()
            )),
            "{path}: {rows:?}"
        );
        let a = named(&mut r, "Results::P::a");
        let expected = recipe(format!(
            "{}/implied/Subsetting/{}",
            r.element_id(result),
            r.element_id(a)
        ));
        assert!(
            r.implied_relationships(result)
                .iter()
                .any(|&row| r.element_id(row) == expected),
            "{path}"
        );
        assert!(r.property(chain, "result").is_ok(), "{path}");
    }
}

#[test]
fn written_and_library_results_are_left_alone() {
    let mut r = model();
    // A cast writes its result: no second one, and the checked read
    // answers the written one.
    let cast = value_of(&mut r, "Results::P::cast");
    assert_eq!(r.element_type(cast), "OperatorExpression");
    assert!(
        implied(&mut r, cast)
            .iter()
            .all(|(kind, _)| kind != "ReturnParameterMembership")
    );
    let written = r
        .owned_relationships(cast)
        .into_iter()
        .find(|&m| r.element_type(m) == "ReturnParameterMembership")
        .expect("the cast's written result membership");
    assert!(!r.is_implied(written));
    let result = derived_result(&mut r, cast).unwrap();
    assert_eq!(
        r.relationship_ends(written).1,
        vec![Reference::Element(result)]
    );
    let certified = r.property(cast, "result").unwrap();
    assert_eq!(
        certified["@id"].as_str().unwrap(),
        r.element_id(result).to_string()
    );
    // The library's own expressions keep what they have.
    let library_operator = r
        .elements_of_metaclass("OperatorExpression")
        .into_iter()
        .find(|&e| r.is_library_element(e))
        .expect("a library operator expression");
    assert!(
        implied(&mut r, library_operator)
            .iter()
            .all(|(kind, _)| kind != "ReturnParameterMembership")
    );
}
