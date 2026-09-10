//! The spelled power-product expansion opt-out: with
//! `set_unit_spelling_expansion(false)`, quoted spellings like
//! `'m³⋅s⁻²'` stay opaque bases (the pre-expansion behavior). Lives in
//! its own test binary because the switch is process-wide — flipping it
//! next to concurrently running evaluator tests would race them.

use sysmlv2_parser::eval::{EvalError, Value, set_unit_spelling_expansion};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

fn eval_with(decls: &str, expr: &str) -> Result<Value, EvalError> {
    let mut model = Model::new();
    let unit = model.add_source(
        "t.sysml",
        &format!("package T {{ {decls} attribute result = {expr}; }}"),
    );
    assert!(
        unit.diagnostics.is_empty(),
        "test source must parse cleanly"
    );
    let mut r = ResolvedModel::build(&model);
    let e = r.resolve_qualified("T::result").expect("result resolves");
    r.evaluate(e)
}

#[test]
fn spelling_expansion_disabled_keeps_spellings_opaque() {
    set_unit_spelling_expansion(false);
    let units = "attribute m; attribute s;
                 attribute <'m³⋅s⁻²'> 'metre cubed per second squared';";
    // Opaque base vs. the spelled-out expression: incommensurable.
    assert!(matches!(
        eval_with(units, "1 ['m³⋅s⁻²'] + 1 [m**3/s**2]"),
        Err(EvalError::Type(_))
    ));
    // Same opaque base on both sides still works.
    assert_eq!(
        eval_with(units, "1 ['m³⋅s⁻²'] + 1 ['m³⋅s⁻²']"),
        Ok(Value::Quantity(
            Box::new(Value::Integer(2)),
            match eval_with(units, "1 ['m³⋅s⁻²']") {
                Ok(Value::Quantity(_, u)) => u,
                other => panic!("expected a quantity, got {other:?}"),
            },
        ))
    );
    set_unit_spelling_expansion(true);
}
