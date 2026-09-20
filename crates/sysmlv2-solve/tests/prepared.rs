//! Solver entry points must read unit metadata without reconstructing the
//! syntax of a prepared library.
use std::sync::Arc;
use sysmlv2_model::{model::Model, prepared::PreparedLibrary};
use sysmlv2_solve::{PropagateConfig, propagate_constraints};

#[test]
fn propagation_over_a_prepared_library_keeps_library_syntax_unloaded() {
    let mut base = Model::new();
    base.add_library_source(
        "lib.sysml",
        "package Lib { attribute def N; part def T { attribute n : N; assert constraint c { n > 0 } } }",
    );
    // A decoded snapshot starts with no library syntax in memory.
    let bytes = base.prepare_library().unwrap().to_bytes(1).unwrap();
    let prepared = Arc::new(PreparedLibrary::from_bytes(&bytes, 1).unwrap());
    let mut model = Model::new();
    prepared.install(&mut model).unwrap();
    model.add_source(
        "user.sysml",
        "package U { part t : Lib::T { attribute :>> n = 2; } constraint k { t.n < 5 } }",
    );
    assert_eq!(model.loaded_library_unit_count(), 0);
    let propagation = propagate_constraints(&model, &PropagateConfig::default());
    assert!(
        propagation
            .constraints
            .iter()
            .all(|c| !model.is_library_unit(c.unit)),
        "library constraints are never reported"
    );
    assert!(
        !propagation.constraints.is_empty(),
        "the user constraint is analysed"
    );
    assert_eq!(
        model.loaded_library_unit_count(),
        0,
        "solver metadata reads must not materialize library syntax"
    );
}
