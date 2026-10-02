//! Approximate definitions cannot become definitive satisfaction through contraction.
use std::sync::Arc;
use sysmlv2_model::{
    json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};
use sysmlv2_solve::{
    PropagateOutcome, SolveOutcome, SolverConfig, propagate_constraints_with,
    solve_constraints_with, verify_constraints_with, z3_version,
};
fn models(source: &str) -> Vec<Model> {
    let lib = "package ScalarValues { datatype Integer; datatype Natural specializes Integer; }";
    let mut base = Model::new();
    base.add_library_source("lib.kerml", lib);
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(43).unwrap(), 43).unwrap());
    (0..4)
        .map(|mode| {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("lib.kerml", lib);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            for pkg in ["A", "B"] {
                m.add_source(
                    format!("{pkg}.sysml"),
                    &format!("package {pkg} {{ attribute x[1]:ScalarValues::Integer; {source} }}"),
                );
            }
            assert!(!m.has_errors());
            m
        })
        .collect()
}

fn is_open(outcome: &Option<PropagateOutcome>) -> bool {
    matches!(
        outcome,
        Some(PropagateOutcome::Undecided | PropagateOutcome::Unsupported(_))
    )
}
fn source(constraints: &str) -> String {
    format!("attribute y[1]:ScalarValues::Integer=(x,0)#(1); {constraints}")
}
fn assert_no_hydration(mode: usize, model: &Model, loaded: usize) {
    assert_eq!(model.loaded_library_unit_count(), loaded);
    if mode == 3 {
        assert_eq!(loaded, 0);
    }
}
fn assert_approximation_stays_open(constraints: &str, expected_ranges: &[(&str, &str)]) {
    let cfg = SolverConfig::default();
    let native = z3_version(&cfg).is_ok();
    for (mode, model) in models(&source(constraints)).into_iter().enumerate() {
        let loaded = model.loaded_library_unit_count();
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            let propagation = propagate_constraints_with(&mut r, &model, &Default::default());
            assert_eq!(propagation.constraints.len(), 2);
            assert!(
                propagation
                    .constraints
                    .iter()
                    .all(|c| is_open(&c.propagate)),
                "mode={mode}: {propagation:?}"
            );
            for &(feature, expected) in expected_ranges {
                let ranges: Vec<_> = propagation
                    .ranges
                    .iter()
                    .filter(|r| r.feature == feature)
                    .collect();
                assert_eq!(ranges.len(), 2);
                assert!(
                    ranges.iter().all(|r| r.range == expected),
                    "{propagation:?}"
                );
            }
            let report = verify_constraints_with(
                &mut r,
                &model,
                native.then_some(&cfg),
                &Default::default(),
            )
            .unwrap();
            assert_eq!(report.constraints.len(), 2);
            for c in report.constraints {
                assert!(is_open(&c.propagate), "mode={mode}: {c:?}");
                if native {
                    assert!(
                        matches!(c.solve, Some(SolveOutcome::Unknown(_))),
                        "verification must reach native fallback: {c:?}"
                    );
                } else {
                    assert_eq!(c.solve, None);
                }
            }
            if native {
                for c in solve_constraints_with(&mut r, &model, &cfg).unwrap() {
                    assert!(
                        matches!(c.solve, Some(SolveOutcome::Unknown(_))),
                        "mode={mode}: {c:?}"
                    );
                }
            }
        }
        assert_no_hydration(mode, &model, loaded);
    }
}

#[test]
fn approximate_definition_cannot_prove_its_own_asserted_value() {
    assert_approximation_stays_open("assert constraint c {y==1}", &[("y", "[1, 1]")]);
}

#[test]
fn dropped_scalar_index_identity_cannot_manufacture_a_satisfied_constraint() {
    // The unsupported symbolic index means y=x. This assertion has no model
    // witness, even though independently invented x/y variables satisfy it.
    assert_approximation_stays_open(
        "assert constraint c {y==1 & x==0}",
        &[("y", "[1, 1]"), ("x", "[0, 0]")],
    );
}

#[test]
fn approximate_facts_cannot_settle_an_exact_shared_variable_sibling() {
    let cfg = SolverConfig::default();
    let native = z3_version(&cfg).is_ok();
    for reverse in [false, true] {
        let approximate = "assert constraint approximation {y==1 & x==0}";
        let exact = "assert constraint sibling {x==0}";
        let constraints = if reverse {
            format!("{exact} {approximate}")
        } else {
            format!("{approximate} {exact}")
        };
        for (mode, model) in models(&source(&constraints)).into_iter().enumerate() {
            let loaded = model.loaded_library_unit_count();
            let mut r = ResolvedModel::build(&model);
            for _ in 0..2 {
                let p = propagate_constraints_with(&mut r, &model, &Default::default());
                assert_eq!(p.constraints.len(), 4);
                assert!(
                    p.constraints.iter().all(|c| is_open(&c.propagate)),
                    "mode={mode} reverse={reverse}: {p:?}"
                );
                let report = verify_constraints_with(
                    &mut r,
                    &model,
                    native.then_some(&cfg),
                    &Default::default(),
                )
                .unwrap();
                for c in report.constraints {
                    assert!(is_open(&c.propagate), "{c:?}");
                    if native {
                        if c.name.as_deref() == Some("sibling") {
                            assert!(
                                matches!(c.solve, Some(SolveOutcome::Satisfiable(_))),
                                "{c:?}"
                            );
                        } else {
                            assert!(matches!(c.solve, Some(SolveOutcome::Unknown(_))), "{c:?}");
                        }
                    }
                }
            }
            assert_no_hydration(mode, &model, loaded);
        }
    }
}

#[test]
fn contradictory_approximate_bounds_still_prove_unsatisfiability() {
    let cfg = SolverConfig::default();
    let native = z3_version(&cfg).is_ok();
    for (mode, model) in models(&source("assert constraint c {y==1 & y==2}"))
        .into_iter()
        .enumerate()
    {
        let loaded = model.loaded_library_unit_count();
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            let p = propagate_constraints_with(&mut r, &model, &Default::default());
            assert_eq!(p.constraints.len(), 2);
            assert!(
                p.constraints
                    .iter()
                    .all(|c| c.propagate == Some(PropagateOutcome::Unsatisfiable)),
                "{p:?}"
            );
            let report = verify_constraints_with(
                &mut r,
                &model,
                native.then_some(&cfg),
                &Default::default(),
            )
            .unwrap();
            for c in report.constraints {
                assert_eq!(c.propagate, Some(PropagateOutcome::Unsatisfiable));
                assert_eq!(
                    c.solve, None,
                    "sound refutation should avoid an unnecessary native call"
                );
            }
            if native {
                for c in solve_constraints_with(&mut r, &model, &cfg).unwrap() {
                    assert_eq!(c.solve, Some(SolveOutcome::Unsatisfiable));
                }
            }
        }
        assert_no_hydration(mode, &model, loaded);
    }
}

#[test]
fn native_universal_proof_remains_valid_for_approximate_definitions() {
    let cfg = SolverConfig::default();
    let native = z3_version(&cfg).is_ok();
    for (mode, model) in models(&source("assert constraint c {y==y}"))
        .into_iter()
        .enumerate()
    {
        let loaded = model.loaded_library_unit_count();
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            let report = verify_constraints_with(
                &mut r,
                &model,
                native.then_some(&cfg),
                &Default::default(),
            )
            .unwrap();
            for c in report.constraints {
                if native && c.propagate != Some(PropagateOutcome::Satisfied) {
                    assert_eq!(c.solve, Some(SolveOutcome::Valid), "{c:?}");
                }
            }
            if native {
                for c in solve_constraints_with(&mut r, &model, &cfg).unwrap() {
                    assert_eq!(c.solve, Some(SolveOutcome::Valid));
                }
            }
        }
        assert_no_hydration(mode, &model, loaded);
    }
}

#[test]
fn declaration_only_proofs_survive_unrelated_approximations() {
    let cfg = SolverConfig::default();
    let native = z3_version(&cfg).is_ok();
    let constraints = "attribute n[1]:ScalarValues::Natural; assert constraint approximation {y==1} assert constraint baseline {n>=0}";
    for (mode, model) in models(&source(constraints)).into_iter().enumerate() {
        let loaded = model.loaded_library_unit_count();
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            let report = verify_constraints_with(
                &mut r,
                &model,
                native.then_some(&cfg),
                &Default::default(),
            )
            .unwrap();
            assert_eq!(report.constraints.len(), 4);
            for c in report.constraints {
                if c.name.as_deref() == Some("baseline") {
                    assert_eq!(c.propagate, Some(PropagateOutcome::Satisfied), "{c:?}");
                    assert_eq!(c.solve, None);
                } else {
                    assert!(is_open(&c.propagate), "{c:?}");
                    if native {
                        assert!(matches!(c.solve, Some(SolveOutcome::Unknown(_))), "{c:?}");
                    }
                }
            }
        }
        assert_no_hydration(mode, &model, loaded);
    }
}

#[test]
fn negated_assertion_cannot_certify_an_approximated_value() {
    assert_approximation_stays_open("assert not constraint c {y!=1}", &[("y", "[1, 1]")]);
}

#[test]
fn partial_conjunctions_with_approximate_terms_can_refute_but_not_prove() {
    let cfg = SolverConfig::default();
    let native = z3_version(&cfg).is_ok();
    for contradiction in [false, true] {
        let expression = if contradiction {
            "y==1 & y==2 & Missing()"
        } else {
            "y==1 & Missing()"
        };
        let declaration = source(&format!("assert constraint c {{{expression}}}"));
        for (mode, model) in models(&declaration).into_iter().enumerate() {
            let loaded = model.loaded_library_unit_count();
            let mut r = ResolvedModel::build(&model);
            for _ in 0..2 {
                let report = verify_constraints_with(
                    &mut r,
                    &model,
                    native.then_some(&cfg),
                    &Default::default(),
                )
                .unwrap();
                assert_eq!(report.constraints.len(), 2);
                for c in report.constraints {
                    if contradiction {
                        assert_eq!(c.propagate, Some(PropagateOutcome::Unsatisfiable), "{c:?}");
                        assert_eq!(c.solve, None);
                    } else {
                        assert!(
                            matches!(c.propagate, Some(PropagateOutcome::Unsupported(_))),
                            "{c:?}"
                        );
                        if native {
                            assert!(matches!(c.solve, Some(SolveOutcome::Unknown(_))), "{c:?}");
                        }
                    }
                }
            }
            assert_no_hydration(mode, &model, loaded);
        }
    }
}
