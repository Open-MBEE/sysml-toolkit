//! Solving gate over the Airbus Apollo 11 external validation model.
//! Skips without the submodule or a `z3` binary; the
//! outcome tuple is a ratchet — `valid`/`unsatisfiable` must stay 0 on
//! the conforming scaffold, `satisfiable` should only grow.

use sysmlv2_model::model::Model;
use sysmlv2_solve::{SolveOutcome, SolverConfig, solve_constraints, z3_version};

#[test]
fn apollo_solve_ratchet() {
    let cfg = SolverConfig::default();
    if z3_version(&cfg).is_err() {
        eprintln!("skipping apollo_solve_ratchet: no z3 on PATH");
        return;
    }
    let Some(files) = sysmlv2_testkit::apollo_files() else {
        eprintln!("skipping apollo_solve_ratchet: submodule not initialized");
        return;
    };
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in &files {
        let src = std::fs::read_to_string(f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let solved = solve_constraints(&model, &cfg).unwrap();
    let (mut valid, mut sat, mut unsat, mut unknown) = (0, 0, 0, 0);
    for s in &solved {
        match &s.solve {
            None => {}
            Some(SolveOutcome::Valid) => valid += 1,
            Some(SolveOutcome::Satisfiable(_)) => sat += 1,
            Some(SolveOutcome::Unsatisfiable) => {
                unsat += 1;
                eprintln!(
                    "UNSAT: {} — {:?} ({})",
                    model.units()[s.unit].name,
                    s.name,
                    s.element_type
                );
            }
            Some(SolveOutcome::Unknown(_)) => unknown += 1,
            // A conclusion this count does not know would silently skew
            // the ratchet.
            Some(other) => panic!("unhandled solve conclusion: {other:?}"),
        }
    }
    assert_eq!(
        (valid, sat, unsat, unknown),
        (0, 56, 0, 2),
        "apollo solve ratchet moved — unsatisfiable/valid must stay 0; \
         satisfiable should only grow via translator improvements"
    );
}
