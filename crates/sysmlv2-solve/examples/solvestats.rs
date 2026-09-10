//! Dev tool: corpus-wide Z3 outcomes for the constraints the evaluator
//! leaves undecided (the solving stage).

use sysmlv2_model::check::ConstraintVerdict;
use sysmlv2_model::model::Model;
use sysmlv2_solve::{SolveOutcome, SolverConfig, solve_constraints, z3_version};

fn main() {
    let cfg = SolverConfig::default();
    if let Err(e) = z3_version(&cfg) {
        eprintln!("{e}");
        std::process::exit(1);
    }
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let solved = solve_constraints(&model, &cfg).unwrap();
    let (mut sat, mut vio, mut und) = (0, 0, 0);
    let (mut valid, mut witness, mut unsat, mut unknown) = (0, 0, 0, 0);
    let mut reasons: std::collections::BTreeMap<String, usize> = Default::default();
    for s in &solved {
        match &s.verdict {
            ConstraintVerdict::Satisfied => sat += 1,
            ConstraintVerdict::Violated => vio += 1,
            ConstraintVerdict::Undecided(_) => und += 1,
        }
        match &s.solve {
            None => {}
            Some(SolveOutcome::Valid) => {
                valid += 1;
                println!(
                    "VALID: {} — {:?} ({})",
                    model.units()[s.unit].name,
                    s.name,
                    s.element_type
                );
            }
            Some(SolveOutcome::Unsatisfiable) => {
                unsat += 1;
                println!(
                    "UNSAT: {} — {:?} ({})",
                    model.units()[s.unit].name,
                    s.name,
                    s.element_type
                );
            }
            Some(SolveOutcome::Satisfiable(w)) => {
                witness += 1;
                let vals: Vec<String> = w.iter().map(|(n, v)| format!("{n} = {v}")).collect();
                println!(
                    "sat: {} — {:?} e.g. {}",
                    model.units()[s.unit].name,
                    s.name,
                    vals.join(", ")
                );
            }
            Some(SolveOutcome::Unknown(m)) => {
                unknown += 1;
                *reasons.entry(m.clone()).or_default() += 1;
            }
        }
    }
    println!(
        "\n{} checks: {sat} satisfied, {vio} violated, {und} undecided",
        solved.len()
    );
    println!(
        "solve over undecided: {valid} valid, {witness} satisfiable, {unsat} unsatisfiable, \
         {unknown} unknown"
    );
    println!("\nunknown reasons:");
    let mut sorted: Vec<_> = reasons.into_iter().collect();
    sorted.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (m, n) in sorted {
        println!("{n:5}  {m}");
    }
}
