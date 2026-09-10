//! Triage: print the reason for every corpus constraint the solver
//! leaves Unknown, grouped by reason prefix.
//!
//!     cargo run -p sysmlv2-solve --example unknowns

use std::collections::BTreeMap;
use sysmlv2_model::model::Model;
use sysmlv2_solve::{SolveOutcome, SolverConfig, solve_constraints};

fn main() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let solved = solve_constraints(&model, &SolverConfig::default()).unwrap();
    let mut by_reason: BTreeMap<String, Vec<String>> = BTreeMap::new();
    for s in &solved {
        if let Some(SolveOutcome::Unknown(reason)) = &s.solve {
            by_reason.entry(reason.clone()).or_default().push(format!(
                "{} — {:?}",
                model.units()[s.unit].name,
                s.name
            ));
        }
    }
    for (reason, sites) in &by_reason {
        println!("{} × {}", sites.len(), reason);
        for s in sites {
            println!("    {s}");
        }
    }
}
