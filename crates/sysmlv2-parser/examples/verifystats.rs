//! Dev tool: corpus-wide constraint verdicts.
use sysmlv2_parser::check::{ConstraintVerdict, check_constraints};
use sysmlv2_parser::model::Model;

fn main() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let checks = check_constraints(&model);
    let (mut sat, mut vio, mut und) = (0, 0, 0);
    for c in &checks {
        match &c.verdict {
            ConstraintVerdict::Satisfied => sat += 1,
            ConstraintVerdict::Violated => {
                vio += 1;
                println!(
                    "VIOLATED: {} — {:?} ({})",
                    model.units()[c.unit].name,
                    c.name,
                    c.element_type
                );
            }
            ConstraintVerdict::Undecided(_) => und += 1,
        }
    }
    println!(
        "{} checks: {sat} satisfied, {vio} violated, {und} undecided",
        checks.len()
    );
}
