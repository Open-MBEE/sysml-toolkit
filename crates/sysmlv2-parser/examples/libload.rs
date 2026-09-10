//! Timing triage: where standard-library loading spends its time.
//!
//! ```sh
//! cargo run --release -p sysmlv2-parser --example libload
//! ```

use std::time::Instant;

fn main() {
    let lib = std::path::Path::new("spec-refs/SysML-v2-Release/sysml.library");
    if !lib.is_dir() {
        eprintln!("library dir not found: {}", lib.display());
        std::process::exit(1);
    }

    let t0 = Instant::now();
    let mut model = sysmlv2_parser::model::Model::new();
    let n = model.load_library_dir(lib).expect("load");
    let t_parse = t0.elapsed();

    let t1 = Instant::now();
    let user = model.add_source("t.sysml", "package Demo { part def P; part p : P; }");
    let _ = user;
    let t_user = t1.elapsed();

    let t2 = Instant::now();
    let _r = sysmlv2_parser::json::ResolvedModel::build(&model);
    let t_build = t2.elapsed();

    println!("library files parsed : {n} in {t_parse:?}");
    println!("user source added    : {t_user:?}");
    println!("build+resolve        : {t_build:?}");
    println!("total                : {:?}", t0.elapsed());
}
