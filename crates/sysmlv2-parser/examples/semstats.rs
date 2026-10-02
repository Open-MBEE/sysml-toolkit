//! Dev tool: corpus-wide semantic-constraint findings.
use sysmlv2_parser::check::validate_semantics;
use sysmlv2_parser::model::Model;

fn main() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(
            sysmlv2_testkit::relative_source_name(&sysmlv2_testkit::corpus_root(), f.as_path()),
            &src,
        );
    }
    let diags = validate_semantics(&model);
    for (u, d) in &diags {
        println!("{} — {}", model.units()[*u].name, d);
    }
    println!("total: {}", diags.len());
}
