//! Emit every view for every non-library corpus file into a directory
//! (one `.puml` per file and view), for bulk validation with a real
//! PlantUML build:
//!
//! ```console
//! $ cargo run -p sysmlv2-viz --example vizsweep -- /tmp/puml
//! $ java -jar plantuml.jar -checkonly /tmp/puml/*.puml
//! ```
//!
//! Empty diagrams (a view with nothing to show for that file) are
//! skipped — PlantUML accepts them, but they would dilute the count.

use sysmlv2_model::json::ResolvedModel;
use sysmlv2_model::model::Model;
use sysmlv2_viz::{View, VizOptions, plantuml};

const VIEWS: &[(View, &str)] = &[
    (View::Tree, "tree"),
    (View::Interconnection, "ic"),
    (View::State, "state"),
    (View::Action, "action"),
    (View::Sequence, "seq"),
    (View::Case, "case"),
    (View::Mixed, "mixed"),
];

fn main() {
    let out_dir = std::env::args().nth(1).expect("usage: vizsweep <out-dir>");
    std::fs::create_dir_all(&out_dir).expect("out dir");
    let mut emitted = 0usize;
    let mut empty = 0usize;
    let mut skipped = 0usize;
    for path in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&path).expect("corpus file reads");
        let mut model = Model::new();
        let unit = model.add_source(path.display().to_string(), &src);
        if !unit.diagnostics.is_empty() {
            skipped += 1;
            continue;
        }
        let mut r = ResolvedModel::build(&model);
        let stem: String = path
            .display()
            .to_string()
            .chars()
            .map(|c| if c.is_alphanumeric() { c } else { '_' })
            .collect();
        for (view, suffix) in VIEWS {
            let opts = VizOptions::default().with_view(*view);
            let out = plantuml(&mut r, None, &opts);
            if out == "@startuml\n@enduml\n" {
                empty += 1;
                continue;
            }
            std::fs::write(format!("{out_dir}/{stem}.{suffix}.puml"), out).expect("write");
            emitted += 1;
        }
    }
    println!("emitted {emitted} diagrams ({empty} empty views, {skipped} files skipped on parse)");
}
