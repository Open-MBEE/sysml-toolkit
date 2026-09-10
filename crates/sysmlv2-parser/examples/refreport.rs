//! Dev tool: corpus-wide referential-check report (non-library units).
use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::{check::validate_model, model::Model};

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(entries) = fs::read_dir(dir) {
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                collect(&p, out);
            } else if matches!(
                p.extension().and_then(|x| x.to_str()),
                Some("sysml" | "kerml")
            ) {
                out.push(p);
            }
        }
    }
}

fn main() {
    let root = Path::new("spec-refs/SysML-v2-Release");
    let mut model = Model::new();
    model.load_library_dir(&root.join("sysml.library")).unwrap();
    let mut files = Vec::new();
    collect(&root.join("sysml/src"), &mut files);
    files.sort();
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let diags = validate_model(&model);
    let mut unresolved = 0;
    let mut aliases = 0;
    let mut cycles = 0;
    for (unit, d) in &diags {
        if d.message.starts_with("unresolved") {
            unresolved += 1;
        } else if d.message.starts_with("alias") {
            aliases += 1;
        } else {
            cycles += 1;
            if cycles <= 8 {
                println!("cycle: {} — {}", model.units()[*unit].name, d.message);
            }
        }
        if d.message.starts_with("alias") && aliases <= 5 {
            println!("alias: {} — {}", model.units()[*unit].name, d.message);
        }
    }
    println!(
        "total: {} unresolved, {} aliases, {} cycles",
        unresolved, aliases, cycles
    );
}
