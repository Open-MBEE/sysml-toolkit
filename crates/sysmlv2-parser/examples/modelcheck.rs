//! Dev tool: emit all non-library corpus files against the vendored
//! standard library and count unresolved references.
use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::{json::model_to_compact_json, model::Model};

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
    let libs = model.load_library_dir(&root.join("sysml.library")).unwrap();
    let mut files = Vec::new();
    collect(&root.join("sysml/src"), &mut files);
    files.sort();
    let n = files.len();
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        let name = f.file_name().unwrap().to_string_lossy().into_owned();
        model.add_source(name, &src);
    }
    let v = model_to_compact_json(&model);
    let elements = v.as_array().unwrap().len();
    let text = v.to_string();
    let ids = text.matches("\"@id\"").count();
    let unresolved = text.matches("\"@ref\"").count();
    println!(
        "library units: {libs}; user files: {n}; elements: {elements}; id-refs: {ids}; unresolved @refs: {unresolved}"
    );
}
