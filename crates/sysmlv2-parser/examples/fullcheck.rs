//! Dev tool: produce full-form JSON for corpus files (library-resolved) and
//! validate every element against the published SysML schema.
use serde_json::Value;
use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::full::model_to_full_json;
use sysmlv2_parser::model::Model;

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
    let schema: Value =
        serde_json::from_str(&fs::read_to_string("spec-refs/SysML.schema.json").unwrap()).unwrap();
    let mut validators: std::collections::HashMap<String, jsonschema::Validator> =
        Default::default();

    let mut model = Model::new();
    model.load_library_dir(&root.join("sysml.library")).unwrap();
    let mut files = Vec::new();
    collect(&root.join("sysml/src"), &mut files);
    files.sort();
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let full = model_to_full_json(&model);
    let elements = full.as_array().unwrap();
    let (mut ok, mut bad) = (0usize, 0usize);
    let mut messages: std::collections::HashMap<String, usize> = Default::default();
    for el in elements {
        let t = el["@type"].as_str().unwrap().to_string();
        let validator = validators.entry(t.clone()).or_insert_with(|| {
            let def = &schema["$defs"][&t];
            let mut mini = if def.get("anyOf").is_some() {
                def["anyOf"][0].clone()
            } else {
                def.clone()
            };
            mini["$defs"] = schema["$defs"].clone();
            jsonschema::validator_for(&mini).unwrap()
        });
        let mut any = false;
        for err in validator.iter_errors(el).take(2) {
            any = true;
            let key = format!(
                "{t} @ {}: {}",
                err.instance_path(),
                err.to_string().chars().take(90).collect::<String>()
            );
            *messages.entry(key).or_default() += 1;
        }
        if any { bad += 1 } else { ok += 1 }
    }
    println!("{ok} elements valid, {bad} invalid (of {})", elements.len());
    let mut v: Vec<_> = messages.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (msg, n) in v.iter().take(15) {
        println!("{n:>6}  {msg}");
    }
}
