//! Dev tool: sample unresolved @refs by category.
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

fn walk(v: &serde_json::Value, out: &mut Vec<String>) {
    match v {
        serde_json::Value::Object(m) => {
            if let Some(r) = m.get("@ref").and_then(|x| x.as_str()) {
                out.push(r.to_string());
            }
            for x in m.values() {
                walk(x, out);
            }
        }
        serde_json::Value::Array(a) => {
            for x in a {
                walk(x, out);
            }
        }
        _ => {}
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
    let v = model_to_compact_json(&model);
    let mut refs = Vec::new();
    walk(&v, &mut refs);
    let chains = refs.iter().filter(|r| r.contains('.')).count();
    let qualified = refs
        .iter()
        .filter(|r| !r.contains('.') && r.contains("::"))
        .count();
    let simple = refs
        .iter()
        .filter(|r| !r.contains('.') && !r.contains("::"))
        .count();
    println!(
        "total {} = chains {} + qualified {} + simple {}",
        refs.len(),
        chains,
        qualified,
        simple
    );
    let mut counts: std::collections::HashMap<&str, usize> = Default::default();
    for r in &refs {
        if !r.contains('.') {
            *counts.entry(r.as_str()).or_default() += 1;
        }
    }
    let mut v: Vec<_> = counts.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    for (name, n) in v.iter().take(15) {
        println!("{n:>5}  {name}");
    }
}
