//! Dev tool: histogram of first-diagnostic messages across the corpus.
use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};

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
    let root = std::env::args()
        .nth(1)
        .unwrap_or_else(|| "spec-refs/SysML-v2-Release".into());
    let mut files = Vec::new();
    collect(Path::new(&root), &mut files);
    files.sort();
    let mut counts: std::collections::HashMap<String, usize> = Default::default();
    let (mut clean, mut total) = (0, 0);
    for f in &files {
        total += 1;
        let src = fs::read_to_string(f).unwrap();
        let p = if f.extension().and_then(|x| x.to_str()) == Some("kerml") {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        if p.diagnostics.is_empty() {
            clean += 1;
        } else {
            for d in p.diagnostics.iter().take(3) {
                *counts.entry(d.message.clone()).or_default() += 1;
            }
        }
    }
    let mut v: Vec<_> = counts.into_iter().collect();
    v.sort_by_key(|(_, n)| std::cmp::Reverse(*n));
    println!("{clean}/{total} clean");
    for (msg, n) in v.iter().take(30) {
        println!("{n:>5}  {msg}");
    }
}
