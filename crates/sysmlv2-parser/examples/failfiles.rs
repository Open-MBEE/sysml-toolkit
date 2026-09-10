//! Dev tool: print first diagnostics with context for failing corpus files.
use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};
use sysmlv2_parser::span::LineIndex;

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
        .unwrap_or("spec-refs/SysML-v2-Release/sysml/src".into());
    let filter = std::env::args().nth(2);
    let mut files = Vec::new();
    collect(Path::new(&root), &mut files);
    files.sort();
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        let p = if f.extension().and_then(|x| x.to_str()) == Some("kerml") {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        if p.diagnostics.is_empty() {
            continue;
        }
        let idx = LineIndex::new(&src);
        for d in p.diagnostics.iter().take(2) {
            if let Some(flt) = &filter {
                if !d.message.contains(flt.as_str()) {
                    continue;
                }
            }
            let pos = idx.line_col(d.span.start);
            let line = src.lines().nth(pos.line as usize - 1).unwrap_or("");
            println!(
                "{}:{}: {}\n    | {}",
                f.display(),
                pos.line,
                d.message,
                line.trim()
            );
        }
    }
}
