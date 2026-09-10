//! Dev tool: emit compact JSON for every corpus file; report panics/failures.
use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::{
    json::to_compact_json,
    parser::{parse_kerml_source, parse_source},
};

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
    let mut files = Vec::new();
    collect(Path::new("spec-refs/SysML-v2-Release"), &mut files);
    files.sort();
    let (mut ok, mut fail, mut elements, mut refs, mut unresolved) = (0, 0, 0usize, 0usize, 0usize);
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        let parse = if f.extension().and_then(|x| x.to_str()) == Some("kerml") {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        let result = std::panic::catch_unwind(|| to_compact_json(&parse.unit));
        match result {
            Ok(v) => {
                ok += 1;
                let arr = v.as_array().unwrap();
                elements += arr.len();
                let text = v.to_string();
                refs += text.matches("\"@id\"").count();
                unresolved += text.matches("\"@ref\"").count();
            }
            Err(_) => {
                fail += 1;
                eprintln!("PANIC: {}", f.display());
            }
        }
    }
    println!(
        "json ok={ok} panic={fail}; {elements} elements, {refs} id-refs, {unresolved} unresolved @refs"
    );
}
