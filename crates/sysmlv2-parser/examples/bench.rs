//! Dev tool: pipeline throughput over the corpus (performance record).
//!
//! Times each stage over all 345 corpus files (bytes are summed once):
//! parse, compact JSON emission, full JSON, print, format, lift.
//! Run with `cargo run --release --example bench`.

use std::fs;
use std::path::{Path, PathBuf};
use std::time::Instant;
use sysmlv2_parser::ast::Dialect;
use sysmlv2_parser::parser::{Parse, parse_kerml_source, parse_source};

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
    let mut files = Vec::new();
    collect(root, &mut files);
    files.sort();
    let sources: Vec<(Dialect, String)> = files
        .iter()
        .map(|p| {
            let d = if p.extension().and_then(|e| e.to_str()) == Some("kerml") {
                Dialect::Kerml
            } else {
                Dialect::Sysml
            };
            (d, fs::read_to_string(p).unwrap())
        })
        .collect();
    let bytes: usize = sources.iter().map(|(_, s)| s.len()).sum();
    let mib = bytes as f64 / (1024.0 * 1024.0);
    println!(
        "{} files, {:.2} MiB — timings are best of 3 passes\n",
        sources.len(),
        mib
    );

    let parse_all = |sources: &[(Dialect, String)]| -> Vec<Parse> {
        sources
            .iter()
            .map(|(d, s)| match d {
                Dialect::Kerml => parse_kerml_source(s),
                Dialect::Sysml => parse_source(s),
            })
            .collect()
    };

    let time = |label: &str, f: &mut dyn FnMut()| {
        let mut best = f64::MAX;
        for _ in 0..3 {
            let t = Instant::now();
            f();
            best = best.min(t.elapsed().as_secs_f64());
        }
        println!(
            "{label:<22} {:>8.1} ms   {:>7.1} MiB/s",
            best * 1e3,
            mib / best
        );
    };

    time("parse", &mut || {
        let _ = parse_all(&sources);
    });

    let parses = parse_all(&sources);

    time("emit compact JSON", &mut || {
        for p in &parses {
            let _ = sysmlv2_parser::json::to_compact_json(&p.unit);
        }
    });
    time("emit full JSON", &mut || {
        for p in &parses {
            let _ = sysmlv2_parser::full::to_full_json(&p.unit);
        }
    });
    time("print", &mut || {
        for p in &parses {
            let _ = sysmlv2_parser::print::print_source(&p.unit);
        }
    });
    time("format", &mut || {
        for (d, s) in &sources {
            let _ = sysmlv2_parser::print::format_source(s, *d);
        }
    });

    let jsons: Vec<serde_json::Value> = parses
        .iter()
        .map(|p| sysmlv2_parser::json::to_compact_json(&p.unit))
        .collect();
    time("lift (JSON → AST)", &mut || {
        for j in &jsons {
            let _ = sysmlv2_parser::lift::from_compact_json(j);
        }
    });

    // The multi-file model resolution path (library + user files together).
    let mut model_time = f64::MAX;
    for _ in 0..3 {
        let t = Instant::now();
        let mut model = sysmlv2_parser::model::Model::new();
        model.load_library_dir(&root.join("sysml.library")).unwrap();
        let mut user = Vec::new();
        collect(&root.join("sysml/src"), &mut user);
        user.sort();
        for f in &user {
            let src = fs::read_to_string(f).unwrap();
            model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
        }
        let _ = sysmlv2_parser::json::model_to_compact_json(&model);
        model_time = model_time.min(t.elapsed().as_secs_f64());
    }
    println!(
        "{:<22} {:>8.1} ms   (94 lib + 251 user files, incl. I/O + resolution)",
        "full model emit",
        model_time * 1e3
    );
}
