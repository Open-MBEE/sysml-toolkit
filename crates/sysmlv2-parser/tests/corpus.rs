//! Corpus tests: the parser must handle every official SysML v2 release file
//! — `.sysml` (SysML dialect: standard library, training, examples,
//! validation suites) and `.kerml` (KerML dialect: kernel libraries) —
//! without diagnostics, and the compact-JSON emitter must process each parse
//! without panicking.

use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::parser::{Parse, parse_kerml_source, parse_source};

fn corpus_files() -> Vec<PathBuf> {
    let files = sysmlv2_testkit::corpus_files();
    assert!(files.len() > 340, "expected the full corpus checkout");
    files
}

fn parse_file(path: &Path, src: &str) -> Parse {
    if path.extension().and_then(|e| e.to_str()) == Some("kerml") {
        parse_kerml_source(src)
    } else {
        parse_source(src)
    }
}

#[test]
fn corpus_parses_without_diagnostics() {
    let mut failures = Vec::new();
    for path in corpus_files() {
        let src = fs::read_to_string(&path).unwrap();
        let parse = parse_file(&path, &src);
        if !parse.diagnostics.is_empty() {
            failures.push(format!(
                "{}: {} diagnostics, first: {}",
                path.display(),
                parse.diagnostics.len(),
                parse.diagnostics[0].message
            ));
        }
    }
    assert!(
        failures.is_empty(),
        "{} corpus files failed to parse:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

#[cfg(feature = "json")]
#[test]
fn corpus_emits_compact_json() {
    use sysmlv2_parser::json::to_compact_json;
    for path in corpus_files() {
        let src = fs::read_to_string(&path).unwrap();
        let parse = parse_file(&path, &src);
        let value = to_compact_json(&parse.unit);
        let elements = value.as_array().expect("flat element array");
        assert!(!elements.is_empty(), "{}: no elements", path.display());
    }
}
