//! Parse a `.sysml` / `.kerml` file and print its compact JSON representation.
//!
//! Usage:
//!   cargo run --example to_json -- <file> [--lib <library-dir>]
//!
//! With `--lib`, references into the standard library resolve to the
//! normative KerML 9.1 element IDs (e.g. point it at the vendored
//! `spec-refs/SysML-v2-Release/sysml.library`).

use std::path::Path;
use std::process::ExitCode;
use sysmlv2_parser::json::{model_to_compact_json, to_compact_json_string};
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};
use sysmlv2_parser::span::LineIndex;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let mut path = None;
    let mut lib_dir = None;
    let mut i = 0;
    while i < args.len() {
        if args[i] == "--lib" && i + 1 < args.len() {
            lib_dir = Some(args[i + 1].clone());
            i += 2;
        } else {
            path = Some(args[i].clone());
            i += 1;
        }
    }
    let Some(path) = path else {
        eprintln!("usage: to_json <file.sysml|file.kerml> [--lib <library-dir>]");
        return ExitCode::from(2);
    };
    let src = match std::fs::read_to_string(&path) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("error: cannot read {path}: {e}");
            return ExitCode::FAILURE;
        }
    };

    let report = |diags: &[sysmlv2_parser::Diagnostic]| {
        let index = LineIndex::new(&src);
        for d in diags {
            let pos = index.line_col(d.span.start);
            eprintln!("{path}:{}:{}: {}", pos.line, pos.col, d.message);
        }
    };

    if let Some(lib) = lib_dir {
        let mut model = Model::new();
        if let Err(e) = model.load_library_dir(Path::new(&lib)) {
            eprintln!("error: cannot load library {lib}: {e}");
            return ExitCode::FAILURE;
        }
        let unit = model.add_source(path.clone(), &src);
        if !unit.diagnostics.is_empty() {
            report(&unit.diagnostics);
            return ExitCode::FAILURE;
        }
        let json = serde_json::to_string_pretty(&model_to_compact_json(&model)).unwrap();
        println!("{json}");
        return ExitCode::SUCCESS;
    }

    let parse = if path.ends_with(".kerml") {
        parse_kerml_source(&src)
    } else {
        parse_source(&src)
    };
    if !parse.diagnostics.is_empty() {
        report(&parse.diagnostics);
        return ExitCode::FAILURE;
    }
    println!("{}", to_compact_json_string(&parse.unit));
    ExitCode::SUCCESS
}
