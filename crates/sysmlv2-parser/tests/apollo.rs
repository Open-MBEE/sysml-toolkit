//! External-validation gates over the Airbus Apollo 11 model — the first
//! substantial model independent of the OMG pilot lineage.
//!
//! Every test skips (with a note) when the `spec-refs/apollo-11-sysml-v2`
//! submodule is not initialized, so plain clones stay green; run
//! `git submodule update --init` to enable. Counts are ratchets: they may
//! move only in the improving direction, deliberately.

#![cfg(feature = "json")]

use std::fs;
use sysmlv2_parser::ast::Dialect;
use sysmlv2_parser::check::{
    ConstraintVerdict, check_constraints, validate, validate_model, validate_semantics,
};
use sysmlv2_parser::json::{ResolvedModel, to_compact_json};
use sysmlv2_parser::lift::from_compact_json;
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::parse_source;
use sysmlv2_parser::print::{format_source, print_source};

macro_rules! apollo_or_skip {
    () => {
        match sysmlv2_testkit::apollo_files() {
            Some(files) => files,
            None => {
                eprintln!("skipping: apollo-11-sysml-v2 submodule not initialized");
                return;
            }
        }
    };
}

/// The whole model + standard library as one resolution context.
fn apollo_model(files: &[std::path::PathBuf]) -> Model {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    for f in files {
        let src = fs::read_to_string(f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    model
}

/// Every file parses clean and passes body-context validation.
#[test]
fn apollo_parses_and_validates() {
    let files = apollo_or_skip!();
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        let parse = parse_source(&src);
        assert!(
            parse.diagnostics.is_empty(),
            "{}: {:?}",
            f.display(),
            parse.diagnostics[0]
        );
        let findings = validate(&parse.unit);
        assert!(findings.is_empty(), "{}: {:?}", f.display(), findings[0]);
    }
}

/// Referential + semantic checks over the resolved model: zero findings
/// (the one pre-fix unresolved reference was the recursive-rollup chain,
/// resolved since — see `tests/check.rs::recursive_rollup_chain_member_resolves`).
#[test]
fn apollo_checks_clean() {
    let files = apollo_or_skip!();
    let model = apollo_model(&files);
    assert!(!model.has_errors());
    let findings: Vec<_> = validate_model(&model)
        .into_iter()
        .chain(validate_semantics(&model))
        .collect();
    // The invocation-arity check flags exactly the model's three genuine
    // under-application defects: both
    // `calculateDeltaV` call sites (4 params, 3 arguments — `mf` never
    // bound) and the `ln` shim call (their `calc <ln> naturalLogarithm`
    // declares two parameters). Nothing else may fire.
    let (arity, rest): (Vec<_>, Vec<_>) = findings
        .into_iter()
        .partition(|(_, d)| d.message.contains("binds"));
    assert!(
        rest.is_empty(),
        "{} non-arity findings, first: {:?}",
        rest.len(),
        rest[0].1
    );
    let n_deltav = arity
        .iter()
        .filter(|(_, d)| d.message.contains("`calculateDeltaV`"))
        .count();
    let n_ln = arity
        .iter()
        .filter(|(_, d)| d.message.contains("`ln`"))
        .count();
    assert_eq!(
        (arity.len(), n_deltav, n_ln),
        (3, 2, 1),
        "arity findings moved: {:?}",
        arity.iter().map(|(_, d)| &d.message).collect::<Vec<_>>()
    );
}

/// Formatter: idempotent and AST-preserving (identical compact JSON, since
/// IDs derive from ownership paths, not spans) on every file.
#[test]
fn apollo_format_stable() {
    let files = apollo_or_skip!();
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        let json0 = to_compact_json(&parse_source(&src).unit);
        let once = format_source(&src, Dialect::Sysml).expect("formats");
        let twice = format_source(&once, Dialect::Sysml).expect("reformats");
        assert_eq!(once, twice, "{}: formatter not idempotent", f.display());
        let json1 = to_compact_json(&parse_source(&once).unit);
        assert_eq!(json0, json1, "{}: formatting changed the AST", f.display());
    }
}

/// JSON round-trip byte-identity per file (found the `'$'`-unit and
/// Dependency double-escaping defects; both fixed with regressions in
/// `tests/roundtrip.rs`).
#[test]
fn apollo_json_roundtrip() {
    let files = apollo_or_skip!();
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        let json1 = to_compact_json(&parse_source(&src).unit);
        let lifted = from_compact_json(&json1).expect("lift");
        assert!(
            lifted.errors.is_empty(),
            "{}: {:?}",
            f.display(),
            lifted.errors
        );
        let printed = print_source(&lifted.unit);
        let reparsed = parse_source(&printed);
        assert!(
            reparsed.diagnostics.is_empty(),
            "{}: regenerated text does not parse: {:?}",
            f.display(),
            reparsed.diagnostics[0]
        );
        assert_eq!(
            json1,
            to_compact_json(&reparsed.unit),
            "{}: JSON changed across the round-trip",
            f.display()
        );
    }
}

/// Evaluator coverage ratchet over the model's feature values.
#[test]
fn apollo_eval_ratchet() {
    let files = apollo_or_skip!();
    let model = apollo_model(&files);
    let mut r = ResolvedModel::build(&model);
    let features = r.features_with_values();
    let ok = features.iter().filter(|e| r.evaluate(**e).is_ok()).count();
    assert!(
        features.len() >= 3669,
        "expected the full Apollo feature-value population, got {}",
        features.len()
    );
    assert!(
        ok >= 3063,
        "apollo eval ratchet moved down: {ok}/{}",
        features.len()
    );
}

/// Constraint verdicts: the model is a conforming scaffold — nothing may
/// be violated. The mission-timeline assertions (`isDuring(…)` over the
/// July 1969 event sequence) evaluate to satisfied; the requirement
/// constraints over deliberately unbound "actual" values stay undecided
/// (the solving gate lives in `sysmlv2-solve/tests/apollo.rs`).
#[test]
fn apollo_verify_no_violations() {
    let files = apollo_or_skip!();
    let model = apollo_model(&files);
    let checks = check_constraints(&model);
    let vio = checks
        .iter()
        .filter(|c| matches!(c.verdict, ConstraintVerdict::Violated))
        .count();
    let sat = checks
        .iter()
        .filter(|c| matches!(c.verdict, ConstraintVerdict::Satisfied))
        .count();
    assert_eq!(vio, 0, "violated constraints in a conforming model");
    assert!(sat >= 14, "satisfied ratchet moved down: {sat}");
    assert!(
        checks.len() >= 72,
        "expected all constraint bodies, got {}",
        checks.len()
    );
}
