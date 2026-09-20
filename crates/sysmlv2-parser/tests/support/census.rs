//! Shared stage runner for the external negative-fixture census. The
//! gated baseline tests (`tests/opensysml.rs`) and the reporting example
//! (`examples/opensysmlcheck.rs`) include this file, so both run exactly
//! the same stages and classify a file by the same rule. Referential
//! findings are always recorded under their own stage; whether they can
//! make a file *diagnosed* depends on the mode: without a library they
//! are missing dependencies (a file with nothing else stays unknown),
//! with the library they are findings like any other (a private-member
//! reference is rejected by exactly that stage). Contracts are satisfied
//! only by tagged rows, which the referential stage never produces.
#![allow(dead_code)]

use serde_json::{Value, json};
use std::collections::BTreeMap;
use sysmlv2_parser::{check, json::ResolvedModel, model::Model};

/// Stage names in pipeline order. A parse error ends the pipeline;
/// the three model stages run only on a clean parse.
pub const STAGES: [&str; 4] = ["parse", "structure", "referential", "semantics"];

/// Run every stage over the one user unit of `model` (library units may
/// precede it) and return `{stage, severity, message, start, end}` rows.
pub fn stage_diagnostics(model: &Model) -> Vec<Value> {
    let (index, unit) = model
        .units()
        .iter()
        .enumerate()
        .find(|(_, u)| !u.is_library)
        .expect("one user unit");
    let mut rows = Vec::new();
    let mut record = |stage: &str, d: &sysmlv2_parser::Diagnostic| {
        rows.push(json!({
            "stage": stage,
            "severity": format!("{:?}", d.severity),
            "message": d.message,
            "start": d.span.start,
            "end": d.span.end,
        }));
    };
    for d in &unit.diagnostics {
        record("parse", d);
    }
    if !unit.diagnostics.is_empty() {
        return rows;
    }
    for d in check::validate(&unit.unit) {
        record("structure", &d);
    }
    let mut resolved = ResolvedModel::build(model);
    for (u, d) in check::validate_model_with(&mut resolved, model) {
        if u == index {
            record("referential", &d);
        }
    }
    for (u, d) in check::validate_semantics_with(&mut resolved, model) {
        if u == index {
            record("semantics", &d);
        }
    }
    rows
}

/// True when no stage produced a row — or, when `ignore_referential`
/// (the no-library mode), no stage other than the referential one.
pub fn is_unknown(rows: &[Value], ignore_referential: bool) -> bool {
    rows.iter()
        .all(|d| ignore_referential && d["stage"] == "referential")
}

/// The baseline status of a file: `accepted (adjudicated)` for a
/// registered acceptance that is unknown, `unknown_label` for any other
/// unknown file, `diagnostic baseline` otherwise.
pub fn status(
    rows: &[Value],
    ignore_referential: bool,
    accepted: bool,
    unknown_label: &str,
) -> String {
    match (is_unknown(rows, ignore_referential), accepted) {
        (true, true) => "accepted (adjudicated)".to_string(),
        (true, false) => unknown_label.to_string(),
        (false, _) => "diagnostic baseline".to_string(),
    }
}

/// Fixtures whose registered acceptance verdict applies (no rejection
/// expected).
pub fn accepted_fixtures(negative_contracts: &Value) -> Vec<String> {
    negative_contracts["contracts"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|c| c["verdict"] == "accepted")
        .map(|c| c["fixture"].as_str().unwrap().to_string())
        .collect()
}

/// A row satisfies a rejection contract when it carries the rule tag,
/// the registered category, and a nonempty span.
fn satisfies(rows: &[Value], rule: &str, severity: &Value) -> bool {
    let tag = format!("[{rule}]");
    rows.iter().any(|d| {
        d["message"].as_str().is_some_and(|m| m.contains(&tag))
            && d["severity"] == *severity
            && d["start"].as_u64() < d["end"].as_u64()
    })
}

/// Registered contracts that the full-library rows do not satisfy: probe
/// contracts by fixture name under `probes/`, negative contracts by their
/// own path, an `accepted` verdict requiring no rejection at all.
pub fn contract_failures(
    rows: &BTreeMap<String, Vec<Value>>,
    static_contracts: &Value,
    negative_contracts: &Value,
) -> Vec<String> {
    let mut missing = Vec::new();
    for c in static_contracts["contracts"].as_array().unwrap() {
        let name = format!("probes/{}", c["fixture"].as_str().unwrap());
        let ok = rows
            .get(&name)
            .is_some_and(|r| satisfies(r, c["rule"].as_str().unwrap(), &c["severity"]));
        if !ok {
            missing.push(name);
        }
    }
    for c in negative_contracts["contracts"].as_array().unwrap() {
        let name = c["fixture"].as_str().unwrap();
        let ok = rows.get(name).is_some_and(|r| {
            if c["verdict"] == "accepted" {
                is_unknown(r, false)
            } else {
                satisfies(r, c["rule"].as_str().unwrap(), &c["severity"])
            }
        });
        if !ok {
            missing.push(name.to_string());
        }
    }
    missing
}
