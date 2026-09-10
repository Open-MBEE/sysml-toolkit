//! `dimensional-consistency` gates: quantity typing against value
//! units over the real standard library — mismatch findings with
//! re-typing fixes, untyped-inference findings with declaring fixes,
//! spelling preferences, aspect scoping, and the silent cases
//! (consistent models, opaque units, no library).

use sysmlv2_lint::{Config, Finding, Severity, lint};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

/// Lint `src` (one unit) against the vendored standard library.
fn run_with_lib(src: &str, config: &Config) -> (Vec<Finding>, String) {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_source("t.sysml", src);
    let mut resolved = ResolvedModel::build(&model);
    (lint(&mut resolved, config), src.to_string())
}

/// Apply a finding's fix edits to the unit text (single-unit models).
fn apply_fix(src: &str, f: &Finding) -> String {
    let fix = f.fix.as_ref().expect("fix");
    let mut edits = fix.edits.clone();
    edits.sort_by_key(|e| e.span.start);
    let mut out = String::new();
    let mut at = 0usize;
    for e in edits {
        out.push_str(&src[at..e.span.start as usize]);
        out.push_str(&e.replacement);
        at = e.span.end as usize;
    }
    out.push_str(&src[at..]);
    out
}

fn dimensional(findings: &[Finding]) -> Vec<&Finding> {
    findings
        .iter()
        .filter(|f| f.rule == "dimensional-consistency")
        .collect()
}

#[test]
fn untyped_attribute_infers_from_the_unit() {
    // The motivating line: an untyped attribute with an acceleration
    // unit infers the acceleration quantity type, spelled through the
    // wrapper package when nothing is imported.
    let (findings, src) = run_with_lib(
        "package G {\n    attribute gravity = 9.8 [SI::m / SI::s ** 2];\n}\n",
        &Config::default(),
    );
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    let f = d[0];
    assert_eq!(f.severity, Severity::Warn);
    assert!(
        f.message.contains("`gravity`") && f.message.contains("`ISQ::AccelerationValue`"),
        "{}",
        f.message
    );
    assert_eq!(f.element.as_deref(), Some("G::gravity"));
    assert_eq!(f.suggest.as_deref(), Some("ISQ::AccelerationValue"));
    let fixed = apply_fix(&src, f);
    assert!(
        fixed.contains("attribute gravity : ISQ::AccelerationValue = 9.8 [SI::m / SI::s ** 2];"),
        "{fixed}"
    );
}

#[test]
fn inventory_advertises_the_untyped_default() {
    // Configuration UIs render scope rows from the inventory — the
    // advertised default must say what an unset `untyped` scope
    // actually does (warn, pinned above).
    let rule = sysmlv2_lint::RULES
        .iter()
        .find(|r| r.id == "dimensional-consistency")
        .expect("rule in inventory");
    let untyped = rule
        .scopes
        .iter()
        .find(|s| s.key == "untyped")
        .expect("untyped scope advertised");
    assert_eq!(untyped.default, Some(Severity::Warn));
}

#[test]
fn imports_shorten_the_inferred_spelling() {
    // With the quantity types imported, the simple name resolves and
    // wins over the qualified spelling.
    let (findings, src) = run_with_lib(
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute gravity = 9.8 [m/s**2];\n}\n",
        &Config::default(),
    );
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    assert_eq!(d[0].suggest.as_deref(), Some("AccelerationValue"));
    let fixed = apply_fix(&src, d[0]);
    assert!(
        fixed.contains("attribute gravity : AccelerationValue = 9.8 [m/s**2];"),
        "{fixed}"
    );
}

#[test]
fn plain_literals_infer_scalar_value_types() {
    let (findings, _) = run_with_lib(
        "package G {\n    private import ScalarValues::*;\n    \
         attribute r = 9.8;\n    attribute n = 3;\n    attribute b = true;\n    \
         attribute s = \"tag\";\n}\n",
        &Config::default(),
    );
    let suggests: Vec<_> = dimensional(&findings)
        .iter()
        .filter_map(|f| f.suggest.as_deref())
        .collect();
    assert_eq!(
        suggests,
        ["Real", "Integer", "Boolean", "String"],
        "{findings:?}"
    );
}

#[test]
fn mismatched_declared_type_flags_with_a_retyping_fix() {
    let (findings, src) = run_with_lib(
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute mass : MassValue = 9.8 [m/s**2];\n}\n",
        &Config::default(),
    );
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    let f = d[0];
    assert_eq!(f.severity, Severity::Warn);
    assert!(
        f.message.contains("`MassValue`")
            && f.message.contains("dimension M")
            && f.message.contains("measures L*T^-2"),
        "{}",
        f.message
    );
    let fixed = apply_fix(&src, f);
    assert!(
        fixed.contains("attribute mass : AccelerationValue = 9.8 [m/s**2];"),
        "{fixed}"
    );
}

#[test]
fn consistent_typing_is_silent() {
    // Direct SI spelling, and a prefixed/derived spelling that reaches
    // the same dimension through unit conversions.
    let (findings, _) = run_with_lib(
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute a : AccelerationValue = 9.8 [m/s**2];\n    \
         attribute b : AccelerationValue = 1.2 [km/h/s];\n    \
         attribute t : DurationValue = 30 [min];\n}\n",
        &Config::default(),
    );
    assert!(dimensional(&findings).is_empty(), "{findings:?}");
}

#[test]
fn indeterminate_sides_are_silent() {
    // An opaque user unit has no library dimension; a typed attribute
    // with a plain number carries no unit; subsetting delivers the
    // type indirectly — none of these speak.
    let (findings, _) = run_with_lib(
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute def U;\n    attribute u = 3 [G::U];\n    \
         attribute m : MassValue = 9.8;\n    \
         attribute base : MassValue = 1 [kg];\n    attribute sub :> base;\n}\n",
        &Config::default(),
    );
    assert!(dimensional(&findings).is_empty(), "{findings:?}");
}

#[test]
fn no_library_is_silent() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package G {\n    attribute gravity = 9.8;\n    attribute n = 3;\n}\n",
    );
    let mut resolved = ResolvedModel::build(&model);
    let findings = lint(&mut resolved, &Config::default());
    assert!(dimensional(&findings).is_empty(), "{findings:?}");
}

#[test]
fn aspect_scopes_tune_independently() {
    let src = "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
               attribute gravity = 9.8 [m/s**2];\n    \
               attribute mass : MassValue = 9.8 [m/s**2];\n}\n";
    // `untyped` off keeps the mismatch finding alone.
    let cfg = Config::from_json(
        r#"{ "rules": { "dimensional-consistency": { "scopes": { "untyped": "off" } } } }"#,
    )
    .unwrap();
    let (findings, _) = run_with_lib(src, &cfg);
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    assert!(d[0].message.contains("`MassValue`"), "{}", d[0].message);
    // `mismatch` off keeps the inference hint alone, re-tuned to warn.
    let cfg = Config::from_json(
        r#"{ "rules": { "dimensional-consistency": { "scopes": { "mismatch": "off", "untyped": "warn" } } } }"#,
    )
    .unwrap();
    let (findings, _) = run_with_lib(src, &cfg);
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    assert_eq!(d[0].severity, Severity::Warn);
    assert!(d[0].message.contains("`gravity`"), "{}", d[0].message);
    // The rule off is fully off — the unseeded untyped default must
    // not resurrect it.
    let cfg = Config::from_json(r#"{ "rules": { "dimensional-consistency": "off" } }"#).unwrap();
    let (findings, _) = run_with_lib(src, &cfg);
    assert!(dimensional(&findings).is_empty(), "{findings:?}");
}

#[test]
fn untyped_usage_attribute_findings_carry_the_declaring_fix() {
    let cfg = Config::from_json(r#"{ "rules": { "untyped-usage": "warn" } }"#).unwrap();
    let (findings, src) = run_with_lib(
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute gravity = 9.8 [m/s**2];\n}\n",
        &cfg,
    );
    let f = findings
        .iter()
        .find(|f| f.rule == "untyped-usage")
        .expect("untyped-usage finding");
    assert_eq!(f.suggest.as_deref(), Some("AccelerationValue"));
    let fixed = apply_fix(&src, f);
    assert!(
        fixed.contains("attribute gravity : AccelerationValue = 9.8 [m/s**2];"),
        "{fixed}"
    );
}

#[test]
fn finding_span_covers_name_through_value() {
    let (findings, src) = run_with_lib(
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute gravity = 9.8 [m/s**2];\n}\n",
        &Config::default(),
    );
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    let span = d[0].span.expect("span");
    let covered = &src[span.start as usize..span.end as usize];
    assert_eq!(covered, "gravity = 9.8 [m/s**2]", "{covered:?}");
}

#[test]
fn ambiguous_units_offer_every_compatible_type() {
    // `J` names the energy unit, so the energy type is the preferred
    // inference even though torque and friends share the dimension —
    // those arrive as alternative fixes for the quick-fix menu.
    let (findings, src) = run_with_lib(
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute burn = 30 [J];\n}\n",
        &Config::default(),
    );
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    let f = d[0];
    assert_eq!(f.suggest.as_deref(), Some("EnergyValue"), "{}", f.message);
    assert!(f.message.contains("also compatible"), "{}", f.message);
    let alt_labels: Vec<&str> = f.alternatives.iter().map(|a| a.label.as_str()).collect();
    assert!(
        alt_labels.iter().any(|l| l.contains("TorqueValue")),
        "{alt_labels:?}"
    );
    // Every alternative applies cleanly at the same insertion point.
    let alt = f
        .alternatives
        .iter()
        .find(|a| a.label.contains("TorqueValue"))
        .expect("torque alternative");
    let mut with_alt = f.clone();
    with_alt.fix = Some(alt.clone());
    let fixed = apply_fix(&src, &with_alt);
    assert!(
        fixed.contains("attribute burn : TorqueValue = 30 [J];"),
        "{fixed}"
    );
}

#[test]
fn mismatch_offers_alternatives_too() {
    let (findings, _) = run_with_lib(
        "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute torque : MassValue = 30 [J];\n}\n",
        &Config::default(),
    );
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    let f = d[0];
    assert_eq!(f.suggest.as_deref(), Some("EnergyValue"), "{}", f.message);
    assert!(
        f.alternatives
            .iter()
            .any(|a| a.label.contains("TorqueValue")),
        "{:?}",
        f.alternatives.iter().map(|a| &a.label).collect::<Vec<_>>()
    );
}
