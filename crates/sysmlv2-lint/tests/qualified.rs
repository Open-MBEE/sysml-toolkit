//! `qualified-names` gates: consistency default, the three policy
//! styles (qualified / minimal / imported incl. the import-adding
//! fix and the conflict exemption), bracket-unit exemption, and the
//! sourceless complaint.

use sysmlv2_lint::{Config, Finding, lint, lint_with_sources};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

/// Lint `src` (one unit) with source text against the vendored
/// standard library.
fn run(src: &str, config: &Config) -> Vec<Finding> {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_source("t.sysml", src);
    let mut resolved = ResolvedModel::build(&model);
    let unit = resolved.reference_sites().last().expect("sites").unit;
    lint_with_sources(&mut resolved, config, &[(unit, src)])
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

fn qualified(findings: &[Finding]) -> Vec<&Finding> {
    findings
        .iter()
        .filter(|f| f.rule == "qualified-names")
        .collect()
}

fn cfg(json: &str) -> Config {
    Config::from_json(json).unwrap()
}

const ON: &str = r#"{ "rules": { "qualified-names": "warn" } }"#;

#[test]
fn off_by_default_and_complains_without_sources() {
    let src = "package G {\n    private import ISQ::*;\n    \
               attribute a : MassValue;\n    attribute b : ISQ::MassValue;\n}\n";
    assert!(qualified(&run(src, &Config::default())).is_empty());
    // Enabled but sourceless (plain `lint`): a configuration finding,
    // not a silent skip.
    let mut model = Model::new();
    model.add_source("t.sysml", src);
    let mut resolved = ResolvedModel::build(&model);
    let findings = lint(&mut resolved, &cfg(ON));
    assert!(
        findings
            .iter()
            .any(|f| f.rule == "lint-config" && f.message.contains("qualified-names")),
        "{findings:?}"
    );
}

#[test]
fn inconsistent_spellings_flag_the_minority() {
    // The screenshot case: one element, two spellings — the minority
    // site re-spells to the majority form.
    let src = "package G {\n    private import ISQ::*;\n    \
               attribute a : MassValue;\n    attribute b : MassValue;\n    \
               attribute c : ISQ::MassValue;\n}\n";
    let findings = run(src, &cfg(ON));
    let q = qualified(&findings);
    assert_eq!(q.len(), 1, "{findings:?}");
    let f = q[0];
    assert!(
        f.message.contains("`ISQ::MassValue`") && f.message.contains("`MassValue` at 2 of 3 sites"),
        "{}",
        f.message
    );
    // The finding covers the whole written reference — clients render
    // the squiggle over `ISQ::MassValue`, not a segment of it.
    let span = f.span.expect("span");
    assert_eq!(
        &src[span.start as usize..span.end as usize],
        "ISQ::MassValue"
    );
    let fixed = apply_fix(src, f);
    assert!(fixed.contains("attribute c : MassValue;"), "{fixed}");
}

#[test]
fn qualified_style_wants_the_full_owner_chain() {
    let src = "package G {\n    private import ISQ::*;\n    \
               attribute a : MassValue;\n}\n";
    let findings = run(
        src,
        &cfg(r#"{ "rules": { "qualified-names": { "severity": "warn", "style": "qualified" } } }"#),
    );
    let q = qualified(&findings);
    // The typing reference and nothing else (imports are exempt).
    assert_eq!(q.len(), 1, "{findings:?}");
    assert_eq!(q[0].suggest.as_deref(), Some("ISQBase::MassValue"));
    let fixed = apply_fix(src, q[0]);
    assert!(
        fixed.contains("attribute a : ISQBase::MassValue;"),
        "{fixed}"
    );
}

#[test]
fn minimal_style_shortens_and_leaves_units_alone() {
    let src = "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
               attribute a : ISQ::MassValue = 1 [kg];\n}\n";
    let findings = run(
        src,
        &cfg(r#"{ "rules": { "qualified-names": { "severity": "warn", "style": "minimal" } } }"#),
    );
    let q = qualified(&findings);
    // Only the typing — `kg` inside the bracket is the unit-spelling
    // rule's business.
    assert_eq!(q.len(), 1, "{findings:?}");
    assert_eq!(q[0].suggest.as_deref(), Some("MassValue"));
    let fixed = apply_fix(src, q[0]);
    assert!(
        fixed.contains("attribute a : MassValue = 1 [kg];"),
        "{fixed}"
    );
}

#[test]
fn imported_style_adds_the_missing_import() {
    let src = "package G {\n    private import ScalarValues::Real;\n    \
               attribute a : ISQBase::MassValue;\n}\n";
    let findings = run(
        src,
        &cfg(r#"{ "rules": { "qualified-names": { "severity": "warn", "style": "imported" } } }"#),
    );
    let q = qualified(&findings);
    assert_eq!(q.len(), 1, "{findings:?}");
    let f = q[0];
    assert!(
        f.message
            .contains("`MassValue` with `ISQBase::MassValue` imported"),
        "{}",
        f.message
    );
    let fixed = apply_fix(src, f);
    assert!(
        fixed
            .contains("private import ScalarValues::Real;\n    private import ISQBase::MassValue;"),
        "{fixed}"
    );
    assert!(fixed.contains("attribute a : MassValue;"), "{fixed}");
    // The fixed text lints clean under the same policy.
    let refindings = run(
        &fixed,
        &cfg(r#"{ "rules": { "qualified-names": { "severity": "warn", "style": "imported" } } }"#),
    );
    assert!(qualified(&refindings).is_empty(), "{refindings:?}");
}

#[test]
fn imported_style_respects_conflicts_and_visibility() {
    // `MassValue` is locally taken — the qualified reference is
    // earning its keep and stays silent; the visible target re-spells
    // directly without an import.
    let src = "package G {\n    private import ISQ::*;\n    \
               attribute def MassValue;\n    \
               attribute a : ISQBase::MassValue;\n    \
               attribute b : ISQ::DurationValue;\n}\n";
    let findings = run(
        src,
        &cfg(r#"{ "rules": { "qualified-names": { "severity": "warn", "style": "imported" } } }"#),
    );
    let q = qualified(&findings);
    assert_eq!(q.len(), 1, "{findings:?}");
    let f = q[0];
    assert_eq!(f.suggest.as_deref(), Some("DurationValue"), "{}", f.message);
    let fixed = apply_fix(src, f);
    assert!(fixed.contains("attribute b : DurationValue;"), "{fixed}");
    assert!(
        fixed.contains("attribute a : ISQBase::MassValue;"),
        "{fixed}"
    );
}

#[test]
fn necessary_qualification_is_not_inconsistency() {
    // `wetMass` is a member of the part — outside the part's body the
    // reference *must* qualify, so the spelling difference is
    // necessity, not inconsistency: no finding, and certainly no
    // finding without a fix.
    let src = "package G {\n    private import ISQ::*;\n    private import SI::*;\n    \
               part propellantSystem {\n        \
               attribute wetMass : MassValue = 100 [kg];\n        \
               attribute margin : MassValue = wetMass;\n    }\n    \
               attribute total : MassValue = propellantSystem::wetMass;\n}\n";
    let findings = run(src, &cfg(ON));
    let q = qualified(&findings);
    assert!(q.is_empty(), "{q:?}");
    // And every consistency finding that does surface carries a fix.
    let src2 = "package G {\n    private import ISQ::*;\n    \
                attribute a : MassValue;\n    attribute b : MassValue;\n    \
                attribute c : ISQ::MassValue;\n}\n";
    let findings = run(src2, &cfg(ON));
    for f in qualified(&findings) {
        assert!(f.fix.is_some(), "{f:?}");
    }
}
