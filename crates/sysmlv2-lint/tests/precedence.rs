//! `unit-precedence` gates over the real standard library: a quantity
//! bracket on the right operand of an arithmetic operator binds to that
//! operand alone — the flagged spellings, the parenthesizing fix and
//! the written-binding alternative, the chain the fix covers, the
//! silent cases (parentheses, `*` alone, a quantity on the left, an
//! annotated magnitude, a cancelling unit), the hand-off to
//! `dimensional-consistency`, and the typing inference that no longer
//! lets the bracket's unit name a value of another dimension.

use sysmlv2_lint::{Config, Finding, Fix, RULES, RuleId, Severity, canonicalization_digest, lint};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

const PRELUDE: &str = "package G {\n    private import ISQ::*;\n    private import SI::*;\n";

/// Lint `body` inside the importing package, against the vendored
/// standard library.
fn run_with_lib(body: &str, config: &Config) -> (Vec<Finding>, String) {
    let src = format!("{PRELUDE}{body}}}\n");
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_source("t.sysml", &src);
    let mut resolved = ResolvedModel::build(&model);
    (lint(&mut resolved, config), src)
}

/// Apply a fix's edits to the unit text (single-unit models).
fn apply(src: &str, fix: &Fix) -> String {
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

fn precedence(findings: &[Finding]) -> Vec<&Finding> {
    findings
        .iter()
        .filter(|f| f.rule == RuleId::UnitPrecedence)
        .collect()
}

fn dimensional(findings: &[Finding]) -> Vec<&Finding> {
    findings
        .iter()
        .filter(|f| f.rule == RuleId::DimensionalConsistency)
        .collect()
}

#[test]
fn a_plain_number_over_a_bracketed_magnitude_flags_with_both_fixes() {
    // The motivating line: the unit binds to `15`, the value is a
    // reciprocal length, and the author meant a length.
    let (findings, src) = run_with_lib("    attribute c = 1 / 15 [km];\n", &Config::default());
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    let f = p[0];
    assert_eq!(f.severity, Severity::Warn);
    assert!(
        f.message.contains("unit `km` binds to `15` alone")
            && f.message
                .contains("`1 / 15 [km]` measures L^-1 rather than L")
            && f.message.contains("parenthesize `(1 / 15) [km]`"),
        "{}",
        f.message
    );
    assert_eq!(f.element.as_deref(), Some("G::c"));
    let span = f.span.expect("span");
    assert_eq!(&src[span.start as usize..span.end as usize], "1 / 15 [km]");
    let fix = f.fix.as_ref().expect("fix");
    assert!(fix.semantic, "the fix changes the value");
    assert!(!fix.deletes);
    assert!(fix.label.contains("`(1 / 15) [km]`"), "{}", fix.label);
    assert!(
        apply(&src, fix).contains("attribute c = (1 / 15) [km];"),
        "{}",
        apply(&src, fix)
    );
    assert_eq!(f.alternatives.len(), 1, "{:?}", f.alternatives);
    let alt = &f.alternatives[0];
    assert!(!alt.semantic, "the alternative keeps the value");
    assert!(alt.label.contains("`(15 [km])`"), "{}", alt.label);
    assert!(
        apply(&src, alt).contains("attribute c = 1 / (15 [km]);"),
        "{}",
        apply(&src, alt)
    );
    // `dimensional-consistency` steps aside: no inferred type for a
    // value whose dimension is in question.
    assert!(dimensional(&findings).is_empty(), "{findings:?}");
}

#[test]
fn parentheses_settle_the_binding_either_way() {
    let (findings, _) = run_with_lib(
        "    attribute a = (1 / 15) [km];\n    attribute b = 1 / (15 [km]);\n",
        &Config::default(),
    );
    assert!(precedence(&findings).is_empty(), "{findings:?}");
    // Both are determinate again: `a` is a length; `b` is a reciprocal
    // length, and `km` no longer puts `LengthValue` ahead of the types
    // that fit it.
    let d = dimensional(&findings);
    assert_eq!(d.len(), 2, "{findings:?}");
    let a = d.iter().find(|f| f.message.contains("`a`")).expect("a");
    assert_eq!(a.suggest.as_deref(), Some("LengthValue"), "{}", a.message);
    assert!(a.alternatives.is_empty(), "{:?}", a.alternatives);
    let b = d.iter().find(|f| f.message.contains("`b`")).expect("b");
    assert_ne!(b.suggest.as_deref(), Some("LengthValue"), "{}", b.message);
    assert!(
        b.alternatives
            .iter()
            .all(|alt| !alt.label.contains("`LengthValue`")),
        "{:?}",
        b.alternatives.iter().map(|a| &a.label).collect::<Vec<_>>()
    );
}

#[test]
fn a_typed_attribute_with_an_explicit_reciprocal_is_a_plain_mismatch() {
    // Settled binding, wrong type: the mismatch fix proposes types of
    // the value's dimension, never the unit's.
    let (findings, _) = run_with_lib(
        "    attribute c : LengthValue = 1 / (15 [km]);\n",
        &Config::default(),
    );
    assert!(precedence(&findings).is_empty(), "{findings:?}");
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    let f = d[0];
    assert!(f.message.contains("measures L^-1"), "{}", f.message);
    assert_ne!(f.suggest.as_deref(), Some("LengthValue"), "{}", f.message);
    assert!(
        f.alternatives
            .iter()
            .all(|alt| !alt.label.contains("`LengthValue`")),
        "{:?}",
        f.alternatives.iter().map(|a| &a.label).collect::<Vec<_>>()
    );
}

#[test]
fn multiplication_alone_agrees_either_way() {
    let (findings, _) = run_with_lib("    attribute a = 2 * 3 [m];\n", &Config::default());
    assert!(precedence(&findings).is_empty(), "{findings:?}");
    // …but a sum above the product does not: the chain climbs through
    // the `*` to the operator that matters.
    let (findings, src) = run_with_lib("    attribute b = 4 + 2 * 3 [m];\n", &Config::default());
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    // The product is a fine `6 [m]`; the sum is where the binding bites.
    assert!(
        p[0].message
            .contains("`4 + 2 * 3 [m]` adds `4` to a `m` quantity"),
        "{}",
        p[0].message
    );
    let fixed = apply(&src, p[0].fix.as_ref().expect("fix"));
    assert!(fixed.contains("attribute b = (4 + 2 * 3) [m];"), "{fixed}");
}

#[test]
fn a_quantity_on_the_left_keeps_the_written_binding() {
    let (findings, _) = run_with_lib(
        "    attribute r : LengthValue = 5 [mm];\n    \
         attribute s = 2 * r + 20 [mm];\n    \
         attribute t : ThermodynamicTemperatureValue = 300 [K];\n    \
         attribute ratio = t / 900 [K];\n    \
         attribute q : LengthValue;\n    \
         attribute q2 = q / 15 [km];\n",
        &Config::default(),
    );
    assert!(precedence(&findings).is_empty(), "{findings:?}");
}

#[test]
fn an_annotated_magnitude_and_a_cancelling_unit_are_silent() {
    // `d [km]` annotates an already-dimensioned feature; `[m/m]` binds
    // nothing.
    let (findings, _) = run_with_lib(
        "    attribute d : LengthValue = 3 [m];\n    \
         attribute k = 1 / d [km];\n    \
         attribute m = 1 / 4 [m/m];\n",
        &Config::default(),
    );
    assert!(precedence(&findings).is_empty(), "{findings:?}");
}

#[test]
fn the_fix_parenthesizes_the_whole_plain_chain() {
    let (findings, src) = run_with_lib(
        "    attribute radius = 22/2*25.4 + 110 [mm];\n    \
         attribute p1 = 3;\n    \
         attribute p2 = 4;\n    \
         attribute w = p1 + p2 / 15 [km];\n    \
         attribute v = 1 / 15 [km] + 3 [km];\n    \
         attribute g = p1 + (p2 / 15 [km]);\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 4, "{findings:?}");
    let fixed: Vec<String> = p
        .iter()
        .map(|f| apply(&src, f.fix.as_ref().expect("fix")))
        .collect();
    assert!(
        fixed[0].contains("attribute radius = (22/2*25.4 + 110) [mm];"),
        "{}",
        fixed[0]
    );
    assert!(
        fixed[1].contains("attribute w = (p1 + p2 / 15) [km];"),
        "{}",
        fixed[1]
    );
    // The quotient is a fine reciprocal length; the sum is what has no
    // value, and the quantity it was handed is named at that level.
    assert!(
        p[1].message
            .contains("`p1 + p2 / 15 [km]` adds `p1` to a `1/"),
        "{}",
        p[1].message
    );
    // The chain ends where the left operand stops being a plain number.
    assert!(
        fixed[2].contains("attribute v = (1 / 15) [km] + 3 [km];"),
        "{}",
        fixed[2]
    );
    // …and at a group the author closed.
    assert!(
        fixed[3].contains("attribute g = p1 + ((p2 / 15) [km]);"),
        "{}",
        fixed[3]
    );
}

#[test]
fn sums_and_powers_flag_as_mixing() {
    let (findings, src) = run_with_lib(
        "    attribute f = 2 + 3 [m];\n    attribute h = 2 ** 3 [m];\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 2, "{findings:?}");
    assert!(
        p[0].message
            .contains("`2 + 3 [m]` adds `2` to a `m` quantity"),
        "{}",
        p[0].message
    );
    assert!(
        p[1].message
            .contains("`2 ** 3 [m]` raises `2` to a `m` quantity"),
        "{}",
        p[1].message
    );
    assert!(apply(&src, p[0].fix.as_ref().expect("fix")).contains("attribute f = (2 + 3) [m];"));
    assert!(apply(&src, p[1].fix.as_ref().expect("fix")).contains("attribute h = (2 ** 3) [m];"));
}

#[test]
fn a_declared_plain_number_without_a_value_counts() {
    // No value to evaluate, but the declared type says plain number.
    let (findings, _) = run_with_lib(
        "    attribute y : ScalarValues::Real;\n    attribute z = y / 15 [km];\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    assert!(
        p[0].message
            .contains("`y / 15 [km]` measures L^-1 rather than L"),
        "{}",
        p[0].message
    );
    // An untyped, unvalued operand is indeterminate: silence.
    let (findings, _) = run_with_lib(
        "    attribute u;\n    attribute z = u / 15 [km];\n",
        &Config::default(),
    );
    assert!(precedence(&findings).is_empty(), "{findings:?}");
}

#[test]
fn an_angle_reads_by_its_unit() {
    // Plane angle is dimensionless, so the base dimensions agree; the
    // units themselves tell the readings apart.
    let (findings, _) = run_with_lib(
        "    attribute n = 8;\n    attribute v = 360 / n ['°'];\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    assert!(
        p[0].message.contains("measures `1/°` rather than `'°'`"),
        "{}",
        p[0].message
    );
}

#[test]
fn constraint_bodies_are_scanned() {
    let (findings, src) = run_with_lib(
        "    attribute d : LengthValue = 3 [m];\n    \
         assert constraint { d > 1 / 15 [km] }\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    let fixed = apply(&src, p[0].fix.as_ref().expect("fix"));
    assert!(fixed.contains("{ d > (1 / 15) [km] }"), "{fixed}");
}

#[test]
fn switching_the_rule_off_hands_the_attribute_back() {
    let config = Config::from_json(r#"{ "rules": { "unit-precedence": "off" } }"#).expect("config");
    let (findings, _) = run_with_lib(
        "    attribute c = 1 / 15 [km];\n    attribute e : LengthValue = 1 / 15 [km];\n",
        &config,
    );
    assert!(precedence(&findings).is_empty(), "{findings:?}");
    let d = dimensional(&findings);
    assert_eq!(d.len(), 2, "{findings:?}");
    for f in d {
        assert_ne!(f.suggest.as_deref(), Some("LengthValue"), "{}", f.message);
    }
}

#[test]
fn scoping_by_owner_metaclass_applies() {
    let config = Config::from_json(
        r#"{ "rules": { "unit-precedence": { "scopes": { "AttributeUsage": "off" } } } }"#,
    )
    .expect("config");
    let (findings, _) = run_with_lib(
        "    attribute c = 1 / 15 [km];\n    \
         attribute d : LengthValue = 3 [m];\n    \
         assert constraint { d > 1 / 15 [km] }\n",
        &config,
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    assert!(
        p[0].element.as_deref() != Some("G::c"),
        "the attribute scope is off: {:?}",
        p[0].element
    );
}

#[test]
fn inventory_advertises_warn_without_scopes() {
    let r = RULES
        .iter()
        .find(|r| r.id == RuleId::UnitPrecedence)
        .expect("inventory entry");
    assert_eq!(r.id.id(), "unit-precedence");
    assert_eq!(r.default, Severity::Warn);
    assert!(r.scopes.is_empty() && r.options.is_empty());
}

#[test]
fn a_sign_on_either_side_is_transparent() {
    // `-1 / 15 [km]` signs the left operand; `1 / -15 [km]` signs the
    // magnitude (the sign wraps the primary, so the unit still binds
    // to `15` alone). A parenthesized signed quantity is a closed group.
    let (findings, src) = run_with_lib(
        "    attribute a = -1 / 15 [km];\n    \
         attribute b = 1 / -15 [km];\n    \
         attribute c = 2 ** -3 [m];\n    \
         attribute d = 1 / (-15 [km]);\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 3, "{findings:?}");
    let fixed: Vec<String> = p
        .iter()
        .map(|f| apply(&src, f.fix.as_ref().expect("fix")))
        .collect();
    assert!(
        fixed[0].contains("attribute a = (-1 / 15) [km];"),
        "{}",
        fixed[0]
    );
    assert!(
        fixed[1].contains("attribute b = (1 / -15) [km];"),
        "{}",
        fixed[1]
    );
    assert!(
        fixed[2].contains("attribute c = (2 ** -3) [m];"),
        "{}",
        fixed[2]
    );
    assert!(
        p[1].message.contains("parenthesize `(1 / -15) [km]`"),
        "{}",
        p[1].message
    );
    // `dimensional-consistency` stepped aside for all three; `d` is
    // settled and infers as written.
    let d = dimensional(&findings);
    assert_eq!(d.len(), 1, "{findings:?}");
    assert!(d[0].message.contains("`d`"), "{}", d[0].message);
}

#[test]
fn a_parenthesized_magnitude_keeps_its_parentheses_in_the_text() {
    let (findings, src) = run_with_lib("    attribute a = 1 / (2 + 3) [km];\n", &Config::default());
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    let f = p[0];
    assert!(
        f.message.contains("binds to `(2 + 3)` alone")
            && f.message.contains("parenthesize `(1 / (2 + 3)) [km]`"),
        "{}",
        f.message
    );
    assert!(
        apply(&src, f.fix.as_ref().expect("fix")).contains("attribute a = (1 / (2 + 3)) [km];")
    );
    let alt = &f.alternatives[0];
    assert!(alt.label.contains("`((2 + 3) [km])`"), "{}", alt.label);
    assert!(apply(&src, alt).contains("attribute a = 1 / ((2 + 3) [km]);"));
}

#[test]
fn a_parenthesized_chain_top_gains_inner_parentheses() {
    let (findings, src) =
        run_with_lib("    attribute a = (1 / 15 [km]) * 2;\n", &Config::default());
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    let fixed = apply(&src, p[0].fix.as_ref().expect("fix"));
    assert!(
        fixed.contains("attribute a = ((1 / 15) [km]) * 2;"),
        "{fixed}"
    );
}

#[test]
fn remainder_and_caret_count_as_binding_operators() {
    let (findings, src) = run_with_lib(
        "    attribute a = 7 % 3 [m];\n    attribute b = 2 ^ 3 [m];\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 2, "{findings:?}");
    assert!(
        p[0].message.contains("takes `7` modulo a `m` quantity"),
        "{}",
        p[0].message
    );
    assert!(apply(&src, p[0].fix.as_ref().expect("fix")).contains("attribute a = (7 % 3) [m];"));
    assert!(apply(&src, p[1].fix.as_ref().expect("fix")).contains("attribute b = (2 ^ 3) [m];"));
}

#[test]
fn the_edits_respect_notes_and_line_breaks() {
    let (findings, src) = run_with_lib(
        "    attribute a = 1 /\n        15 // per segment\n        [km];\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    let fixed = apply(&src, p[0].fix.as_ref().expect("fix"));
    assert!(
        fixed.contains("attribute a = (1 /\n        15) // per segment\n        [km];"),
        "{fixed}"
    );
}

#[test]
fn a_bracket_inside_a_conditional_branch_is_its_own_chain() {
    let (findings, src) = run_with_lib(
        "    attribute a = if true ? 1 / 15 [km] else 2 [km];\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    let fixed = apply(&src, p[0].fix.as_ref().expect("fix"));
    assert!(
        fixed.contains("attribute a = if true ? (1 / 15) [km] else 2 [km];"),
        "{fixed}"
    );
}

#[test]
fn an_inherited_body_is_one_source() {
    // The definition's result reaches `constraints` again under every
    // bodiless usage typed by it: one body, one finding, attributed to
    // the definition.
    let (findings, src) = run_with_lib(
        "    attribute d : LengthValue = 3 [m];\n    \
         constraint def D { d > 1 / 15 [km] }\n    \
         assert constraint c1 : D;\n    \
         assert constraint c2 : D;\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    assert_eq!(p[0].element.as_deref(), Some("G::D"));
    let fixed = apply(&src, p[0].fix.as_ref().expect("fix"));
    assert!(
        fixed.contains("constraint def D { d > (1 / 15) [km] }"),
        "{fixed}"
    );
}

#[test]
fn a_library_body_is_never_linted() {
    // A user usage typed by a library definition carries the library's
    // body: no finding, and no edit against a unit the host does not
    // hold.
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_library_source(
        "extra.sysml",
        "package Extra {\n    private import ISQ::*;\n    private import SI::*;\n    \
         attribute d : LengthValue = 3 [m];\n    \
         constraint def D { d > 1 / 15 [km] }\n}\n",
    );
    model.add_source(
        "t.sysml",
        "package U {\n    private import Extra::*;\n    assert constraint c : D;\n}\n",
    );
    let mut resolved = ResolvedModel::build(&model);
    let findings = lint(&mut resolved, &Config::default());
    assert!(precedence(&findings).is_empty(), "{findings:?}");
}

#[test]
fn declared_numbers_count_wherever_the_model_can_classify_them() {
    // A member through a part, a user subtype of a number type, and a
    // product of unvalued numbers are all plain; a product with a
    // quantity is not.
    let (findings, _) = run_with_lib(
        "    part p { attribute m : ScalarValues::Real; }\n    \
         attribute a = p.m / 15 [km];\n    \
         attribute def Ratio :> ScalarValues::Real;\n    \
         attribute r : Ratio;\n    \
         attribute b = r / 15 [km];\n    \
         attribute n : ScalarValues::Real;\n    \
         attribute c = n * n / 15 [km];\n    \
         attribute q : LengthValue;\n    \
         attribute e = n * q / 15 [km];\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    let flagged: Vec<Option<&str>> = p.iter().map(|f| f.element.as_deref()).collect();
    assert_eq!(
        flagged,
        vec![Some("G::a"), Some("G::b"), Some("G::c")],
        "{findings:?}"
    );
}

#[test]
fn the_canonicalization_digest_tracks_the_attribute_scope() {
    // On attributes the rule decides whether `dimensional-consistency`
    // writes a type, so a sweep's output depends on it there — and
    // nowhere else.
    let base = canonicalization_digest(&Config::default());
    let off = Config::from_json(r#"{ "rules": { "unit-precedence": "off" } }"#).unwrap();
    assert_ne!(base, canonicalization_digest(&off));
    let attribute_off = Config::from_json(
        r#"{ "rules": { "unit-precedence": { "scopes": { "AttributeUsage": "off" } } } }"#,
    )
    .unwrap();
    assert_ne!(base, canonicalization_digest(&attribute_off));
    let constraint_off = Config::from_json(
        r#"{ "rules": { "unit-precedence": { "scopes": { "ConstraintUsage": "off" } } } }"#,
    )
    .unwrap();
    assert_eq!(base, canonicalization_digest(&constraint_off));
}

#[test]
fn a_unit_of_anonymous_elements_is_still_linted() {
    // No named element, so no declaration site to find the unit by —
    // the unit is still a user unit.
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_source(
        "t.sysml",
        "private import ISQ::*;\nprivate import SI::*;\nassert constraint { 3 [m] > 1 / 15 [km] }\n",
    );
    let mut resolved = ResolvedModel::build(&model);
    let findings = lint(&mut resolved, &Config::default());
    assert_eq!(precedence(&findings).len(), 1, "{findings:?}");
}

#[test]
fn a_bodiless_usage_inside_the_definition_does_not_take_its_body() {
    let (findings, _) = run_with_lib(
        "    attribute d : LengthValue = 3 [m];\n    \
         constraint def D { assert constraint inner : D; d > 1 / 15 [km] }\n",
        &Config::default(),
    );
    let p = precedence(&findings);
    assert_eq!(p.len(), 1, "{findings:?}");
    assert_eq!(p[0].element.as_deref(), Some("G::D"));
}
