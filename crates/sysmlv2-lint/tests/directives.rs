//! Suppression directives: the line, next-line and range forms, what
//! they suppress and what they leave, the `lint-directive` reports on
//! malformed and unused directives with their removal fixes, the
//! `reason` option, dormancy under an `off` rule, and the hosts' view
//! (`lint_outcome`, the sourceless `lint`).

use sysmlv2_lint::directive::{next_line_directive, next_line_directive_rules};
use sysmlv2_lint::{Config, Finding, Fix, RULES, RuleId, Severity, lint, lint_outcome, lint_units};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

/// Lint one unit with its text, as every host does.
fn run(src: &str, config: &Config) -> Vec<Finding> {
    outcome(src, config).findings
}

fn outcome(src: &str, config: &Config) -> sysmlv2_lint::Outcome {
    let mut model = Model::new();
    model.add_source("t.sysml", src);
    let mut resolved = ResolvedModel::build(&model);
    lint_outcome(&mut resolved, config, &[(0, "t.sysml", src)])
}

fn rule(findings: &[Finding], id: RuleId) -> Vec<&Finding> {
    findings.iter().filter(|f| f.rule == id).collect()
}

fn line_of(src: &str, f: &Finding) -> usize {
    src[..f.span.expect("located").start as usize]
        .matches('\n')
        .count()
        + 1
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

// `naming-convention` is on by default (info) and needs no library:
// a lowercase definition name is the finding under test throughout.
const TWO: &str = "package P {
    // sysmlint-disable-next-line naming-convention
    part def widget_one;
    part def widget_two;
}
";

#[test]
fn next_line_governs_exactly_the_following_line() {
    let findings = run(TWO, &Config::default());
    let naming = rule(&findings, RuleId::NamingConvention);
    assert_eq!(naming.len(), 1, "{findings:?}");
    assert_eq!(line_of(TWO, naming[0]), 4);
    assert!(
        rule(&findings, RuleId::LintDirective).is_empty(),
        "{findings:?}"
    );
}

#[test]
fn the_outcome_keeps_what_was_suppressed() {
    let o = outcome(TWO, &Config::default());
    assert_eq!(o.suppressed.len(), 1, "{o:?}");
    assert_eq!(o.suppressed[0].rule, RuleId::NamingConvention);
    assert_eq!(line_of(TWO, &o.suppressed[0]), 3);
    // The plain entry points report the same findings.
    let mut model = Model::new();
    model.add_source("t.sysml", TWO);
    let mut resolved = ResolvedModel::build(&model);
    let plain = lint_units(&mut resolved, &Config::default(), &[(0, "t.sysml", TWO)]);
    assert_eq!(plain.len(), o.findings.len());
}

#[test]
fn a_trailing_directive_governs_its_own_line() {
    let src = "package P {\n    part def widget_one; // sysmlint-disable-line naming-convention\n    part def widget_two;\n}\n";
    let findings = run(src, &Config::default());
    let naming = rule(&findings, RuleId::NamingConvention);
    assert_eq!(naming.len(), 1, "{findings:?}");
    assert_eq!(line_of(src, naming[0]), 3);
    assert!(
        rule(&findings, RuleId::LintDirective).is_empty(),
        "{findings:?}"
    );
}

#[test]
fn several_rules_and_a_reason_on_one_directive() {
    let cfg = Config::from_json(r#"{ "rules": { "unused-definition": "warn" } }"#).unwrap();
    let src = "package P {
    // sysmlint-disable-next-line naming-convention, unused-definition -- legacy name, consumed elsewhere
    part def widget_one;
    part def Wheel;
    part w : Wheel;
}
";
    let findings = run(src, &cfg);
    assert!(findings.is_empty(), "{findings:?}");
}

#[test]
fn a_block_note_is_a_directive_too() {
    let src = "package P {\n    //* sysmlint-disable-next-line naming-convention */\n    part def widget_one;\n}\n";
    let findings = run(src, &Config::default());
    assert!(findings.is_empty(), "{findings:?}");
}

#[test]
fn a_comment_body_is_never_a_directive() {
    // `/* … */` is a Comment element of the model, not a note.
    let src = "package P {\n    /* sysmlint-disable-next-line naming-convention */\n    part def widget_one;\n}\n";
    let findings = run(src, &Config::default());
    assert_eq!(
        rule(&findings, RuleId::NamingConvention).len(),
        1,
        "{findings:?}"
    );
    assert!(
        rule(&findings, RuleId::LintDirective).is_empty(),
        "{findings:?}"
    );
}

#[test]
fn strictly_the_next_line_and_an_unused_directive_warns_with_a_removal_fix() {
    let src = "package P {\n    // sysmlint-disable-next-line naming-convention\n\n    part def widget_one;\n}\n";
    let findings = run(src, &Config::default());
    assert_eq!(
        rule(&findings, RuleId::NamingConvention).len(),
        1,
        "{findings:?}"
    );
    let unused = rule(&findings, RuleId::LintDirective);
    assert_eq!(unused.len(), 1, "{findings:?}");
    let f = unused[0];
    assert_eq!(f.severity, Severity::Warn);
    assert_eq!(
        f.message,
        "`naming-convention` is not reported on line 3; the directive suppresses nothing"
    );
    assert_eq!(line_of(src, f), 2);
    let fix = f.fix.as_ref().expect("removal fix");
    assert!(fix.deletes && !fix.semantic);
    assert_eq!(fix.label, "remove the unused directive");
    assert_eq!(
        apply(src, fix),
        "package P {\n\n    part def widget_one;\n}\n"
    );
}

#[test]
fn removing_one_rule_keeps_the_rest_and_the_reason() {
    let cfg = Config::from_json(r#"{ "rules": { "unused-definition": "warn" } }"#).unwrap();
    let src = "package P {
    // sysmlint-disable-next-line naming-convention, unused-definition -- why
    part def Wheel;
    part w : Wheel;
}
";
    let findings = run(src, &cfg);
    let unused = rule(&findings, RuleId::LintDirective);
    assert_eq!(unused.len(), 2, "{findings:?}");
    let naming = unused
        .iter()
        .find(|f| f.message.starts_with("`naming-convention`"))
        .expect("the naming mention");
    let fix = naming.fix.as_ref().unwrap();
    assert_eq!(fix.label, "remove `naming-convention` from the directive");
    assert_eq!(
        apply(src, fix),
        "package P {\n    // sysmlint-disable-next-line unused-definition -- why\n    part def Wheel;\n    part w : Wheel;\n}\n"
    );
    // A trailing directive's removal takes the blank before it.
    let src = "package P {\n    part def Wheel; // sysmlint-disable-line naming-convention\n    part w : Wheel;\n}\n";
    let findings = run(src, &Config::default());
    let fix = rule(&findings, RuleId::LintDirective)[0]
        .fix
        .as_ref()
        .unwrap();
    assert_eq!(
        apply(src, fix),
        "package P {\n    part def Wheel;\n    part w : Wheel;\n}\n"
    );
}

#[test]
fn malformed_directives_are_reported_never_ignored() {
    let src = "package P {
    // sysmlint-disable-next-lines naming-convention
    part def widget_one;
    // sysmlint-disable-next-line no-such-rule, lint-config, naming-convention, naming-convention
    part def widget_two;
    // sysmlint-disable-next-line
    part def widget_three;
    // sysmlint-enable naming-convention
}
";
    let findings = run(src, &Config::default());
    let messages: Vec<&str> = rule(&findings, RuleId::LintDirective)
        .iter()
        .map(|f| f.message.as_str())
        .collect();
    assert_eq!(
        messages,
        [
            "`sysmlint-disable-next-lines` is not a lint directive; the directives are \
             `sysmlint-disable-next-line`, `sysmlint-disable-line`, `sysmlint-disable` and \
             `sysmlint-enable`",
            "unknown lint rule `no-such-rule`",
            "`lint-config` findings have no location and cannot be suppressed",
            "`naming-convention` is listed twice",
            "the directive names no rule; list the ids it governs, comma-separated",
            "`naming-convention` is not disabled here; nothing to re-enable",
        ],
        "{findings:?}"
    );
    // The misspelled verb suppressed nothing; the valid mention did its work.
    let naming = rule(&findings, RuleId::NamingConvention);
    assert_eq!(naming.len(), 2, "{findings:?}");
    assert_eq!(line_of(src, naming[0]), 3);
    assert_eq!(line_of(src, naming[1]), 7);
}

#[test]
fn a_range_runs_from_disable_through_enable_or_to_the_end() {
    let src = "package P {
    part def widget_one;
    // sysmlint-disable naming-convention
    part def widget_two;
    part def widget_three;
    // sysmlint-enable naming-convention
    part def widget_four;
    // sysmlint-disable naming-convention
    part def widget_five;
}
";
    let findings = run(src, &Config::default());
    let lines: Vec<usize> = rule(&findings, RuleId::NamingConvention)
        .iter()
        .map(|f| line_of(src, f))
        .collect();
    assert_eq!(lines, [2, 7], "{findings:?}");
    assert!(
        rule(&findings, RuleId::LintDirective).is_empty(),
        "{findings:?}"
    );
}

#[test]
fn an_unused_range_and_a_redundant_disable_are_reported() {
    let src = "package P {
    // sysmlint-disable naming-convention
    part def Wheel;
    // sysmlint-disable naming-convention
    part def Axle;
    // sysmlint-enable naming-convention
}
";
    let findings = run(src, &Config::default());
    let reports = rule(&findings, RuleId::LintDirective);
    let messages: Vec<&str> = reports.iter().map(|f| f.message.as_str()).collect();
    assert_eq!(
        messages,
        [
            "`naming-convention` is not reported between lines 2 and 6; the range suppresses nothing",
            "`naming-convention` is already disabled by the directive on line 2; this one suppresses nothing",
        ],
        "{findings:?}"
    );
    let fix = reports[0].fix.as_ref().unwrap();
    assert_eq!(fix.label, "remove the unused directive and its `enable`");
    assert_eq!(
        apply(src, fix),
        "package P {\n    part def Wheel;\n    // sysmlint-disable naming-convention\n    part def Axle;\n}\n"
    );
    assert_eq!(
        reports[1].fix.as_ref().unwrap().label,
        "remove the unused directive"
    );
    // Unmatched: the message says so.
    let src = "package P {\n    // sysmlint-disable naming-convention\n    part def Wheel;\n}\n";
    let findings = run(src, &Config::default());
    assert_eq!(
        rule(&findings, RuleId::LintDirective)[0].message,
        "`naming-convention` is not reported from line 2 on; the directive suppresses nothing"
    );
}

#[test]
fn the_earliest_covering_directive_takes_the_credit() {
    let src = "package P {
    // sysmlint-disable naming-convention
    // sysmlint-disable-next-line naming-convention
    part def widget_one;
    // sysmlint-enable naming-convention
}
";
    let findings = run(src, &Config::default());
    assert!(
        rule(&findings, RuleId::NamingConvention).is_empty(),
        "{findings:?}"
    );
    let reports = rule(&findings, RuleId::LintDirective);
    assert_eq!(reports.len(), 1, "{findings:?}");
    assert_eq!(line_of(src, reports[0]), 3);
}

#[test]
fn a_directive_for_an_off_rule_is_dormant() {
    let cfg = Config::from_json(r#"{ "rules": { "naming-convention": "off" } }"#).unwrap();
    let findings = run(TWO, &cfg);
    assert!(findings.is_empty(), "{findings:?}");
}

#[test]
fn directives_suppress_under_any_lint_directive_severity() {
    // Off silences the reports about directives, never the directives.
    let cfg = Config::from_json(r#"{ "rules": { "lint-directive": "off" } }"#).unwrap();
    let src = "package P {\n    // sysmlint-disable-next-line naming-convention\n    part def widget_one;\n    // sysmlint-disable-next-line naming-convention\n    part def Wheel;\n}\n";
    let findings = run(src, &cfg);
    assert!(findings.is_empty(), "{findings:?}");
    let cfg = Config::from_json(r#"{ "rules": { "lint-directive": "error" } }"#).unwrap();
    let findings = run(src, &cfg);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].severity, Severity::Error);
}

#[test]
fn the_reason_option_requires_a_reason() {
    let cfg = Config::from_json(r#"{ "rules": { "lint-directive": { "reason": "required" } } }"#)
        .unwrap();
    assert!(cfg.directive_reason_required());
    let findings = run(TWO, &cfg);
    let reports = rule(&findings, RuleId::LintDirective);
    assert_eq!(reports.len(), 1, "{findings:?}");
    assert_eq!(
        reports[0].message,
        "the directive gives no reason; add ` -- <why>` after the rule list"
    );
    assert!(reports[0].fix.is_none());
    let with_reason = TWO.replace(
        "naming-convention\n",
        "naming-convention -- a legacy name\n",
    );
    assert!(rule(&run(&with_reason, &cfg), RuleId::LintDirective).is_empty());
    // Optional by default, and a bad value is a configuration finding.
    assert!(!Config::default().directive_reason_required());
    let cfg =
        Config::from_json(r#"{ "rules": { "lint-directive": { "reason": "always" } } }"#).unwrap();
    let findings = run(TWO, &cfg);
    let complaints = rule(&findings, RuleId::LintConfig);
    assert_eq!(complaints.len(), 1, "{complaints:?}");
    assert!(
        complaints[0]
            .message
            .contains("must be `optional` or `required`")
    );
}

#[test]
fn the_inventory_advertises_the_rule_and_rejects_scopes() {
    let r = RuleId::LintDirective.rule().expect("configurable");
    assert_eq!(r.default, Severity::Warn);
    assert!(RULES.iter().any(|r| r.id == RuleId::LintDirective));
    assert_eq!(r.options.len(), 1);
    assert_eq!(r.options[0].key, "reason");
    let cfg = Config::from_json(
        r#"{ "rules": { "lint-directive": { "scopes": { "PartDefinition": "off" } } } }"#,
    )
    .unwrap();
    let findings = run(TWO, &cfg);
    let complaints = rule(&findings, RuleId::LintConfig);
    assert_eq!(complaints.len(), 1, "{complaints:?}");
}

#[test]
fn without_text_a_pass_cannot_see_directives() {
    let mut model = Model::new();
    model.add_source("t.sysml", TWO);
    let mut resolved = ResolvedModel::build(&model);
    let findings = lint(&mut resolved, &Config::default());
    assert_eq!(
        rule(&findings, RuleId::NamingConvention).len(),
        2,
        "{findings:?}"
    );
}

#[test]
fn hosts_write_and_extend_the_next_line_form() {
    assert_eq!(
        next_line_directive("unit-precedence"),
        "// sysmlint-disable-next-line unit-precedence"
    );
    let line = "    // sysmlint-disable-next-line naming-convention, unused-definition -- why";
    let (rules, at) = next_line_directive_rules(line).expect("a directive");
    assert_eq!(rules, ["naming-convention", "unused-definition"]);
    assert_eq!(
        &line[..at],
        "    // sysmlint-disable-next-line naming-convention, unused-definition"
    );
    let bare = "// sysmlint-disable-next-line";
    assert_eq!(next_line_directive_rules(bare), Some((vec![], bare.len())));
    assert!(next_line_directive_rules("    part def X; // a note").is_none());
    assert!(next_line_directive_rules("// sysmlint-disable-line naming-convention").is_none());
    assert!(next_line_directive_rules("// sysmlint-disable naming-convention").is_none());
    assert!(
        next_line_directive_rules("//* sysmlint-disable-next-line naming-convention */").is_none()
    );
}
