//! Rule-level gates: hit/miss per rule, severity config, scope maps,
//! style presets, config complaints, fix shapes, determinism.

use std::fmt::Write as _;
use sysmlv2_lint::{
    Config, Finding, LintError, RULES, RuleId, Severity, convert_to_style, lint, lint_with_sources,
};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

fn run(sources: &[(&str, &str)], config: &Config) -> Vec<Finding> {
    let mut model = Model::new();
    for (name, src) in sources {
        model.add_source(name.to_string(), src);
    }
    let mut resolved = ResolvedModel::build(&model);
    lint(&mut resolved, config)
}

const CALC: &str = "package P {
    attribute def Real;
    calc def T { in force : Real; in radius : Real; return t : Real = force * 2; }
}
";

const UNUSED_PARAM_ON: &str = r#"{ "rules": { "unused-parameter": "warn" } }"#;

#[test]
fn default_config_is_silent() {
    // Every rule defaults off or clean here: unused-parameter is off by
    // default (a policy opt-in), naming-convention defaults *info* but
    // CALC's names all satisfy the default styles, and CALC trips
    // nothing else.
    assert!(run(&[("a.sysml", CALC)], &Config::default()).is_empty());
}

#[test]
fn naming_convention_fires_at_info_by_default() {
    let findings = run(
        &[("a.sysml", "package P { part def widget; }")],
        &Config::default(),
    );
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "naming-convention");
    assert_eq!(findings[0].severity, Severity::Info);
}

#[test]
fn unused_parameter_flags_the_dead_input_with_a_deleting_fix() {
    let findings = run(
        &[("a.sysml", CALC)],
        &Config::from_json(UNUSED_PARAM_ON).unwrap(),
    );
    // `radius` is never used in the body and never referenced anywhere:
    // flagged, with a deletion fix over the whole member statement.
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = &findings[0];
    assert_eq!(f.rule, "unused-parameter");
    assert_eq!(f.severity, Severity::Warn);
    assert!(
        f.message.contains("`radius`") && f.message.contains("`T`"),
        "{}",
        f.message
    );
    assert_eq!(f.element.as_deref(), Some("P::T::radius"));
    let fix = f.fix.as_ref().expect("deletion fix");
    assert!(fix.deletes);
    assert_eq!(fix.edits.len(), 1);
    // The edit spans the member statement `in radius : Real;`.
    let e = &fix.edits[0];
    let src = CALC;
    let cut = &src[e.span.start as usize..e.span.end as usize];
    assert_eq!(cut, "in radius : Real;", "{cut:?}");
}

#[test]
fn unused_parameter_spares_call_site_only_parameters_of_a_fix() {
    // `radius` is passed by name at a call site but ignored by the
    // body: still a finding, but deleting it would strand the caller —
    // no fix.
    let src = "package P {
    attribute def Real;
    calc def T { in force : Real; in radius : Real; return t : Real = force * 2; }
    part sys { attribute m = T(force = 1, radius = 2); }
}
";
    let findings = run(
        &[("a.sysml", src)],
        &Config::from_json(UNUSED_PARAM_ON).unwrap(),
    );
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert!(
        findings[0].message.contains("outside"),
        "{}",
        findings[0].message
    );
    assert!(findings[0].fix.is_none());
}

#[test]
fn unused_parameter_scopes_toggle_each_definition_context() {
    let src = "package P {
    attribute def Real;
    constraint def NonNeg { in m : Real; in slack : Real; m >= 0 }
    action def Move { in dist : Real; }
}
";
    // Both contexts flag under an enabled base…
    let findings = run(
        &[("a.sysml", src)],
        &Config::from_json(UNUSED_PARAM_ON).unwrap(),
    );
    assert_eq!(findings.len(), 2, "{findings:?}");
    // …a scope silences just the action context…
    let cfg = Config::from_json(
        r#"{ "rules": { "unused-parameter": { "severity": "warn", "scopes": { "ActionDefinition": "off" } } } }"#,
    )
    .unwrap();
    let findings = run(&[("a.sysml", src)], &cfg);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert!(
        findings[0].message.contains("`slack`"),
        "{}",
        findings[0].message
    );
    // …and a scope escalates one context above the base.
    let cfg = Config::from_json(
        r#"{ "rules": { "unused-parameter": { "severity": "warn", "scopes": { "ActionDefinition": "error" } } } }"#,
    )
    .unwrap();
    let by_sev: Vec<Severity> = run(&[("a.sysml", src)], &cfg)
        .iter()
        .map(|f| f.severity)
        .collect();
    assert_eq!(
        by_sev,
        [Severity::Warn, Severity::Error],
        "constraint warn, action error"
    );
}

#[test]
fn severity_config_silences_and_escalates() {
    let mut cfg = Config::from_json(r#"{ "rules": { "unused-parameter": "off" } }"#).unwrap();
    assert!(run(&[("a.sysml", CALC)], &cfg).is_empty());
    cfg = Config::from_json(r#"{ "rules": { "unused-parameter": { "severity": "error" } } }"#)
        .unwrap();
    let findings = run(&[("a.sysml", CALC)], &cfg);
    assert_eq!(findings[0].severity, Severity::Error);
}

#[test]
fn info_and_hint_severities_parse_and_surface() {
    let src = "package P { part def Orphan; part chassis; }\n";
    let cfg = Config::from_json(
        r#"{ "rules": { "unused-definition": "hint", "untyped-usage": "info" } }"#,
    )
    .unwrap();
    let findings = run(&[("a.sysml", src)], &cfg);
    assert_eq!(findings.len(), 2, "{findings:?}");
    assert_eq!(findings[0].rule, "unused-definition");
    assert_eq!(findings[0].severity, Severity::Hint);
    assert_eq!(findings[1].rule, "untyped-usage");
    assert_eq!(findings[1].severity, Severity::Info);
    // The ladder orders by gravity.
    assert!(Severity::Hint < Severity::Info && Severity::Info < Severity::Warn);
}

#[test]
fn base_off_with_an_enabling_scope_runs_for_that_scope_only() {
    // unused-definition is off by default; one scope turns exactly one
    // stereotype on.
    let src = "package P {
    part def Orphan;
    attribute def Loose;
}
";
    assert!(run(&[("a.sysml", src)], &Config::default()).is_empty());
    let cfg = Config::from_json(
        r#"{ "rules": { "unused-definition": { "scopes": { "PartDefinition": "warn" } } } }"#,
    )
    .unwrap();
    let findings = run(&[("a.sysml", src)], &cfg);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert!(
        findings[0].message.contains("`Orphan`"),
        "{}",
        findings[0].message
    );
    assert_eq!(findings[0].element.as_deref(), Some("P::Orphan"));
}

#[test]
fn unknown_rule_ids_and_options_become_config_findings() {
    let cfg = Config::from_json(
        r#"{ "rules": { "no-such-rule": "warn", "unused-parameter": { "severity": "warn", "wat": 1 } } }"#,
    )
    .unwrap();
    let findings = run(&[("a.sysml", "package P;\n")], &cfg);
    let configs: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.rule == "lint-config")
        .collect();
    assert_eq!(configs.len(), 2, "{findings:?}");
    assert!(configs.iter().any(|f| f.message.contains("no-such-rule")));
    assert!(configs.iter().any(|f| f.message.contains("`wat`")));
}

#[test]
fn unknown_scope_keys_and_settings_become_config_findings() {
    let cfg = Config::from_json(
        r#"{ "rules": {
            "unused-parameter": { "scopes": { "PartDefinition": "off" } },
            "untyped-usage": { "scopes": { "PartUsage": { "depth": 2 } } } } }"#,
    )
    .unwrap();
    let findings = run(&[("a.sysml", "package P;\n")], &cfg);
    let msgs: Vec<&str> = findings
        .iter()
        .filter(|f| f.rule == "lint-config")
        .map(|f| f.message.as_str())
        .collect();
    assert_eq!(msgs.len(), 2, "{msgs:?}");
    // unused-parameter is strict about its three contexts…
    assert!(
        msgs.iter()
            .any(|m| m.contains("`PartDefinition`") && m.contains("not a known context")),
        "{msgs:?}"
    );
    // …and depth belongs to undocumented-element only.
    assert!(
        msgs.iter().any(|m| m.contains("unknown setting `depth`")),
        "{msgs:?}"
    );
}

#[test]
fn naming_convention_checks_both_families_with_default_styles() {
    let src = "package P {
    part def snake_wheel;
    part def Wheel;
    part GoodPart : Wheel;
    part axle : Wheel;
}
";
    // Info by default — the same findings fire as a nudge…
    let default_findings = run(&[("a.sysml", src)], &Config::default());
    assert_eq!(default_findings.len(), 2, "{default_findings:?}");
    assert!(
        default_findings
            .iter()
            .all(|f| f.severity == Severity::Info),
        "{default_findings:?}"
    );
    // …and configuring the rule sets the severity.
    let cfg = Config::from_json(r#"{ "rules": { "naming-convention": "warn" } }"#).unwrap();
    let findings = run(&[("a.sysml", src)], &cfg);
    assert_eq!(findings.len(), 2, "{findings:?}");
    assert_eq!(findings[0].rule, "naming-convention");
    assert!(
        findings[0].message.contains("`snake_wheel`") && findings[0].message.contains("PascalCase"),
        "{}",
        findings[0].message
    );
    // Preset styles carry a converted suggestion + the edit target.
    assert_eq!(findings[0].suggest.as_deref(), Some("SnakeWheel"));
    assert_eq!(findings[0].element.as_deref(), Some("P::snake_wheel"));
    assert!(
        findings[1].message.contains("`GoodPart`") && findings[1].message.contains("camelCase"),
        "{}",
        findings[1].message
    );
    assert_eq!(findings[1].suggest.as_deref(), Some("goodPart"));
}

#[test]
fn naming_convention_family_styles_and_regexes_configure() {
    let src = "package P { part def snake_wheel; part BigPart; }\n";
    // Definitions allowed snake_case (preset); usages must match a
    // custom regex (no preset → no suggestion).
    let cfg = Config::from_json(
        r#"{ "rules": { "naming-convention": {
            "severity": "warn",
            "definitions": "snake_case",
            "usages": { "regex": "^[A-Z0-9_]+$" } } } }"#,
    )
    .unwrap();
    let findings = run(&[("a.sysml", src)], &cfg);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert!(
        findings[0].message.contains("`BigPart`")
            && findings[0].message.contains("configured pattern"),
        "{}",
        findings[0].message
    );
    assert!(findings[0].suggest.is_none());
}

#[test]
fn naming_convention_scopes_override_style_and_severity_per_stereotype() {
    let src = "package P {
    enum def Palette { red; deepBlue; }
    part def Wheel;
    part Wagon : Wheel;
}
";
    // Enum literals must be UPPER_SNAKE_CASE; parts stop being checked.
    let cfg = Config::from_json(
        r#"{ "rules": { "naming-convention": { "severity": "warn", "scopes": {
            "EnumerationUsage": "UPPER_SNAKE_CASE",
            "PartUsage": "off" } } } }"#,
    )
    .unwrap();
    let findings = run(&[("a.sysml", src)], &cfg);
    let msgs: Vec<&str> = findings.iter().map(|f| f.message.as_str()).collect();
    // `Wagon` (PartUsage) is scoped off; both literals fail the scoped
    // style with converted suggestions.
    assert_eq!(findings.len(), 2, "{msgs:?}");
    assert!(
        msgs[0].contains("`red`") && msgs[0].contains("UPPER_SNAKE_CASE"),
        "{msgs:?}"
    );
    assert_eq!(findings[0].suggest.as_deref(), Some("RED"));
    assert_eq!(findings[1].suggest.as_deref(), Some("DEEP_BLUE"));

    // Object form: style + severity together.
    let cfg = Config::from_json(
        r#"{ "rules": { "naming-convention": { "severity": "warn", "scopes": {
            "EnumerationUsage": { "style": "UPPER_SNAKE_CASE", "severity": "error" },
            "PartUsage": "off" } } } }"#,
    )
    .unwrap();
    let findings = run(&[("a.sysml", src)], &cfg);
    assert_eq!(findings[0].severity, Severity::Error);
}

#[test]
fn naming_convention_bad_specs_complain_and_keep_defaults() {
    let cfg = Config::from_json(
        r#"{ "rules": { "naming-convention": {
            "severity": "warn",
            "definitions": { "regex": "([" },
            "scopes": { "PartUsage": "no-such-style" } } } }"#,
    )
    .unwrap();
    let findings = run(&[("a.sysml", "package P { part def bad_name; }\n")], &cfg);
    let configs: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.rule == "lint-config")
        .collect();
    assert_eq!(configs.len(), 2, "{findings:?}");
    assert!(
        configs[0].message.contains("regex is invalid")
            || configs[1].message.contains("regex is invalid")
    );
    // The default family style still applies.
    let naming: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.rule == "naming-convention")
        .collect();
    assert_eq!(naming.len(), 1);
    assert!(
        naming[0].message.contains("PascalCase"),
        "{}",
        naming[0].message
    );
}

/// A converted name a sibling already carries is not suggested: the
/// rename would leave two members of one namespace sharing a name.
/// The finding itself stays.
#[test]
fn naming_convention_withholds_suggestions_a_sibling_already_carries() {
    let src = "package P {
    part def Wheel;
    part def wheel;
    part def <'Axle'> spindle;
    part def axle;
    part def brake_disc;
}
";
    let findings = run(&[("a.sysml", src)], &Config::default());
    let naming: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.rule == "naming-convention")
        .collect();
    let by_target = |qn: &str| {
        naming
            .iter()
            .find(|f| f.element.as_deref() == Some(qn))
            .unwrap_or_else(|| panic!("no finding for {qn}: {naming:?}"))
    };
    assert_eq!(by_target("P::wheel").suggest, None);
    assert_eq!(by_target("P::axle").suggest, None);
    assert_eq!(
        by_target("P::brake_disc").suggest.as_deref(),
        Some("BrakeDisc")
    );
}

#[test]
fn style_conversion_covers_the_presets() {
    for (name, style, want) in [
        ("dead_wheel", "PascalCase", "DeadWheel"),
        ("dead_wheel", "camelCase", "deadWheel"),
        ("DeadWheel", "snake_case", "dead_wheel"),
        ("deepBlue", "UPPER_SNAKE_CASE", "DEEP_BLUE"),
        ("DeadWheel", "kebab-case", "dead-wheel"),
        ("mk2Rover", "PascalCase", "Mk2Rover"),
    ] {
        assert_eq!(
            convert_to_style(name, style).as_deref(),
            Some(want),
            "{name} → {style}"
        );
    }
}

#[test]
fn undocumented_element_flags_top_level_defs_when_enabled() {
    let src = "package P {
    part def Wheel { doc /* rolls */ }
    part def Axle;
    part def Frame { part def Tube; }
}
";
    // Off by default.
    assert!(
        run(&[("a.sysml", src)], &Config::default())
            .iter()
            .all(|f| f.rule != "undocumented-element")
    );
    let cfg = Config::from_json(r#"{ "rules": { "undocumented-element": "warn" } }"#).unwrap();
    let hits: Vec<Finding> = run(&[("a.sysml", src)], &cfg)
        .into_iter()
        .filter(|f| f.rule == "undocumented-element")
        .collect();
    // Wheel is documented; Tube is nested (depth 2, out of default scope).
    assert_eq!(hits.len(), 2, "{hits:?}");
    assert!(hits[0].message.contains("`Axle`"), "{hits:?}");
    assert!(hits[1].message.contains("`Frame`"), "{hits:?}");
    assert_eq!(hits[0].element.as_deref(), Some("P::Axle"));
}

#[test]
fn undocumented_element_scopes_tune_severity_and_depth() {
    let src = "package P {
    attribute def Mass;
    part def Frame { part def Tube; }
}
";
    // Base off; one scope enables part defs and deepens their coverage.
    let cfg = Config::from_json(
        r#"{ "rules": { "undocumented-element": { "scopes": {
            "PartDefinition": { "severity": "warn", "depth": 2 } } } } }"#,
    )
    .unwrap();
    let hits: Vec<String> = run(&[("a.sysml", src)], &cfg)
        .into_iter()
        .filter(|f| f.rule == "undocumented-element")
        .map(|f| f.message)
        .collect();
    // Mass (attribute def) inherits the off base; depth 2 pulls Tube in.
    assert_eq!(hits.len(), 2, "{hits:?}");
    assert!(
        hits[0].contains("`Frame`") && hits[1].contains("`Tube`"),
        "{hits:?}"
    );
}

#[test]
fn undocumented_element_counts_a_comment_written_about_the_target() {
    let src = "package P {
    part def Wheel;
    comment about Wheel /* documented from afar */
}
";
    let cfg = Config::from_json(r#"{ "rules": { "undocumented-element": "warn" } }"#).unwrap();
    let hits: Vec<Finding> = run(&[("a.sysml", src)], &cfg)
        .into_iter()
        .filter(|f| f.rule == "undocumented-element")
        .collect();
    assert!(hits.is_empty(), "{hits:?}");
}

#[test]
fn untyped_usage_flags_bare_usages_and_honors_default_scopes() {
    let src = "package P {
    part def Wheel;
    part wheel : Wheel;
    part chassis;
    part spare :> wheel;
    enum def Color { red; green; }
    state machine {
        state off;
        transition offToOn first off then on;
        state on;
    }
}
";
    // Off by default.
    assert!(
        run(&[("a.sysml", src)], &Config::default())
            .iter()
            .all(|f| f.rule != "untyped-usage")
    );
    let cfg = Config::from_json(r#"{ "rules": { "untyped-usage": "error" } }"#).unwrap();
    let hits: Vec<Finding> = run(&[("a.sysml", src)], &cfg)
        .into_iter()
        .filter(|f| f.rule == "untyped-usage")
        .collect();
    // wheel is typed, spare subsets, enum literals and the transition
    // sit on default-off scopes; chassis and the untyped states remain.
    let names: Vec<&str> = hits.iter().map(|f| f.message.as_str()).collect();
    assert_eq!(hits.len(), 4, "{names:?}");
    assert_eq!(hits[0].severity, Severity::Error);
    assert!(names[0].contains("`chassis`"), "{names:?}");
    assert!(names[1].contains("`machine`"), "{names:?}");
    assert!(names[2].contains("`off`"), "{names:?}");
    assert!(names[3].contains("`on`"), "{names:?}");
    assert!(!names.iter().any(|m| m.contains("offToOn")), "{names:?}");
}

#[test]
fn untyped_usage_scopes_silence_and_reenable_stereotypes() {
    let src = "package P {
    part chassis;
    item cargo;
    state machine { state off; transition go first off then off; }
}
";
    let cfg = Config::from_json(
        r#"{ "rules": { "untyped-usage": { "severity": "warn", "scopes": {
            "ItemUsage": "off",
            "StateUsage": "off",
            "TransitionUsage": "warn" } } } }"#,
    )
    .unwrap();
    let hits: Vec<String> = run(&[("a.sysml", src)], &cfg)
        .into_iter()
        .filter(|f| f.rule == "untyped-usage")
        .map(|f| f.message)
        .collect();
    // cargo and every state (incl. `machine` itself) are scoped off;
    // the default-off transition scope is re-enabled; `chassis`
    // inherits the warn base.
    assert_eq!(hits.len(), 2, "{hits:?}");
    assert!(hits[0].contains("`chassis`"), "{hits:?}");
    assert!(hits[1].contains("`go`"), "{hits:?}");
}

#[test]
fn option_objects_without_severity_keep_the_default_level() {
    // An options-only object neither complains nor changes severity —
    // the rule stays at its default (info), with the configured
    // pattern in effect.
    let cfg = Config::from_json(
        r#"{ "rules": { "naming-convention": { "usages": { "regex": "^[a-z_]+$" } } } }"#,
    )
    .unwrap();
    let findings = run(
        &[(
            "a.sysml",
            "package P { part def Wheel; part BigWheel : Wheel; }\n",
        )],
        &cfg,
    );
    // `Wheel` satisfies the definition-family default; `BigWheel`
    // trips the configured usage regex at the default info level.
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].severity, Severity::Info);
    assert!(findings[0].message.contains("`BigWheel`"), "{findings:?}");
}

#[test]
fn findings_are_deterministically_ordered_across_units() {
    let a = "package A { attribute def R; calc def C1 { in x : R; 0 } }\n";
    let b = "package B { attribute def S; calc def C2 { in y : S; 1 } }\n";
    let cfg = || Config::from_json(UNUSED_PARAM_ON).unwrap();
    let first = run(&[("a.sysml", a), ("b.sysml", b)], &cfg());
    let second = run(&[("a.sysml", a), ("b.sysml", b)], &cfg());
    let key = |fs: &[Finding]| -> Vec<(Option<usize>, Option<u32>, String)> {
        fs.iter()
            .map(|f| (f.unit, f.span.map(|s| s.start), f.message.clone()))
            .collect()
    };
    assert_eq!(key(&first), key(&second));
    assert_eq!(first.len(), 2);
    assert!(first[0].message.contains("`x`") && first[1].message.contains("`y`"));
}

// -- unit-spelling ------------------------------------------------------------

const MIXED_SPELLINGS: &str = "package P {
    attribute m; attribute s;
    attribute <'m⋅s⁻¹'> mps;
    attribute a = 1 ['m⋅s⁻¹'];
    attribute b = 2 ['m⋅s⁻¹'];
    attribute c = 3 [m/s];
}
";

#[test]
fn unit_spelling_flags_the_minority_spelling_with_a_respelling_fix() {
    let findings = run(
        &[("a.sysml", MIXED_SPELLINGS)],
        &Config::from_json(r#"{ "rules": { "unit-spelling": "warn" } }"#).unwrap(),
    );
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = &findings[0];
    assert_eq!(f.rule, "unit-spelling");
    assert_eq!(f.severity, Severity::Warn);
    assert!(
        f.message.contains("`m/s`") && f.message.contains("`'m⋅s⁻¹'`"),
        "{}",
        f.message
    );
    assert_eq!(f.element.as_deref(), Some("P::c"));
    let fix = f.fix.as_ref().expect("re-spelling fix");
    assert!(!fix.deletes);
    let e = &fix.edits[0];
    let cut = &MIXED_SPELLINGS[e.span.start as usize..e.span.end as usize];
    assert_eq!(cut, "m/s", "{cut:?}");
    assert_eq!(e.replacement, "'m⋅s⁻¹'");
}

#[test]
fn unit_spelling_default_and_consistent_models_are_silent() {
    // Rule off by default.
    assert!(run(&[("a.sysml", MIXED_SPELLINGS)], &Config::default()).is_empty());
    // One spelling only: nothing to flag, even with the rule on.
    let consistent = "package P {
        attribute m; attribute s;
        attribute a = 1 [m/s];
        attribute b = 2 [m/s];
        attribute plain = 3 [m];
    }
    ";
    let findings = run(
        &[("a.sysml", consistent)],
        &Config::from_json(r#"{ "rules": { "unit-spelling": "warn" } }"#).unwrap(),
    );
    assert!(findings.is_empty(), "{findings:?}");
}

#[test]
fn unit_spelling_style_enforces_the_preferred_form() {
    // expression style: the quoted product names flag, with fixes.
    let quoted_only = "package P {
        attribute m; attribute s;
        attribute <'m⋅s⁻¹'> mps;
        attribute a = 1 ['m⋅s⁻¹'];
        attribute plain = 3 [m];
    }
    ";
    let findings = run(
        &[("a.sysml", quoted_only)],
        &Config::from_json(
            r#"{ "rules": { "unit-spelling": { "severity": "info", "style": "expression" } } }"#,
        )
        .unwrap(),
    );
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = &findings[0];
    assert_eq!(f.severity, Severity::Info);
    assert!(f.message.contains("unit expression"), "{}", f.message);
    assert_eq!(
        f.fix
            .as_ref()
            .and_then(|x| x.edits.first())
            .map(|e| e.replacement.as_str()),
        Some("m/s")
    );

    // quoted-product style: the expression spelling flags, fix quotes it.
    let expr_only = "package P {
        attribute m; attribute s;
        attribute a = 1 [m/s**2];
        attribute plain = 3 [m];
    }
    ";
    let findings = run(
        &[("a.sysml", expr_only)],
        &Config::from_json(
            r#"{ "rules": { "unit-spelling": { "severity": "warn", "style": "quoted-product" } } }"#,
        )
        .unwrap(),
    );
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(
        findings[0]
            .fix
            .as_ref()
            .and_then(|x| x.edits.first())
            .map(|e| e.replacement.as_str()),
        Some("'m⋅s⁻²'")
    );
}

#[test]
fn unit_spelling_style_rejects_unknown_names() {
    let findings = run(
        &[("a.sysml", "package P { attribute m; attribute a = 1 [m]; }")],
        &Config::from_json(
            r#"{ "rules": { "unit-spelling": { "severity": "warn", "style": "fancy" } } }"#,
        )
        .unwrap(),
    );
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "lint-config");
    assert!(
        findings[0].message.contains("quoted-product"),
        "{}",
        findings[0].message
    );
}

const CHAINS: &str = "package Q {
    attribute def Real;
    constraint def C {
        attribute a : Real;
        attribute b : Real;
        attribute c : Real;
        assert constraint { a > 0.0 and b > 0.0 and c > 0.0 }
        assert constraint { a > 0.0 and b > 0.0 }
        assert constraint {
            a > 0.0
            and b > 0.0
            and c > 0.0
        }
    }
}
";

#[test]
fn multiline_conditions_flags_single_line_chains_only() {
    let on = r#"{ "rules": { "multiline-conditions": "warn" } }"#;
    let findings = run(&[("a.sysml", CHAINS)], &Config::from_json(on).unwrap());
    // One finding: the 3-operand chain on one line. The 2-operand chain
    // is under the threshold and the already-broken chain is fine.
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = &findings[0];
    assert_eq!(f.rule, "multiline-conditions");
    assert!(
        f.message.contains("3-condition `and` chain"),
        "{}",
        f.message
    );
    assert!(f.fix.is_none(), "no auto-fix — Format Document is the fix");

    // `min` raises the threshold…
    let min4 = r#"{ "rules": { "multiline-conditions": { "severity": "warn", "min": 4 } } }"#;
    let cfg = Config::from_json(min4).unwrap();
    assert!(run(&[("a.sysml", CHAINS)], &cfg).is_empty());
    assert_eq!(
        cfg.format_chain_min(),
        Some(4),
        "the formatter shares the threshold"
    );

    // …and 0 keeps chains inline everywhere (formatter included).
    let off = r#"{ "rules": { "multiline-conditions": { "severity": "warn", "min": 0 } } }"#;
    let cfg = Config::from_json(off).unwrap();
    assert!(run(&[("a.sysml", CHAINS)], &cfg).is_empty());
    assert_eq!(cfg.format_chain_min(), None);
}

// ---- the textual tier: `indentation` ----

/// [`run`] for the textual tier: the same model, plus the unit texts the
/// host would hold.
fn run_text(sources: &[(&str, &str)], config: &Config) -> Vec<Finding> {
    let mut model = Model::new();
    for (name, src) in sources {
        model.add_source(name.to_string(), src);
    }
    let mut resolved = ResolvedModel::build(&model);
    let texts: Vec<(usize, &str)> = sources
        .iter()
        .enumerate()
        .map(|(i, (_, src))| (i, *src))
        .collect();
    lint_with_sources(&mut resolved, config, &texts)
}

/// Four-space indentation throughout — canonical printer style, and
/// three findings under the tabs default (the inner `}` included; the
/// outer one sits at column 0).
const SPACED: &str = "package P {
    part def Wheel {
        attribute size;
    }
}
";

#[test]
fn indentation_defaults_to_tabs_and_fixes_each_offending_line() {
    let on = r#"{ "rules": { "indentation": "warn" } }"#;
    let cfg = Config::from_json(on).unwrap();
    assert_eq!(
        cfg.format_indent(),
        sysmlv2_parser::print::Indent::Tabs,
        "tabs is the default style, and the formatter shares it"
    );
    let findings = run_text(&[("a.sysml", SPACED)], &cfg);
    // Every indented line: `part def`, `attribute`, and the inner `}`.
    assert_eq!(findings.len(), 3, "{findings:?}");
    let f = &findings[0];
    assert_eq!(f.rule, "indentation");
    assert_eq!(f.severity, Severity::Warn);
    assert!(
        f.message.contains("4 spaces") && f.message.contains("tabs"),
        "{}",
        f.message
    );
    assert!(f.element.is_none(), "a line is not an element");
    // The fix replaces the leading whitespace only, one tab per level.
    let fix = f.fix.as_ref().expect("re-indent fix");
    assert!(!fix.deletes);
    let e = &fix.edits[0];
    assert_eq!(&SPACED[e.span.start as usize..e.span.end as usize], "    ");
    assert_eq!(e.replacement, "\t");
    // …two levels deep, two tabs.
    let deep = findings[1].fix.as_ref().unwrap();
    assert_eq!(deep.edits[0].replacement, "\t\t");

    // Tab-indented text is silent under the default.
    let tabbed = SPACED.replace("        ", "\t\t").replace("    ", "\t");
    assert!(
        run_text(&[("a.sysml", &tabbed)], &cfg).is_empty(),
        "{tabbed:?}"
    );
}

#[test]
fn indentation_spaces_style_flags_tabs_and_odd_widths() {
    let two = r#"{ "rules": { "indentation": { "severity": "error", "style": "spaces",
                  "size": 2 } } }"#;
    let cfg = Config::from_json(two).unwrap();
    assert_eq!(
        cfg.format_indent(),
        sysmlv2_parser::print::Indent::Spaces(2)
    );
    let src = "package P {
  part def Wheel {
\tattribute size;
   attribute mass;
  }
}
";
    let findings = run_text(&[("a.sysml", src)], &cfg);
    // The tab and the 3-space line; the 2-space lines conform.
    assert_eq!(findings.len(), 2, "{findings:?}");
    assert_eq!(findings[0].severity, Severity::Error);
    assert!(
        findings[0].message.contains("1 tab"),
        "{}",
        findings[0].message
    );
    assert_eq!(findings[0].fix.as_ref().unwrap().edits[0].replacement, "  ");
    assert!(
        findings[1]
            .message
            .contains("not a multiple of this project's 2"),
        "{}",
        findings[1].message
    );
    // 3 columns rounds to two levels — an indented line never dedents
    // to column 0.
    assert_eq!(
        findings[1].fix.as_ref().unwrap().edits[0].replacement,
        "    "
    );
}

#[test]
fn indentation_spares_verbatim_bodies_and_blank_lines() {
    // A documentation body and a multi-line note the formatter
    // reproduces byte for byte, plus a whitespace-only line.
    let src = "package P {
\tdoc /* first
    second, space-indented inside the body
\t*/
\t
\tpart def Wheel;
\t//* a note
       continued
\t*/
}
";
    let on = r#"{ "rules": { "indentation": "warn" } }"#;
    let findings = run_text(&[("a.sysml", src)], &Config::from_json(on).unwrap());
    assert!(findings.is_empty(), "{findings:?}");
}

#[test]
fn indentation_is_off_by_default_and_needs_source_text() {
    // Off like every other rule: policy is opt-in.
    assert!(run_text(&[("a.sysml", SPACED)], &Config::default()).is_empty());

    // Enabled but text-less (a host that did not wire the tier): a
    // configuration finding, never a silent pass.
    let on = r#"{ "rules": { "indentation": "warn" } }"#;
    let findings = run(&[("a.sysml", SPACED)], &Config::from_json(on).unwrap());
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "lint-config");
    assert!(
        findings[0].message.contains("source text"),
        "{}",
        findings[0].message
    );
}

#[test]
fn indentation_bad_options_complain_and_keep_the_defaults() {
    let bad = r#"{ "rules": { "indentation": { "severity": "warn", "style": "wide",
                  "size": 0, "scopes": { "PartDefinition": "off" } } } }"#;
    let cfg = Config::from_json(bad).unwrap();
    assert_eq!(
        cfg.format_indent(),
        sysmlv2_parser::print::Indent::Tabs,
        "defaults survive"
    );
    let findings = run_text(&[("a.sysml", SPACED)], &cfg);
    let complaints: Vec<&str> = findings
        .iter()
        .filter(|f| f.rule == "lint-config")
        .map(|f| f.message.as_str())
        .collect();
    assert_eq!(complaints.len(), 3, "{complaints:?}");
    assert!(
        complaints.iter().any(|c| c.contains("`tabs` or `spaces`")),
        "{complaints:?}"
    );
    assert!(
        complaints.iter().any(|c| c.contains("positive integer")),
        "{complaints:?}"
    );
    assert!(
        complaints.iter().any(|c| c.contains("not a known context")),
        "{complaints:?}"
    );
    // The rule still ran with its defaults.
    assert_eq!(
        findings.iter().filter(|f| f.rule == "indentation").count(),
        3
    );
}

// ---------------------------------------------------------------------------
// import-visibility: the keyword an import's dependents require
// ---------------------------------------------------------------------------

const IMPORT_LIB: &str = "package Lib { part def Thing; }\n";

fn import_visibility_finding(sources: &[(&str, &str)]) -> Finding {
    let findings: Vec<Finding> = run(sources, &Config::default())
        .into_iter()
        .filter(|f| f.rule == "import-visibility")
        .collect();
    assert_eq!(findings.len(), 1, "{findings:?}");
    findings.into_iter().next().unwrap()
}

#[test]
fn import_visibility_recommends_private_when_only_the_importer_uses_it() {
    // A nested package resolves through the enclosing package's import
    // lexically, so it does not need the import to be visible.
    let f = import_visibility_finding(&[
        ("lib.sysml", IMPORT_LIB),
        (
            "p.sysml",
            "package P {\n    import Lib::*;\n    part a : Thing;\n    package Child { part c : Thing; }\n}\n",
        ),
    ]);
    assert_eq!(f.severity, Severity::Info);
    assert!(f.message.contains("`private` suffices"), "{}", f.message);
    assert!(f.message.contains("`P`"), "{}", f.message);
    let fix = f.fix.as_ref().expect("computed fix");
    assert_eq!(fix.label, "Make the import `private`");
    assert!(!fix.semantic && !fix.deletes);
    assert_eq!(fix.edits.len(), 1);
    assert_eq!(fix.edits[0].unit, 1);
    assert_eq!(fix.edits[0].replacement, "private ");
    assert_eq!(fix.edits[0].span.start, fix.edits[0].span.end);
    // The keyword lands where the member starts: `private import Lib::*;`.
    assert_eq!(fix.edits[0].span.start, "package P {\n    ".len() as u32);
    let labels: Vec<&str> = f.alternatives.iter().map(|a| a.label.as_str()).collect();
    assert_eq!(
        labels,
        ["Make the import `protected`", "Make the import `public`"]
    );
    assert!(f.alternatives.iter().all(|a| a.semantic));
}

#[test]
fn import_visibility_recommends_public_when_an_outside_reference_depends_on_it() {
    // `P::Thing` reaches Lib::Thing only through P's import: a private
    // keyword would break Q.
    let f = import_visibility_finding(&[
        ("lib.sysml", IMPORT_LIB),
        ("p.sysml", "package P { import Lib::*; }\n"),
        ("q.sysml", "package Q { part b : P::Thing; }\n"),
    ]);
    assert!(
        f.message.contains("`public` is required") && f.message.contains("1 reference(s)"),
        "{}",
        f.message
    );
    assert_eq!(f.fix.as_ref().unwrap().label, "Make the import `public`");
    assert_eq!(f.suggest.as_deref(), Some("public"));
}

#[test]
fn import_visibility_recommends_protected_for_a_type_used_by_its_specializations() {
    let f = import_visibility_finding(&[
        ("lib.sysml", IMPORT_LIB),
        (
            "p.sysml",
            "package P {\n    part def Base { import Lib::*; }\n    part def Sub :> Base { part t : Thing; }\n}\n",
        ),
    ]);
    assert!(
        f.message.contains("`protected` is required"),
        "{}",
        f.message
    );
    assert_eq!(f.fix.as_ref().unwrap().label, "Make the import `protected`");
}

#[test]
fn reference_sites_record_the_imports_they_resolved_through() {
    let mut model = Model::new();
    model.add_source("lib.sysml".to_string(), IMPORT_LIB);
    model.add_source(
        "p.sysml".to_string(),
        "package P { import Lib::*; part a : Thing; part b : Lib::Thing; }\n",
    );
    let resolved = ResolvedModel::build(&model);
    let imports = resolved.imports_without_visibility();
    assert_eq!(imports.len(), 1);
    let import = imports[0].0;
    let sites: Vec<_> = resolved
        .reference_sites()
        .iter()
        .filter(|s| s.unit == 1 && s.kind == "type")
        .map(|s| (s.span.start, s.via_imports.clone()))
        .collect();
    assert_eq!(sites.len(), 2, "{sites:?}");
    // `Thing` resolved through the import, lexically (full access);
    // `Lib::Thing` did not.
    assert_eq!(
        sites[0].1,
        [(import, sysmlv2_parser::json::AccessMode::Any)]
    );
    assert!(sites[1].1.is_empty(), "{sites:?}");
}

#[test]
fn import_visibility_sees_re_exports_membership_imports_and_import_targets() {
    // A namespace import of P re-exports P's bare import: the walk into
    // P ran under public access, so `private` would break Q.
    let f = import_visibility_finding(&[
        ("lib.sysml", IMPORT_LIB),
        ("p.sysml", "package P { import Lib::*; }\n"),
        (
            "q.sysml",
            "package Q { private import P::*; part b : Thing; }\n",
        ),
    ]);
    assert_eq!(f.fix.as_ref().unwrap().label, "Make the import `public`");
    // A membership import records like a namespace import.
    let f = import_visibility_finding(&[
        ("lib.sysml", IMPORT_LIB),
        (
            "p.sysml",
            "package P { import Lib::Thing; part a : Thing; }\n",
        ),
    ]);
    assert_eq!(f.fix.as_ref().unwrap().label, "Make the import `private`");
    // An import whose own target resolves only through another import
    // depends on that import, even when the import cache was filled by
    // an earlier lookup in the same scope.
    let f = import_visibility_finding(&[
        ("a.sysml", "package A { package B { part def C; } }\n"),
        ("p.sysml", "package P { import A::*; }\n"),
        (
            "q.sysml",
            "package Q { part z : Nope; private import P::*; private import B::*; part c : C; }\n",
        ),
    ]);
    assert_eq!(f.fix.as_ref().unwrap().label, "Make the import `public`");
}

#[test]
fn import_visibility_stays_quiet_on_an_unresolved_import() {
    let findings: Vec<Finding> = run(
        &[("p.sysml", "package P { import Nope::*; }\n")],
        &Config::default(),
    )
    .into_iter()
    .filter(|f| f.rule == "import-visibility")
    .collect();
    assert!(findings.is_empty(), "{findings:?}");
}

// ---------------------------------------------------------------------------
// visibility-blocked-reference: a private member behind an unresolved name
// ---------------------------------------------------------------------------

const BLOCKED: &str = "package P {
    constraint def MaxTime { private port maxTime; }
    part def Req {
        constraint c : MaxTime;
        attribute limit;
        bind c.maxTime = limit;
    }
}
";

fn run_with_sources(sources: &[(&str, &str)], config: &Config) -> Vec<Finding> {
    let mut model = Model::new();
    for (name, src) in sources {
        model.add_source(name.to_string(), src);
    }
    let mut resolved = ResolvedModel::build(&model);
    let texts: Vec<(usize, &str)> = sources
        .iter()
        .enumerate()
        .map(|(i, (_, s))| (i, *s))
        .collect();
    lint_with_sources(&mut resolved, config, &texts)
}

#[test]
fn visibility_blocked_reference_offers_to_widen_the_member() {
    let findings: Vec<Finding> = run_with_sources(&[("a.sysml", BLOCKED)], &Config::default())
        .into_iter()
        .filter(|f| f.rule == "visibility-blocked-reference")
        .collect();
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = &findings[0];
    assert_eq!(
        f.message,
        "`c.maxTime` does not resolve — `P::MaxTime::maxTime` exists but is private"
    );
    assert_eq!(f.element.as_deref(), Some("P::MaxTime::maxTime"));
    let fix = f.fix.as_ref().expect("widening fix");
    assert_eq!(fix.label, "make `P::MaxTime::maxTime` public");
    assert!(fix.semantic);
    assert_eq!(fix.edits.len(), 1);
    let e = &fix.edits[0];
    assert_eq!(
        &BLOCKED[e.span.start as usize..e.span.end as usize],
        "private"
    );
    assert_eq!(e.replacement, "public");
    // `Req` does not specialize `MaxTime`, so `protected` would not help.
    assert!(f.alternatives.is_empty(), "{:?}", f.alternatives);
    // Applying the fix makes the reference resolve.
    let fixed = format!(
        "{}public{}",
        &BLOCKED[..e.span.start as usize],
        &BLOCKED[e.span.end as usize..]
    );
    let again = run_with_sources(&[("a.sysml", &fixed)], &Config::default());
    assert!(
        again
            .iter()
            .all(|f| f.rule != "visibility-blocked-reference"),
        "{again:?}"
    );
    let mut model = Model::new();
    model.add_source("a.sysml".to_string(), &fixed);
    let resolved = ResolvedModel::build(&model);
    assert!(resolved.unresolved_references().is_empty());
}

#[test]
fn visibility_blocked_reference_covers_inherited_and_qualified_members() {
    let src = "package P {
    part def Base { private attribute v; }
    part def Sub :> Base { attribute :>> v = 1; }
    part def Other { attribute w = Base::v; }
}
";
    let mut model = Model::new();
    model.add_source("a.sysml".to_string(), src);
    let resolved = ResolvedModel::build(&model);
    let blocked = resolved.blocked_references();
    let names: Vec<&str> = blocked.iter().map(|b| b.spelling.as_str()).collect();
    assert_eq!(names, ["v", "Base::v"], "{blocked:?}");
    assert!(blocked.iter().all(|b| b.visibility == "private"));
    // The redefinition reaches `v` through the specialization, so
    // `protected` suffices there; the qualified reference from `Other`
    // needs `public`.
    assert_eq!(
        blocked
            .iter()
            .map(|b| b.protected_suffices)
            .collect::<Vec<_>>(),
        [true, false]
    );
    let findings = rule_findings_in(src, "visibility-blocked-reference");
    let alternatives: Vec<usize> = findings.iter().map(|f| f.alternatives.len()).collect();
    assert_eq!(alternatives, [1, 0], "{findings:?}");
    // A plain absent name is not blocked.
    let mut model = Model::new();
    model.add_source("b.sysml".to_string(), "package Q { part x : Nope; }");
    assert!(ResolvedModel::build(&model).blocked_references().is_empty());
}

fn rule_findings_in(src: &str, rule: &str) -> Vec<Finding> {
    run_with_sources(&[("a.sysml", src)], &Config::default())
        .into_iter()
        .filter(|f| f.rule == rule)
        .collect()
}

#[test]
fn visibility_blocked_reference_reports_protected_members_and_skips_deeper_paths() {
    // A protected member reached from outside any specialization.
    let src = "package P {
    part def T { protected attribute m; }
    part def U { attribute x = T::m; }
}
";
    let findings = rule_findings_in(src, "visibility-blocked-reference");
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = &findings[0];
    assert!(
        f.message.ends_with("exists but is protected"),
        "{}",
        f.message
    );
    assert_eq!(f.fix.as_ref().unwrap().label, "make `P::T::m` public");
    assert!(f.alternatives.is_empty());
    // A path through two hidden members: widening the last one alone
    // would not make the reference resolve, so nothing is offered.
    let deep = "package A { private package B { private part def C; } }
package Q { part u : A::B::C; }
";
    assert!(rule_findings_in(deep, "visibility-blocked-reference").is_empty());
    let mut model = Model::new();
    model.add_source("a.sysml".to_string(), deep);
    let resolved = ResolvedModel::build(&model);
    assert!(resolved.blocked_references().is_empty());
    assert_eq!(resolved.unresolved_references().len(), 1);
}

#[test]
fn visibility_probes_never_change_what_resolves() {
    // Q's reference is resolved first and its probe is the first lookup
    // to touch B's scope; B's own import must still fail to resolve
    // (Hidden is private to Outer) and `h : H` stay unresolved.
    // `c` is reachable from `B` only through that import, so the probe's
    // lookup of `c` must consult (and would otherwise fill) B's import
    // cache.
    let src = "package Q { part u : A::B::c; }
package Outer { private package Hidden { part def H; part def c; } }
package A { private package B { import Outer::Hidden::*; part h : H; } }
";
    let mut model = Model::new();
    model.add_source("a.sysml".to_string(), src);
    let resolved = ResolvedModel::build(&model);
    let unresolved: Vec<String> = resolved
        .unresolved_references()
        .iter()
        .map(|u| u.spelling.clone())
        .collect();
    assert!(unresolved.contains(&"H".to_string()), "{unresolved:?}");
    assert!(
        unresolved.contains(&"Outer::Hidden".to_string()),
        "{unresolved:?}"
    );
    assert!(
        unresolved.contains(&"A::B::c".to_string()),
        "{unresolved:?}"
    );
}

// ---------------------------------------------------------------------------
// M32d: kind and referential fixes
// ---------------------------------------------------------------------------

fn rule_findings(sources: &[(&str, &str)], rule: &str) -> Vec<Finding> {
    run_with_sources(sources, &Config::default())
        .into_iter()
        .filter(|f| f.rule == rule)
        .collect()
}

fn apply_fix(text: &str, fix: &sysmlv2_lint::Fix) -> String {
    let mut out = text.to_string();
    let mut edits = fix.edits.clone();
    edits.sort_by_key(|e| std::cmp::Reverse(e.span.start));
    for e in edits {
        out.replace_range(e.span.start as usize..e.span.end as usize, &e.replacement);
    }
    out
}

#[test]
fn usage_kind_mismatch_rewrites_the_usage_keyword() {
    let src = "package P {\n    port def Pd;\n    part def A {\n        private attribute p : Pd;\n    }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "usage-kind-mismatch");
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = &findings[0];
    assert_eq!(
        f.message,
        "AttributeUsage must be typed by DataType; `P::Pd` is a PortDefinition"
    );
    assert_eq!(f.element.as_deref(), Some("P::A::p"));
    let fix = f.fix.as_ref().expect("keyword fix");
    assert_eq!(fix.label, "change `attribute` to `port`");
    assert!(fix.semantic);
    assert_eq!(
        &src[fix.edits[0].span.start as usize..fix.edits[0].span.end as usize],
        "attribute"
    );
    let fixed = apply_fix(src, fix);
    assert!(fixed.contains("private port p : Pd;"), "{fixed}");
    assert!(rule_findings(&[("a.sysml", &fixed)], "usage-kind-mismatch").is_empty());
    // A compatible typing is not a finding.
    let ok = "package P { part def A; item def I; part def B { part a : A; part i : I; } }\n";
    assert!(rule_findings(&[("b.sysml", ok)], "usage-kind-mismatch").is_empty());
    // The most specific definition kind names the keyword: a requirement
    // definition is also a constraint definition, a calculation
    // definition also an action definition.
    let specific = "package P {\n    requirement def R;\n    calc def C;\n    part def A { attribute r : R; attribute c : C; }\n}\n";
    let labels: Vec<String> = rule_findings(&[("c.sysml", specific)], "usage-kind-mismatch")
        .iter()
        .filter_map(|f| f.fix.as_ref().map(|x| x.label.clone()))
        .collect();
    assert_eq!(
        labels,
        [
            "change `attribute` to `requirement`",
            "change `attribute` to `calc`"
        ]
    );
    // Severity is informational: the semantic check already errors.
    assert_eq!(findings[0].severity, Severity::Info);
}

#[test]
fn port_member_referential_inserts_ref() {
    let src = "package P {\n    item def Cmd;\n    part def A {\n        port q {\n            item cmd : Cmd;\n            ref item ok : Cmd;\n        }\n    }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "port-member-referential");
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = &findings[0];
    assert_eq!(f.element.as_deref(), Some("P::A::q::cmd"));
    let fix = f.fix.as_ref().expect("ref fix");
    assert!(!fix.semantic && !fix.deletes);
    let fixed = apply_fix(src, fix);
    assert!(fixed.contains("            ref item cmd : Cmd;"), "{fixed}");
    assert!(rule_findings(&[("a.sysml", &fixed)], "port-member-referential").is_empty());
    // A port definition's own members, prefixes before the keyword, and
    // `ref` placed before `individual` (the grammar reads it first).
    let more = "package P {\n    item def Cmd;\n    port def Pd {\n        private abstract item a : Cmd;\n        individual item i : Cmd;\n        in item p : Cmd;\n    }\n}\n";
    let findings = rule_findings(&[("b.sysml", more)], "port-member-referential");
    let fixed: Vec<String> = findings
        .iter()
        .map(|f| apply_fix(more, f.fix.as_ref().unwrap()))
        .collect();
    assert_eq!(fixed.len(), 2, "{findings:?}");
    assert!(
        fixed[0].contains("private abstract ref item a : Cmd;"),
        "{}",
        fixed[0]
    );
    assert!(
        fixed[1].contains("ref individual item i : Cmd;"),
        "{}",
        fixed[1]
    );
    assert_eq!(findings[0].severity, Severity::Info);
}

#[test]
fn unqualified_enum_literal_qualifies_a_unique_match() {
    let src = "package P {\n    enum def Mode { TRACK; SLEW; }\n    part def A {\n        attribute m : Mode;\n        constraint valid { m == TRACK }\n    }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "unqualified-enum-literal");
    assert_eq!(findings.len(), 1, "{findings:?}");
    let f = &findings[0];
    assert_eq!(f.suggest.as_deref(), Some("P::Mode::TRACK"));
    let fix = f.fix.as_ref().expect("qualify fix");
    assert_eq!(fix.label, "qualify as `P::Mode::TRACK`");
    let fixed = apply_fix(src, fix);
    assert!(fixed.contains("m == P::Mode::TRACK"), "{fixed}");
    let mut model = Model::new();
    model.add_source("a.sysml".to_string(), &fixed);
    assert!(
        ResolvedModel::build(&model)
            .unresolved_references()
            .is_empty()
    );
    // Two literals of that name: no fix, no finding.
    let two = "package P {\n    enum def A { X; }\n    enum def B { X; }\n    part def C { attribute v = X; }\n}\n";
    assert!(rule_findings(&[("b.sysml", two)], "unqualified-enum-literal").is_empty());
    // A restricted-name literal is matched by its escaped spelling and
    // spliced as reference text that re-parses.
    let restricted = "package P {\n    enum def State { 'Not Accepted'; Accepted; }\n    part def A { attribute s = 'Not Accepted'; }\n}\n";
    let findings = rule_findings(&[("c.sysml", restricted)], "unqualified-enum-literal");
    assert_eq!(findings.len(), 1, "{findings:?}");
    let fixed = apply_fix(restricted, findings[0].fix.as_ref().unwrap());
    assert!(
        fixed.contains("attribute s = P::State::'Not Accepted';"),
        "{fixed}"
    );
    let mut model = Model::new();
    model.add_source("c.sysml".to_string(), &fixed);
    assert!(
        ResolvedModel::build(&model)
            .unresolved_references()
            .is_empty()
    );
}

#[test]
fn unresolved_references_survive_a_referential_check() {
    let mut model = Model::new();
    model.add_source("a.sysml".to_string(), "package P { part x : Nope; }");
    let mut resolved = ResolvedModel::build(&model);
    let diags = sysmlv2_parser::check::validate_model_with(&mut resolved, &model);
    assert_eq!(diags.len(), 1);
    assert_eq!(resolved.unresolved_references().len(), 1);
}

// --- typing fixes verified against the value and its redefiners ---

/// A stand-in for the library's scalar types: the inference resolves
/// `ScalarValues::<name>` and the semantic check classifies declared
/// types by these names, so no library load is needed.
const SCALARS: &str = "package ScalarValues {\n    attribute def Boolean;\n    attribute def String;\n    \
                       attribute def Real;\n    attribute def Integer :> Real;\n}\n";

const TYPING_ON: &str =
    r#"{ "rules": { "untyped-usage": "warn", "dimensional-consistency": "warn" } }"#;

/// Lint `src` beside the scalar stand-ins with both typing rules on.
fn typing_findings(src: &str) -> Vec<Finding> {
    run_with_sources(
        &[("scalars.sysml", SCALARS), ("a.sysml", src)],
        &Config::from_json(TYPING_ON).unwrap(),
    )
    .into_iter()
    .filter(|f| f.unit == Some(1))
    .collect()
}

/// The semantic-check diagnostic count for `src` beside the scalar
/// stand-ins — what a typing fix must not raise.
fn check_count(src: &str) -> usize {
    let mut model = Model::new();
    model.add_source("scalars.sysml".to_string(), SCALARS);
    model.add_source("a.sysml".to_string(), src);
    let mut resolved = ResolvedModel::build(&model);
    sysmlv2_parser::check::validate_model_with(&mut resolved, &model).len()
}

/// Apply every preferred fix of `findings` to `src` (single-unit).
/// Identical edits collapse, as they do in every host's fix-all: both
/// typing rules write the same insert for one attribute.
fn apply_all_fixes(src: &str, findings: &[Finding]) -> String {
    let mut edits: Vec<&sysmlv2_lint::Edit> = findings
        .iter()
        .filter_map(|f| f.fix.as_ref())
        .flat_map(|fx| fx.edits.iter())
        .collect();
    edits.sort_by_key(|e| std::cmp::Reverse(e.span.start));
    edits.dedup_by(|a, b| a.span == b.span && a.replacement == b.replacement);
    let mut out = src.to_string();
    for e in edits {
        out.replace_range(e.span.start as usize..e.span.end as usize, &e.replacement);
    }
    out
}

#[test]
fn typing_fix_is_withheld_when_a_redefiner_contradicts_the_inferred_type() {
    // `s = "0"` reads as a String, but the untyped redefiner assigns a
    // number and would borrow the new typing: the semantic check would
    // report it, so neither rule offers the typing.
    let src = "package P {\n    private import ScalarValues::*;\n    \
               part def D { attribute s = \"0\"; }\n    \
               part d : D { attribute :>> s = 5; }\n}\n";
    let findings = typing_findings(src);
    let untyped: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.rule == "untyped-usage")
        .collect();
    assert_eq!(untyped.len(), 1, "{findings:?}");
    assert!(untyped[0].message.contains("`s`"), "{}", untyped[0].message);
    assert!(
        untyped[0].fix.is_none() && untyped[0].suggest.is_none(),
        "{untyped:?}"
    );
    assert!(untyped[0].alternatives.is_empty());
    assert!(
        findings.iter().all(|f| f.rule != "dimensional-consistency"),
        "{findings:?}"
    );
    // Nothing to apply; the check stays where it was.
    assert_eq!(
        check_count(&apply_all_fixes(src, &findings)),
        check_count(src)
    );
}

#[test]
fn integral_value_infers_real_when_a_redefiner_is_not_integral() {
    // `n = 0` alone reads as an Integer; the redefiner's `0.2` could
    // never conform to that, and both values conform to Real.
    let src = "package P {\n    private import ScalarValues::*;\n    \
               part def D { attribute n = 0; }\n    \
               part d : D { attribute :>> n = 0.2; }\n}\n";
    let findings = typing_findings(src);
    let by_rule = |rule: &str| {
        findings
            .iter()
            .find(|f| f.rule == rule)
            .unwrap_or_else(|| panic!("{rule} finding in {findings:?}"))
    };
    assert_eq!(by_rule("untyped-usage").suggest.as_deref(), Some("Real"));
    let d = by_rule("dimensional-consistency");
    assert_eq!(d.suggest.as_deref(), Some("Real"));
    assert!(d.message.contains("infers `Real`"), "{}", d.message);
    assert!(d.alternatives.is_empty(), "{:?}", d.alternatives);
    let fixed = apply_all_fixes(src, &findings);
    assert!(fixed.contains("attribute n : Real = 0;"), "{fixed}");
    assert_eq!(check_count(&fixed), check_count(src), "{fixed}");
}

#[test]
fn real_literal_spelling_infers_real_even_when_integral() {
    // `0.0` evaluates to an exact zero; the author wrote a real. A bare
    // `2` stays an Integer.
    let src = "package P {\n    private import ScalarValues::*;\n    \
               attribute z = 0.0;\n    attribute k = 2;\n    attribute q = 1/4000.0;\n}\n";
    let findings = typing_findings(src);
    let suggest = |name: &str| {
        findings
            .iter()
            .find(|f| {
                f.rule == "dimensional-consistency" && f.message.contains(&format!("`{name}`"))
            })
            .and_then(|f| f.suggest.clone())
    };
    assert_eq!(suggest("z").as_deref(), Some("Real"));
    assert_eq!(suggest("k").as_deref(), Some("Integer"));
    assert_eq!(suggest("q").as_deref(), Some("Real"));
    let fixed = apply_all_fixes(src, &findings);
    assert!(
        fixed.contains("attribute z : Real = 0.0;") && fixed.contains("attribute k : Integer = 2;"),
        "{fixed}"
    );
    assert_eq!(check_count(&fixed), check_count(src), "{fixed}");
}

#[test]
fn integer_inference_survives_integral_redefiners() {
    // Redefiners that keep to integers do not widen the inference; a
    // redefiner typed on its own is not the borrowing kind and does
    // not count either.
    let src = "package P {\n    private import ScalarValues::*;\n    \
               part def D { attribute n = 0; }\n    \
               part d : D { attribute :>> n = 7; }\n    \
               part e : D { attribute :>> n : Real = 0.5; }\n}\n";
    let findings = typing_findings(src);
    let f = findings
        .iter()
        .find(|f| f.rule == "dimensional-consistency")
        .expect("inference finding");
    assert_eq!(f.suggest.as_deref(), Some("Integer"), "{}", f.message);
    let fixed = apply_all_fixes(src, &findings);
    assert_eq!(check_count(&fixed), check_count(src), "{fixed}");
}

#[test]
fn import_visibility_recommends_public_for_dependents_reaching_through_a_chain() {
    // Q sees Lib::Thing only through P's import (re-exported by Q's own
    // import of P): the dependent lives outside P, so `private` would
    // hide the member it resolves through.
    let f = import_visibility_finding(&[
        ("lib.sysml", IMPORT_LIB),
        ("p.sysml", "package P { import Lib::*; }\n"),
        (
            "q.sysml",
            "package Q { private import P::*; part b : Thing; }\n",
        ),
    ]);
    assert!(
        f.message.contains("`public` is required") && f.message.contains("outside `P`"),
        "{}",
        f.message
    );
    assert_eq!(f.suggest.as_deref(), Some("public"));
    assert_eq!(f.fix.as_ref().unwrap().label, "Make the import `public`");
    let private = f
        .alternatives
        .iter()
        .find(|a| a.label == "Make the import `private`")
        .expect("private rewrite");
    assert!(private.semantic);
}

#[test]
fn inherited_name_shadow_spells_the_redefinition() {
    let src = "package P {\n    attribute def Real;\n    attribute def SwitchStatus { attribute downlinkPort : Real; }\n    attribute def M1 :> SwitchStatus { attribute downlinkPort : Real[6]; }\n    attribute def Lan { attribute m1 : M1; }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "inherited-name-shadow");
    assert_eq!(findings.len(), 2, "{findings:?}");
    let owned = findings
        .iter()
        .find(|f| f.element.as_deref() == Some("P::M1::downlinkPort"))
        .expect("owned collision");
    assert_eq!(owned.severity, Severity::Info);
    let fix = owned.fix.as_ref().expect("redefinition fix");
    assert!(fix.semantic && !fix.deletes);
    assert_eq!(fix.label, "redefine the inherited `downlinkPort` (`:>>`)");
    let fixed = apply_fix(src, fix);
    assert!(
        fixed
            .contains("attribute def M1 :> SwitchStatus { attribute :>> downlinkPort : Real[6]; }"),
        "{fixed}"
    );
    assert!(rule_findings(&[("a.sysml", &fixed)], "inherited-name-shadow").is_empty());
    // The inheriting usage carries the finding without a fix: nothing to
    // redefine on its side.
    let both = findings
        .iter()
        .find(|f| f.element.as_deref() == Some("P::Lan::m1"))
        .expect("inherited-twice collision");
    assert!(both.fix.is_none());
    assert!(
        both.message
            .starts_with("`downlinkPort` is inherited from both `M1` and `SwitchStatus`")
    );
}

#[test]
fn inherited_name_shadow_keeps_a_differently_spelled_name() {
    let src = "package P {\n    attribute def Real;\n    attribute def A { attribute x : Real; }\n    attribute def B :> A { attribute <x> other : Real; }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "inherited-name-shadow");
    assert_eq!(findings.len(), 1, "{findings:?}");
    let fixed = apply_fix(src, findings[0].fix.as_ref().expect("fix"));
    assert!(
        fixed.contains("attribute <x> other :>> x : Real;"),
        "{fixed}"
    );
    assert!(rule_findings(&[("a.sysml", &fixed)], "inherited-name-shadow").is_empty());
}

#[test]
fn inherited_name_shadow_withholds_a_contradicting_redefinition() {
    // A type the hidden feature's type does not admit, an explicit
    // multiplicity that differs, and a nested definition: findings without
    // fixes rather than repairs the checker would then reject.
    let src = "package P {\n    attribute def Real;\n    attribute def Text;\n    attribute def A { attribute x : Real; attribute y : Real[1]; part def N; }\n    attribute def B :> A { attribute x : Text; attribute y : Real[6]; part def N; }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "inherited-name-shadow");
    assert_eq!(findings.len(), 3, "{findings:?}");
    assert!(findings.iter().all(|f| f.fix.is_none()), "{findings:?}");
}

#[test]
fn inherited_name_shadow_withholds_redefinitions_the_checker_rejects() {
    // An end hidden by a non-end, a direction the hidden one does not
    // admit, a bound value overridden, a variant hidden: findings without
    // fixes (`validateRedefinitionEndConformance`,
    // `validateRedefinitionDirectionConformance`,
    // `validateFeatureValueOverriding`, variant membership). Parameters
    // and connector ends are not among them: those are redefined by
    // position and never collide.
    let src = "package P {\n    attribute def Real;\n    part def A;\n    part def X { in attribute x : Real; end part e : A; }\n    part def Y :> X { out attribute x : Real; part e : A; }\n    attribute def V { attribute v : Real = 1; }\n    attribute def W :> V { attribute v : Real = 2; }\n    variation part def E { variant part e : A; }\n    part def F :> E { part e : A; }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "inherited-name-shadow");
    let mut elements: Vec<&str> = findings
        .iter()
        .filter_map(|f| f.element.as_deref())
        .collect();
    elements.sort_unstable();
    assert_eq!(
        elements,
        ["P::F::e", "P::W::v", "P::Y::e", "P::Y::x"],
        "{findings:?}"
    );
    assert!(findings.iter().all(|f| f.fix.is_none()), "{findings:?}");
    assert!(
        findings.iter().all(|f| f
            .message
            .ends_with("rename it, or redefine it (`:>>`) with a conforming declaration")),
        "{findings:?}"
    );
}

#[test]
fn inherited_name_shadow_admits_conforming_redefinitions() {
    // `inout` admits any direction, a default value may be overridden,
    // and nested multiplicities conform. (An end hidden by an end is
    // redefined by position and never collides.)
    let src = "package P {\n    attribute def Real;\n    part def A;\n    part def X { inout attribute x : Real; end part e : A; }\n    part def Y :> X { in attribute x : Real; end part e : A; }\n    attribute def V { attribute v : Real default 1; attribute w : Real[0..10]; }\n    attribute def W :> V { attribute v : Real = 2; attribute w : Real[2..5]; }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "inherited-name-shadow");
    assert_eq!(findings.len(), 3, "{findings:?}");
    let mut fixed = src.to_string();
    let mut in_order: Vec<&sysmlv2_lint::Finding> = findings.iter().collect();
    in_order.sort_by_key(|f| std::cmp::Reverse(f.span.unwrap().start));
    for f in in_order {
        fixed = apply_fix(&fixed, f.fix.as_ref().expect("fix"));
    }
    assert!(
        fixed.contains("part def Y :> X { in attribute :>> x : Real; end part e : A; }"),
        "{fixed}"
    );
    assert!(
        fixed.contains("attribute :>> v : Real = 2; attribute :>> w : Real[2..5];"),
        "{fixed}"
    );
    assert!(rule_findings(&[("a.sysml", &fixed)], "inherited-name-shadow").is_empty());
}

#[test]
fn inherited_name_shadow_targets_the_nearest_of_a_chain_by_qualified_name() {
    // `C::x` hides both `B::x` and `A::x`; the fix redefines the nearer,
    // qualified — the simple name is ambiguous there — and together with
    // the fix on `B::x` the model comes out clean.
    let src = "package P {\n    attribute def Real;\n    part def A { attribute x : Real; }\n    part def B :> A { attribute x : Real; }\n    part def C :> B { attribute x : Real; }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "inherited-name-shadow");
    assert_eq!(findings.len(), 2, "{findings:?}");
    let mut fixed = src.to_string();
    let mut in_order: Vec<&sysmlv2_lint::Finding> = findings.iter().collect();
    in_order.sort_by_key(|f| std::cmp::Reverse(f.span.unwrap().start));
    for f in in_order {
        fixed = apply_fix(&fixed, f.fix.as_ref().expect("fix"));
    }
    assert!(
        fixed.contains("part def B :> A { attribute :>> x : Real; }"),
        "{fixed}"
    );
    assert!(
        fixed.contains("part def C :> B { attribute :>> P::B::x : Real; }"),
        "{fixed}"
    );
    assert!(rule_findings(&[("a.sysml", &fixed)], "inherited-name-shadow").is_empty());
    // Unrelated bases: redefining either leaves the other, so no fix.
    let src = "package P {\n    attribute def Real;\n    part def A { attribute x : Real; }\n    part def Z { attribute x : Real; }\n    part def C :> A, Z { attribute x : Real; }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "inherited-name-shadow");
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert!(findings[0].fix.is_none(), "{findings:?}");
}

#[test]
fn inherited_name_shadow_targets_the_hidden_member_by_its_own_name() {
    // The collision is on the hidden member's short name; the
    // redefinition names it by its declared name. An owned member with
    // only a short name gets the redefinition after the bracket.
    let src = "package P {\n    attribute def Real;\n    attribute def A { attribute <x> long : Real; }\n    attribute def B :> A { attribute x : Real; }\n    attribute def C :> A { attribute <x> : Real; }\n}\n";
    let findings = rule_findings(&[("a.sysml", src)], "inherited-name-shadow");
    assert_eq!(findings.len(), 2, "{findings:?}");
    let mut fixed = src.to_string();
    for f in findings.iter().rev() {
        fixed = apply_fix(&fixed, f.fix.as_ref().expect("fix"));
    }
    assert!(
        fixed.contains("attribute def B :> A { attribute x :>> long : Real; }"),
        "{fixed}"
    );
    assert!(
        fixed.contains("attribute def C :> A { attribute <x> :>> long : Real; }"),
        "{fixed}"
    );
    assert!(rule_findings(&[("a.sysml", &fixed)], "inherited-name-shadow").is_empty());
}

/// A flat package of thousands of definitions lints in linear time: the
/// reference index and the per-owner sibling-name index are built once
/// per pass, never once per definition or finding.
#[test]
fn flat_package_of_thousands_of_definitions_lints_quickly() {
    const N: usize = 2_000;
    let mut src = String::from("package P {\n");
    for i in 0..N {
        // Every name is off the PascalCase convention, so each definition
        // yields a naming finding whose suggestion is checked against its
        // siblings; odd definitions specialize their predecessor, so
        // exactly the even ones are referenced.
        if i % 2 == 1 {
            writeln!(src, "    part def item_{i} :> item_{};", i - 1).unwrap();
        } else {
            writeln!(src, "    part def item_{i};").unwrap();
        }
    }
    src.push_str("}\n");
    let config = Config::from_json(r#"{ "rules": { "unused-definition": "warn" } }"#).unwrap();
    let mut model = Model::new();
    model.add_source("a.sysml".to_string(), &src);
    let mut resolved = ResolvedModel::build(&model);
    let started = std::time::Instant::now();
    let findings = lint(&mut resolved, &config);
    let elapsed = started.elapsed();
    let naming: Vec<&Finding> = findings
        .iter()
        .filter(|f| f.rule == "naming-convention")
        .collect();
    let unused = findings
        .iter()
        .filter(|f| f.rule == "unused-definition")
        .count();
    assert_eq!(naming.len(), N);
    assert_eq!(unused, N / 2);
    assert!(
        naming
            .iter()
            .all(|f| f.suggest.as_deref().is_some_and(|s| s.starts_with("Item"))),
        "every naming finding carries its converted suggestion"
    );
    assert!(
        elapsed < std::time::Duration::from_secs(1),
        "lint pass over {N} definitions took {elapsed:?}"
    );
}

/// The rule inventory and the id enum are one table: every configurable
/// id has an inventory entry, every inventory entry parses back to the
/// variant it was written with, and no spelling is claimed twice. A
/// misspelled id can no longer reach a lookup, so the inventory is what
/// has to stay in step.
#[test]
fn every_rule_id_matches_exactly_one_inventory_entry() {
    let mut seen: Vec<&str> = Vec::new();
    for id in RuleId::ALL {
        assert_eq!(id.to_string(), id.id(), "`Display` is the wire spelling");
        assert_eq!(
            id.id().parse::<RuleId>().expect("its own spelling parses"),
            *id
        );
        assert!(!seen.contains(&id.id()), "duplicate spelling `{id}`");
        seen.push(id.id());
        let entries = RULES.iter().filter(|r| r.id == *id).count();
        let want = usize::from(*id != RuleId::LintConfig);
        assert_eq!(entries, want, "`{id}` has {entries} inventory entries");
        assert_eq!(id.rule().is_some(), want == 1);
    }
    assert_eq!(
        RULES.len() + 1,
        RuleId::ALL.len(),
        "only `lint-config` is extra"
    );
}

/// An id no rule carries is rejected once, by name: reading it fails
/// with the unknown-rule error, and config naming it complains about the
/// id rather than about whatever value was written beside it.
#[test]
fn an_unknown_rule_id_is_reported_as_the_unknown_id() {
    let err = "no-such-rule".parse::<RuleId>().expect_err("not a rule");
    assert_eq!(err.to_string(), "unknown lint rule `no-such-rule`");
    let cfg = Config::from_json(r#"{ "rules": { "no-such-rule": "loud" } }"#).unwrap();
    let findings = run(&[("a.sysml", CALC)], &cfg);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "lint-config");
    assert_eq!(findings[0].message, "unknown lint rule `no-such-rule`");
}

/// Configuration fails outright only when the text is not JSON at all;
/// anything readable reports through findings instead, so a host can
/// tell "I could not read your file" from "your file says something
/// odd" without matching on message text.
#[test]
fn only_unreadable_config_is_an_error() {
    let Err(err) = Config::from_json("{ this is not json") else {
        panic!("text that is not JSON has no configuration");
    };
    assert!(matches!(err, LintError::ConfigNotJson(_)), "{err:?}");
    assert!(err.to_string().starts_with("config is not JSON: "), "{err}");
    let _boxed: Box<dyn std::error::Error> = Box::new(err);
    let cfg = Config::from_json(r#"{ "rules": { "indentation": { "size": "wide" } } }"#)
        .expect("readable JSON");
    let findings = run(&[("a.sysml", CALC)], &cfg);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert_eq!(findings[0].rule, "lint-config");
}
