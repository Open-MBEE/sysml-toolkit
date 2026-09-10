//! Rule-level gates: hit/miss per rule, severity config, scope maps,
//! style presets, config complaints, fix shapes, determinism.

use sysmlv2_lint::{Config, Finding, Severity, convert_to_style, lint, lint_with_sources};
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
