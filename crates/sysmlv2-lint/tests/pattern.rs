//! `literal-pattern` over the real standard library and the ambient
//! `StringPatterns` library: a string bound to a feature typed by the
//! standard library's ISO 8601 date-time encoding — a feature value, a
//! constructor argument by position or name, a calculation argument —
//! must take the documented form; a reduced-precision date reports at
//! the reduced severity; annotations in the model govern their own types
//! and subtypes; configuration overrides a type's pattern or disables
//! the rule.

use sysmlv2_lint::{Config, Finding, RULES, RuleId, Severity, lint};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;

const PRELUDE: &str =
    "package G {\n    private import Time::*;\n    private import ScalarValues::*;\n";

const FORM: &str = "YYYY-MM-DDThh:mm:ss[.fff[fff]](Z|±hh:mm)";

/// Lint `body` inside the importing package, against the vendored
/// standard library and the ambient libraries, keeping this rule's
/// findings and the configuration complaints. Every finding on the
/// model is located in the one user unit, which follows the library
/// units.
fn run(body: &str, config: &Config) -> (Vec<Finding>, String) {
    let src = format!("{PRELUDE}{body}}}\n");
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    sysmlv2_model::ambient::add_to(&mut model);
    model.add_source("t.sysml", &src);
    assert!(!model.has_errors(), "test source must parse cleanly");
    let user_unit = model.unit_count() - 1;
    let mut resolved = ResolvedModel::build(&model);
    let findings: Vec<Finding> = lint(&mut resolved, config)
        .into_iter()
        .filter(|f| matches!(f.rule, RuleId::LiteralPattern | RuleId::LintConfig))
        .collect();
    for f in findings.iter().filter(|f| f.rule == RuleId::LiteralPattern) {
        assert_eq!(f.unit, Some(user_unit), "{f:#?}");
    }
    (findings, src)
}

fn config(json: &str) -> Config {
    Config::from_json(json).expect("config")
}

fn literal_span(src: &str, literal: &str) -> (u32, u32) {
    let start = src.find(literal).expect("literal in source") as u32;
    (start, start + literal.len() as u32)
}

#[test]
fn a_string_off_the_documented_form_is_flagged_at_every_binding_site() {
    let (f, src) = run(
        "    part def P {
        attribute dob : Iso8601DateTime = new Iso8601DateTime(\"1926-04-3\");
        attribute named : Iso8601DateTime = new Iso8601DateTime(val = \"1926-4-03\");
        attribute enc : Iso8601DateTimeEncoding = \"x\";
        attribute many : Iso8601DateTimeEncoding[*] = (\"1969-07-20T20:17:00Z\", \"bad\");
    }
    calc def Parse { in s : Iso8601DateTimeEncoding; return : Integer = 1; }
    attribute parsed = Parse(\"nope\");
",
        &Config::default(),
    );
    assert_eq!(f.len(), 5, "{f:#?}");
    for finding in &f {
        assert_eq!(finding.severity, Severity::Warn);
        assert!(
            finding.message.contains(&format!(
                "is not in the form of `Iso8601DateTimeEncoding`, `{FORM}`"
            )),
            "{}",
            finding.message
        );
    }
    let expected = [
        ("G::P::dob", "`1926-04-3` is not", "\"1926-04-3\""),
        ("G::P::named", "`1926-4-03` is not", "\"1926-4-03\""),
        ("G::P::enc", "`x` is not", "\"x\""),
        (
            "G::P::many",
            "`bad` is not",
            "(\"1969-07-20T20:17:00Z\", \"bad\")",
        ),
        ("G::parsed", "`nope` is not", "\"nope\""),
    ];
    for (finding, (element, prefix, literal)) in f.iter().zip(expected) {
        assert_eq!(finding.element.as_deref(), Some(element));
        assert!(finding.message.starts_with(prefix), "{}", finding.message);
        let (start, end) = literal_span(&src, literal);
        let span = finding.span.expect("span");
        assert_eq!((span.start, span.end), (start, end), "{}", finding.message);
    }
}

#[test]
fn documented_forms_and_undecided_values_are_silent() {
    let (f, _) = run(
        "    part def P {
        attribute a : Iso8601DateTime = new Iso8601DateTime(\"1969-07-20T20:17:00Z\");
        attribute b : Iso8601DateTime = new Iso8601DateTime(\"2018-01-23T23:14:44.304827Z\");
        attribute c : Iso8601DateTime = new Iso8601DateTime(\"1969-07-20T15:17:00-05:00\");
        attribute d : Iso8601DateTime = new Iso8601DateTime(\"+12345-12-31T23:59:60.000+02:00\");
        attribute e : Iso8601DateTimeEncoding = someRef;
        attribute n : Iso8601DateTime = new Iso8601DateTime(3);
        attribute s : String = \"anything\";
        attribute t : Iso8601DateTime = new Iso8601DateTime(\"2022-01-30\" + \"T01:00:00Z\");
        attribute shadow : String = \"nope\";
        attribute l = (\"1969-07-20T20:17:00Z\",)->collect {{ in shadow; new Iso8601DateTime(shadow) }};
    }
",
        &Config::default(),
    );
    assert!(f.is_empty(), "{f:#?}");
}

#[test]
fn a_reduced_precision_date_reports_at_the_reduced_severity() {
    let body = "    part def P {
        attribute dob : Iso8601DateTime = new Iso8601DateTime(\"1926-04-03\");
        attribute hour : Iso8601DateTime = new Iso8601DateTime(\"1926-04-03T10:00\");
        attribute year : Iso8601DateTimeEncoding = \"1926\";
    }
";
    let (f, _) = run(body, &Config::default());
    assert_eq!(f.len(), 3, "{f:#?}");
    for finding in &f {
        assert_eq!(finding.severity, Severity::Info);
        assert!(
            finding.message.contains(&format!(
                "is an accepted broader form of `Iso8601DateTimeEncoding`; the documented form is `{FORM}`"
            )),
            "{}",
            finding.message
        );
    }
    assert!(
        f[0].message.starts_with("`1926-04-03` is an accepted"),
        "{}",
        f[0].message
    );

    let (off, _) = run(
        body,
        &config(r#"{ "rules": { "literal-pattern": { "reduced": "off" } } }"#),
    );
    assert!(off.is_empty(), "{off:#?}");
    let (loud, _) = run(
        body,
        &config(r#"{ "rules": { "literal-pattern": { "reduced": "warn" } } }"#),
    );
    assert_eq!(loud.len(), 3);
    assert!(loud.iter().all(|f| f.severity == Severity::Warn));
}

#[test]
fn patterns_govern_subtypes_and_come_from_annotations_in_the_model() {
    let (f, _) = run(
        "    attribute def Stamp :> Iso8601DateTimeEncoding;
    attribute def PartNumber :> String {
        @StringPatterns::Pattern { regex = \"PN-[0-9]{6}\"; form = \"PN-nnnnnn\"; }
    }
    attribute def Code :> String;
    @StringPatterns::Pattern about Code { regex = \"[A-Z]{3}\"; }
    part def W {
        attribute s : Stamp = \"nope\";
        attribute pn : PartNumber = \"PN-12\";
        attribute ok : PartNumber = \"PN-123456\";
        attribute c : Code = \"abc\";
        attribute d : Code = \"ABC\";
    }
",
        &Config::default(),
    );
    let messages: Vec<&str> = f.iter().map(|f| f.message.as_str()).collect();
    assert_eq!(
        messages,
        [
            format!("`nope` is not in the form of `Iso8601DateTimeEncoding`, `{FORM}`"),
            "`PN-12` is not in the form of `PartNumber`, `PN-nnnnnn`".to_string(),
            "`abc` is not in the form of `Code`, `[A-Z]{3}`".to_string(),
        ],
        "{f:#?}"
    );
}

#[test]
fn configuration_overrides_a_pattern_or_turns_the_rule_off() {
    let body = "    part def P {
        attribute dob : Iso8601DateTime = new Iso8601DateTime(\"1926-04-03\");
        attribute full : Iso8601DateTime = new Iso8601DateTime(\"1969-07-20T20:17:00Z\");
    }
";
    let (f, _) = run(
        body,
        &config(
            r#"{ "rules": { "literal-pattern": { "patterns": {
                "Time::Iso8601DateTimeEncoding": "[0-9]{4}-[0-9]{2}-[0-9]{2}" } } } }"#,
        ),
    );
    assert_eq!(f.len(), 1, "{f:#?}");
    assert_eq!(
        f[0].message,
        "`1969-07-20T20:17:00Z` is not in the form of `Iso8601DateTimeEncoding`, `[0-9]{4}-[0-9]{2}-[0-9]{2}`"
    );
    let (f, _) = run(
        body,
        &config(
            r#"{ "rules": { "literal-pattern": { "patterns": {
                "Time::Iso8601DateTimeEncoding": { "regex": "[0-9]{4}-[0-9]{2}-[0-9]{2}", "form": "YYYY-MM-DD" } } } } }"#,
        ),
    );
    assert_eq!(f.len(), 1, "{f:#?}");
    assert!(
        f[0].message
            .ends_with("`Iso8601DateTimeEncoding`, `YYYY-MM-DD`"),
        "{}",
        f[0].message
    );

    let (f, _) = run(
        body,
        &config(r#"{ "rules": { "literal-pattern": "off" } }"#),
    );
    assert!(f.is_empty(), "{f:#?}");

    // Malformed configuration is a `lint-config` finding, not silence.
    for (json, complaint) in [
        (
            r#"{ "rules": { "literal-pattern": { "patterns": { "X::Y": "(" } } } }"#,
            "does not compile",
        ),
        (
            r#"{ "rules": { "literal-pattern": { "patterns": 3 } } }"#,
            "must be an object",
        ),
        (
            r#"{ "rules": { "literal-pattern": { "patterns": { "X::Y": { "accepts": "a" } } } } }"#,
            "needs a `regex`",
        ),
        (
            r#"{ "rules": { "literal-pattern": { "reduced": "loud" } } }"#,
            "must be one of",
        ),
    ] {
        let (f, _) = run(body, &config(json));
        let complaints: Vec<&Finding> = f.iter().filter(|f| f.rule == RuleId::LintConfig).collect();
        assert_eq!(complaints.len(), 1, "{json}: {f:#?}");
        assert!(
            complaints[0].message.contains(complaint),
            "{}",
            complaints[0].message
        );
    }
}

#[test]
fn an_annotation_that_does_not_compile_is_reported_and_governs_nothing() {
    let (f, _) = run(
        "    attribute def Bad :> String {
        @StringPatterns::Pattern { regex = \"(\"; }
    }
    attribute def Empty :> String {
        @StringPatterns::Pattern { form = \"anything\"; }
    }
    attribute b : Bad = \"x\";
    attribute e : Empty = \"y\";
",
        &Config::default(),
    );
    let messages: Vec<&str> = f.iter().map(|f| f.message.as_str()).collect();
    assert_eq!(messages.len(), 2, "{f:#?}");
    assert!(
        messages[0].starts_with("the pattern on `Bad` regex `(` does not compile"),
        "{}",
        messages[0]
    );
    assert_eq!(messages[1], "the pattern on `Empty` names no `regex`");
    assert!(
        f.iter()
            .all(|f| f.severity == Severity::Warn && f.span.is_some()),
        "{f:#?}"
    );
    assert_eq!(f[0].element.as_deref(), Some("G::Bad"));
}

#[test]
fn the_rule_is_in_the_inventory() {
    let rule = RULES
        .iter()
        .find(|r| r.id == RuleId::LiteralPattern)
        .expect("inventory entry");
    assert_eq!(rule.id.id(), "literal-pattern");
    assert_eq!(rule.default, Severity::Warn);
    assert_eq!(rule.options.len(), 1);
    assert_eq!(rule.options[0].key, "reduced");
    assert_eq!(Config::default().literal_pattern_reduced(), Severity::Info);
    assert!(Config::default().literal_patterns().is_empty());
}

#[test]
fn a_memoized_fruitless_type_does_not_end_the_search_for_its_siblings() {
    // `A` is searched first (nothing on it), then `X :> A, B`: the memo
    // for `A` must prune `A` alone, not the search of `B`.
    let (f, _) = run(
        "    attribute def A :> String;
    attribute def B :> String {
        @StringPatterns::Pattern { regex = \"[a-z]+\"; form = \"lower case\"; }
    }
    attribute def X :> A, B;
    attribute def Y :> B, A;
    attribute a0 : A = \"ZZ\";
    attribute x : X = \"ZZ\";
    attribute y : Y = \"ZZ\";
    attribute x2 : X = \"zz\";
",
        &Config::default(),
    );
    let messages: Vec<&str> = f.iter().map(|f| f.message.as_str()).collect();
    assert_eq!(
        messages,
        [
            "`ZZ` is not in the form of `B`, `lower case`",
            "`ZZ` is not in the form of `B`, `lower case`",
        ],
        "{f:#?}"
    );
    assert_eq!(f[0].element.as_deref(), Some("G::x"));
    assert_eq!(f[1].element.as_deref(), Some("G::y"));
}

#[test]
fn calculation_result_expressions_and_nested_constructors_are_sites() {
    let (f, _) = run(
        "    calc def Make { new Iso8601DateTime(\"1926-04-3\") }
    attribute def Pair { attribute stamp : Iso8601DateTime; attribute n : Integer; }
    attribute p : Pair = new Pair(new Iso8601DateTime(\"1926-4-3\"), 1);
",
        &Config::default(),
    );
    let messages: Vec<&str> = f.iter().map(|f| f.message.as_str()).collect();
    assert_eq!(
        messages,
        [
            format!("`1926-04-3` is not in the form of `Iso8601DateTimeEncoding`, `{FORM}`"),
            format!("`1926-4-3` is not in the form of `Iso8601DateTimeEncoding`, `{FORM}`"),
        ],
        "{f:#?}"
    );
    assert_eq!(f[0].element.as_deref(), Some("G::Make"));
    assert_eq!(f[1].element.as_deref(), Some("G::p"));
}

#[test]
fn a_configured_pattern_on_a_subtype_takes_precedence_over_the_supertype_annotation() {
    let body = "    attribute def Stamp :> Iso8601DateTimeEncoding;
    attribute s : Stamp = \"1926-04-03\";
    attribute t : Iso8601DateTimeEncoding = \"1926-04-03\";
";
    let (f, _) = run(
        body,
        &config(
            r#"{ "rules": { "literal-pattern": { "patterns": { "G::Stamp": "[0-9]{4}-[0-9]{2}-[0-9]{2}" }, "reduced": "off" } } }"#,
        ),
    );
    assert!(f.is_empty(), "{f:#?}");
    let (f, _) = run(
        body,
        &config(r#"{ "rules": { "literal-pattern": { "reduced": "off" } } }"#),
    );
    assert!(f.is_empty(), "{f:#?}");
    let (f, _) = run(body, &Config::default());
    assert_eq!(f.len(), 2, "{f:#?}");
    assert!(f.iter().all(|f| f.severity == Severity::Info));
}
