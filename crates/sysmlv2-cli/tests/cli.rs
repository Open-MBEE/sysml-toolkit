//! `sysmlv2` CLI integration tests: help content (descriptions + examples
//! must be present — the documentation exit-criterion) and functional
//! smoke tests for each subcommand.

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn sysmlv2(args: &[&str]) -> Output {
    // The ambient-context variables are scrubbed so a developer's own
    // environment can never leak into test behavior; tests opt in
    // through `sysmlv2_env`.
    Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .env_remove("SYSMLV2_MODEL_DIR")
        .env_remove("SYSMLV2_LIB_DIR")
        .args(args)
        .output()
        .expect("failed to run sysmlv2")
}

fn sysmlv2_env(args: &[&str], env: &[(&str, &str)]) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_sysmlv2"));
    cmd.env_remove("SYSMLV2_MODEL_DIR")
        .env_remove("SYSMLV2_LIB_DIR");
    for (k, v) in env {
        cmd.env(k, v);
    }
    cmd.args(args).output().expect("failed to run sysmlv2")
}

fn stdout(out: &Output) -> String {
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

#[test]
fn top_level_help_documents_conversion_matrix_and_examples() {
    let out = sysmlv2(&["--help"]);
    assert!(out.status.success());
    let help = stdout(&out);
    for expected in [
        "Conversion matrix",
        "compact-json",
        "full-json",
        "EXAMPLES:",
        "sysmlv2 convert model.sysml --to compact-json",
        "sysmlv2 fmt --check",
        "sysmlv2 check",
    ] {
        assert!(
            help.contains(expected),
            "top-level help missing {expected:?}:\n{help}"
        );
    }
}

#[test]
fn every_subcommand_help_has_examples() {
    for sub in [
        "convert", "payload", "fmt", "check", "lint", "verify", "parse", "query", "describe",
        "members", "tree", "lsp",
    ] {
        let out = sysmlv2(&[sub, "--help"]);
        assert!(out.status.success(), "{sub} --help failed");
        let help = stdout(&out);
        assert!(
            help.contains("EXAMPLES:"),
            "`sysmlv2 {sub} --help` has no examples:\n{help}"
        );
        assert!(
            help.matches("sysmlv2 ").count() >= 2,
            "`sysmlv2 {sub} --help` needs at least two worked examples:\n{help}"
        );
    }
}

#[test]
fn convert_to_compact_json() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-convert-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(&input, "package P { part def V; part v : V; }").unwrap();

    let out = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "compact-json"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let json: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("valid JSON");
    let elements = json.as_array().unwrap();
    assert!(elements.iter().any(|e| e["@type"] == "PartDefinition"));

    // Full form: derived properties present (qualifiedName, owner, …).
    let out = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "full-json"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let full: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("valid JSON");
    let def = full
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["@type"] == "PartDefinition")
        .unwrap();
    assert_eq!(def["qualifiedName"], "P::V");
    assert!(def.as_object().unwrap().len() >= 84);
}

/// `--graph-format canonical` lowers under the opt-in contract: the second
/// operand of a conditional `and` is a reference expression to an owned
/// expression, where the default's operand is the expression itself; the
/// flag is global, so it sits before or after the verb, and the
/// environment variable selects the same.
#[test]
fn graph_format_switch_selects_the_canonical_lowering() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-graph-format-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("cond.kerml");
    fs::write(
        &input,
        "package Cond { class C { feature ready; feature hot; feature ok = ready and not hot; } }",
    )
    .unwrap();
    let operand_kinds = |out: &Output| -> Vec<String> {
        assert!(out.status.success(), "{}", stderr(out));
        let json: serde_json::Value = serde_json::from_str(&stdout(out)).expect("valid JSON");
        let elements = json.as_array().unwrap();
        let by_id = |id: &serde_json::Value| {
            elements
                .iter()
                .find(|e| &e["@id"] == id)
                .unwrap_or_else(|| panic!("element {id}"))
        };
        let and = elements
            .iter()
            .find(|e| e["@type"] == "OperatorExpression" && e["operator"] == "and")
            .expect("the conditional and");
        // The operands: the owned parameter of each ParameterMembership, in
        // order (the compact form spells the member as the membership's
        // owned related element).
        and["ownedRelationship"]
            .as_array()
            .unwrap()
            .iter()
            .map(|r| by_id(&r["@id"]))
            .filter(|m| m["@type"] == "ParameterMembership")
            .map(|m| {
                let parameter = by_id(&m["ownedRelatedElement"][0]["@id"]);
                let value = parameter["ownedRelationship"]
                    .as_array()
                    .unwrap()
                    .iter()
                    .map(|r| by_id(&r["@id"]))
                    .find(|r| r["@type"] == "FeatureValue")
                    .expect("the parameter's value");
                by_id(&value["ownedRelatedElement"][0]["@id"])["@type"]
                    .as_str()
                    .unwrap()
                    .to_string()
            })
            .collect()
    };
    let legacy = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "compact-json"]);
    assert_eq!(
        operand_kinds(&legacy),
        ["FeatureReferenceExpression", "OperatorExpression"]
    );
    let canonical = sysmlv2(&[
        "--graph-format",
        "canonical",
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-json",
    ]);
    assert_eq!(
        operand_kinds(&canonical),
        ["FeatureReferenceExpression", "FeatureReferenceExpression"]
    );
    let after_verb = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-json",
        "--graph-format",
        "canonical",
    ]);
    assert_eq!(stdout(&after_verb), stdout(&canonical));
    let from_env = sysmlv2_env(
        &["convert", input.to_str().unwrap(), "--to", "compact-json"],
        &[("SYSMLV2_GRAPH_FORMAT", "canonical")],
    );
    assert_eq!(stdout(&from_env), stdout(&canonical));
    let explicit_legacy = sysmlv2(&[
        "--graph-format",
        "legacy",
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-json",
    ]);
    assert_eq!(stdout(&explicit_legacy), stdout(&legacy));
    let unknown = sysmlv2(&[
        "--graph-format",
        "v4",
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-json",
    ]);
    assert!(!unknown.status.success());
    assert!(
        stderr(&unknown).contains("canonical"),
        "{}",
        stderr(&unknown)
    );
    // An unknown value in the environment is refused the same, never
    // silently the default.
    let typo = sysmlv2_env(
        &["convert", input.to_str().unwrap(), "--to", "compact-json"],
        &[("SYSMLV2_GRAPH_FORMAT", "cannonical")],
    );
    assert!(!typo.status.success());
    assert!(stderr(&typo).contains("canonical"), "{}", stderr(&typo));
    // `prepare` takes the default and says so.
    let out = dir.join("out");
    let prepare = sysmlv2(&[
        "--graph-format",
        "canonical",
        "prepare",
        "--lib",
        dir.to_str().unwrap(),
        "--out",
        out.to_str().unwrap(),
    ]);
    assert!(
        stderr(&prepare).contains("takes the default graph format"),
        "{}",
        stderr(&prepare)
    );
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn plain_full_json_preserves_unresolved_reference_spelling() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-full-recovery-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("partial.sysml");
    fs::write(&input, "package P { part x : Missing; }").unwrap();

    let out = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "full-json"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let full: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert!(full.as_array().unwrap().iter().any(|element| {
        element["@type"] == "TextualRepresentation"
            && element["language"] == "x-sysmlv2-unresolved-reference"
            && element["body"] == "Missing"
    }));
}

#[test]
fn fmt_check_and_rewrite() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-fmt-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("messy.sysml");
    fs::write(&input, "package  P{part def  V;part v:V;}").unwrap();

    // --check on unformatted input: exit 1, file untouched.
    let out = sysmlv2(&["fmt", "--check", input.to_str().unwrap()]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("would reformat"));
    assert_eq!(
        fs::read_to_string(&input).unwrap(),
        "package  P{part def  V;part v:V;}"
    );

    // Rewrite in place, then --check passes.
    let out = sysmlv2(&["fmt", input.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let formatted = fs::read_to_string(&input).unwrap();
    assert_eq!(
        formatted,
        "package P {\n    part def V;\n    part v : V;\n}\n"
    );
    let out = sysmlv2(&["fmt", "--check", input.to_str().unwrap()]);
    assert!(out.status.success());
}

#[test]
fn verify_ranges_narrows_and_attributes_verdicts() {
    // Propagation is solverless, so this needs no z3. Two feasible bounds
    // narrow `wingSpan`; a separate contradictory pair empties `count`. The
    // empty domain must implicate only the constraint that references it —
    // not its innocent siblings in the same unit.
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-ranges-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package Demo {\n\
         \x20   attribute def Real;\n\
         \x20   attribute def Integer;\n\
         \x20   attribute wingSpan : Real[1];\n\
         \x20   attribute count : Integer[1];\n\
         \x20   assert constraint span_lo { wingSpan >= 10 }\n\
         \x20   assert constraint span_hi { wingSpan <= 200 }\n\
         \x20   assert constraint bad { count > 5 & count < 4 }\n\
         }\n",
    )
    .unwrap();

    let out = sysmlv2(&["verify", input.to_str().unwrap(), "--ranges"]);
    let text = stdout(&out);
    // Feasible siblings stay satisfied; only `bad` is proved unsatisfiable.
    assert!(
        text.contains("span_lo (AssertConstraintUsage): satisfied (propagation:"),
        "span_lo should be satisfied by propagation:\n{text}"
    );
    assert!(
        text.contains("bad (AssertConstraintUsage): VIOLATED (propagation:"),
        "bad should be violated by propagation:\n{text}"
    );
    assert!(
        text.contains("2 satisfied, 1 violated, 0 undecided"),
        "{text}"
    );
    // Narrowed ranges block, with the joint bound and the empty domain.
    assert!(text.contains("narrowed ranges:"), "{text}");
    assert!(text.contains("wingSpan ∈ [10, 200]"), "{text}");
    assert!(text.contains("count ∈ ∅"), "{text}");
    // A violation exits non-zero.
    assert!(!out.status.success());
}

#[test]
fn verify_reports_one_verdict_per_satisfaction_claim() {
    // Each claim's verdict sits on its `satisfy` statement, the same in
    // both stages; the constraints behind a failed claim follow it,
    // indented, with the values that decided them.
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-claims-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("claims.sysml");
    fs::write(
        &input,
        "package Load {\n\
         \x20   private import ISQ::*;\n\
         \x20   private import SI::*;\n\
         \x20   part def Crate { attribute mass : MassValue; }\n\
         \x20   requirement def Limit {\n\
         \x20       subject c : Crate;\n\
         \x20       attribute cap : MassValue;\n\
         \x20       require constraint { c.mass <= cap }\n\
         \x20   }\n\
         \x20   requirement small : Limit { attribute :>> cap = 10 [kg]; }\n\
         \x20   part light : Crate { attribute :>> mass = 4 [kg]; }\n\
         \x20   part heavy : Crate { attribute :>> mass = 40 [kg]; }\n\
         \x20   part site {\n\
         \x20       satisfy small by light;\n\
         \x20       satisfy small by heavy;\n\
         \x20   }\n\
         }\n",
    )
    .unwrap();
    for stage in [&[][..], &["--ranges"][..]] {
        let mut args = vec![
            "verify",
            input.to_str().unwrap(),
            "--lib",
            lib.to_str().unwrap(),
        ];
        args.extend_from_slice(stage);
        let out = sysmlv2_env(&args, &[("SYSMLV2_LIB_CACHE", "off")]);
        let text = stdout(&out);
        assert!(
            text.contains(
                "claims.sysml:14:9  <anonymous> (SatisfyRequirementUsage, satisfies Load::small by light): satisfied\n"
            ),
            "{stage:?}:\n{text}"
        );
        assert!(
            text.contains(
                "claims.sysml:15:9  <anonymous> (SatisfyRequirementUsage, satisfies Load::small by heavy): VIOLATED\n  "
            ),
            "{stage:?}:\n{text}"
        );
        assert!(
            text.contains(
                "claims.sysml:8:30  <anonymous> (ConstraintUsage): VIOLATED (with c.mass = 40 [kg], cap = 10 [kg])\n"
            ),
            "{stage:?}:\n{text}"
        );
        // The unbound original, plus one verdict per claim.
        assert!(
            text.contains("1 satisfied, 1 violated, 1 undecided"),
            "{stage:?}:\n{text}"
        );
        assert!(!out.status.success());
    }
}

#[test]
fn check_reports_rustc_style_diagnostics() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-check-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let good = dir.join("good.sysml");
    let bad = dir.join("bad.sysml");
    fs::write(&good, "package P;").unwrap();
    fs::write(&bad, "package Q { part x : ; }").unwrap();

    let out = sysmlv2(&["check", good.to_str().unwrap()]);
    assert!(out.status.success());

    let out = sysmlv2(&["check", bad.to_str().unwrap()]);
    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(err.contains("error:"), "{err}");
    assert!(err.contains("bad.sysml:1:22\n"), "location missing: {err}");
    // The finding's line, and a caret under its span.
    let excerpt = format!(
        "   | package Q {{ part x : ; }}\n   | {}^\n",
        " ".repeat(21)
    );
    assert!(err.contains(&excerpt), "{err}");
}

/// The text report shows at most 160 characters of a finding's line, so
/// on a model written as one long line it costs the same per finding
/// whatever the line's length. Echoing the whole line made the report
/// grow with findings times line length: 960 findings on a 12 KB line
/// wrote 12 MB.
#[test]
fn check_report_per_finding_does_not_grow_with_the_line() {
    const FINDINGS: usize = 100;
    let dir =
        std::env::temp_dir().join(format!("sysmlv2-cli-test-long-line-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    // `FINDINGS` parts of unresolved types on one line, each followed by a
    // note of `pad` characters.
    let report = |name: &str, pad: usize| {
        let note = format!("//* {} */", "x".repeat(pad));
        let parts: String = (0..FINDINGS)
            .map(|i| format!("part p{i} : Missing{i}; {note} "))
            .collect();
        let path = dir.join(name);
        fs::write(&path, format!("package P {{ {parts}}}\n")).unwrap();
        stderr(&sysmlv2(&["check", path.to_str().unwrap()]))
    };
    let short = report("s.sysml", 200);
    let long = report("l.sysml", 20_000);
    for text in [&short, &long] {
        assert_eq!(
            text.matches("warning: unresolved reference").count(),
            FINDINGS,
            "{text}"
        );
        // The gutter, at most 160 characters of the line and a `…` at
        // each cut; the caret line is no longer.
        for line in text.lines().filter(|line| line.starts_with("   | ")) {
            assert!(line.chars().count() <= 5 + 160 + 2, "{line}");
        }
    }
    // A line a hundred times longer adds only the digits of the columns.
    assert!(
        long.len() <= short.len() + 3 * FINDINGS,
        "{} > {}",
        long.len(),
        short.len()
    );
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn lint_flags_unused_parameters_and_deletes_only_behind_the_guard() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-lint-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    let src = "package P {\n    attribute def Real;\n    calc def T {\n        in force : Real;\n        in radius : Real;\n        return t : Real = force * 2;\n    }\n}\n";
    fs::write(&input, src).unwrap();

    // Every rule defaults off — a bare lint run is silent.
    let out = sysmlv2(&["lint", input.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        !stderr(&out).contains("unused-parameter"),
        "{}",
        stderr(&out)
    );

    // The dead input is reported once the rule is enabled; the file is
    // untouched.
    let on = "--rule=unused-parameter=warn";
    let out = sysmlv2(&["lint", on, input.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.contains("`radius`") && err.contains("[unused-parameter]"),
        "{err}"
    );
    assert_eq!(fs::read_to_string(&input).unwrap(), src);

    // --fix alone refuses the deletion and points at the guard flag.
    let out = sysmlv2(&["lint", on, "--fix", input.to_str().unwrap()]);
    assert!(stderr(&out).contains("--fix-deletes"), "{}", stderr(&out));
    assert_eq!(fs::read_to_string(&input).unwrap(), src);

    // --fix-deletes without --fix is a usage error.
    let out = sysmlv2(&["lint", "--fix-deletes", input.to_str().unwrap()]);
    assert!(!out.status.success());

    // The guarded pair deletes the parameter's whole line.
    let out = sysmlv2(&[
        "lint",
        on,
        "--fix",
        "--fix-deletes",
        input.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = fs::read_to_string(&input).unwrap();
    assert!(!text.contains("radius"), "{text}");
    assert!(text.contains("in force : Real;\n        return"), "{text}");
    // A re-lint is clean.
    let out = sysmlv2(&["lint", on, input.to_str().unwrap()]);
    assert!(out.status.success());
    assert!(
        !stderr(&out).contains("unused-parameter"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn lint_rule_overrides_and_config_findings() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-lint-rules-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package P { part def Wheel; part def Orphan; part w : Wheel; }\n",
    )
    .unwrap();

    // unused-definition is off by default…
    let out = sysmlv2(&["lint", input.to_str().unwrap()]);
    assert!(out.status.success());
    assert!(!stderr(&out).contains("Orphan"), "{}", stderr(&out));

    // …an override enables it, and error severity fails the run.
    let out = sysmlv2(&[
        "lint",
        "--rule",
        "unused-definition=error",
        input.to_str().unwrap(),
    ]);
    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(
        err.contains("`Orphan`") && err.contains("[unused-definition]"),
        "{err}"
    );
    assert!(!err.contains("`Wheel`"), "{err}");

    // A typo'd rule id is a finding, never a silent ignore.
    let out = sysmlv2(&["lint", "--rule", "no-such=warn", input.to_str().unwrap()]);
    assert!(
        stderr(&out).contains("unknown lint rule `no-such`"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn lint_directives_suppress_findings_and_report_unused_ones() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-lint-directives-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package P {\n    // sysmlint-disable-next-line naming-convention\n    part def widget_one;\n    part def Wheel; // sysmlint-disable-line naming-convention\n}\n",
    )
    .unwrap();

    // The directive above hides the casing finding; the trailing one
    // hides nothing and is reported, with the count of what was hidden.
    let out = sysmlv2(&["lint", input.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let err = stderr(&out);
    assert!(!err.contains("widget_one"), "{err}");
    assert!(
        err.contains(
            "`naming-convention` is not reported on line 4; the directive suppresses nothing \
             [lint-directive]"
        ),
        "{err}"
    );
    assert!(
        err.contains("1 finding(s) suppressed by directive"),
        "{err}"
    );

    // The JSON summary carries the count.
    let out = sysmlv2(&["lint", "--format", "json", input.to_str().unwrap()]);
    let v: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert_eq!(v["summary"]["suppressed"], 1, "{v}");
    assert_eq!(v["findings"][0]["rule"], "lint-directive", "{v}");

    // Removing the unused directive is a deleting fix.
    let out = sysmlv2(&["lint", "--fix", input.to_str().unwrap()]);
    assert!(
        stderr(&out).contains("1 deletion fix(es)"),
        "{}",
        stderr(&out)
    );
    let out = sysmlv2(&["lint", "--fix", "--fix-deletes", input.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(
        fs::read_to_string(&input).unwrap(),
        "package P {\n    // sysmlint-disable-next-line naming-convention\n    part def widget_one;\n    part def Wheel;\n}\n"
    );
}

#[test]
fn convert_json_back_to_text() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-lift-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package P { part def V; part v : V { attribute m : X = 1; } }",
    )
    .unwrap();
    let json_path = dir.join("m.json");

    let out = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-json",
        "-o",
        json_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));

    // JSON → text: parses and re-emits to identical JSON.
    let out = sysmlv2(&["convert", json_path.to_str().unwrap(), "--to", "text"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("part def V"), "{text}");
    let text_path = dir.join("m2.sysml");
    fs::write(&text_path, &text).unwrap();
    let out2 = sysmlv2(&[
        "convert",
        text_path.to_str().unwrap(),
        "--to",
        "compact-json",
    ]);
    assert!(out2.status.success());
    let json1 = fs::read_to_string(&json_path).unwrap();
    assert_eq!(
        stdout(&out2).trim(),
        json1.trim(),
        "round-trip JSON must be identical"
    );

    // JSON → compact-json is a normalization pass (identity for compact).
    let out3 = sysmlv2(&[
        "convert",
        json_path.to_str().unwrap(),
        "--to",
        "compact-json",
    ]);
    assert!(out3.status.success());
    assert_eq!(stdout(&out3).trim(), json1.trim());
}

#[test]
fn convert_with_library_uses_normative_ids() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-lib-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package M { import ScalarValues::*; attribute x : Real; }",
    )
    .unwrap();
    let out = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-json",
        "--lib",
        lib.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stdout(&out).contains("14c0aa22-5489-59b5-b438-ded26e83ba31"),
        "normative ScalarValues::Real ID missing"
    );
}

#[test]
fn convert_multi_file_one_root_namespace_per_file() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-multiconv-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("a.sysml"), "package A { part def P; }").unwrap();
    fs::write(
        dir.join("b.sysml"),
        "package B { private import A::*; part p : P; }",
    )
    .unwrap();
    let out = sysmlv2(&[
        "convert",
        "--to",
        "compact-json",
        dir.join("a.sysml").to_str().unwrap(),
        dir.join("b.sysml").to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let elements: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    let roots = elements
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| {
            e["@type"] == "Namespace" && e.get("owningRelationship").is_none_or(|v| v.is_null())
        })
        .count();
    assert_eq!(roots, 2, "one root namespace per input file");
    // Cross-file reference resolved: `p : P` must be an @id, not @ref.
    let txt = stdout(&out);
    assert!(
        !txt.contains("\"@ref\": \"P\""),
        "cross-file ref must resolve"
    );
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn convert_flexo_payload_round_trips_through_split() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-flexo-{}", std::process::id()));
    let outdir = dir.join("out");
    fs::create_dir_all(&outdir).unwrap();
    fs::write(
        dir.join("alpha.sysml"),
        "package Alpha { part def P; part p : P; }",
    )
    .unwrap();
    fs::write(dir.join("beta.sysml"), "package Beta { attribute b = 1; }").unwrap();

    // Commit direction: {payload, identity} records, roots named by file.
    let out = sysmlv2(&[
        "convert",
        "--to",
        "compact-json",
        "--flexo",
        dir.join("alpha.sysml").to_str().unwrap(),
        dir.join("beta.sysml").to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let records: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    let records = records.as_array().unwrap();
    assert!(
        records
            .iter()
            .all(|r| r.get("payload").is_some() && r.get("identity").is_some())
    );
    assert!(
        records
            .iter()
            .all(|r| r["identity"]["@id"] == r["payload"]["@id"])
    );
    let root_names: Vec<&str> = records
        .iter()
        .map(|r| &r["payload"])
        .filter(|p| p["@type"] == "Namespace")
        .filter_map(|p| p["qualifiedName"].as_str())
        .collect();
    assert_eq!(root_names, ["alpha.sysml", "beta.sysml"]);
    // Flexo shape: no null property values inside payloads.
    fn no_nulls(v: &serde_json::Value) -> bool {
        match v {
            serde_json::Value::Object(m) => m.values().all(no_nulls),
            serde_json::Value::Array(a) => a.iter().all(no_nulls),
            v => !v.is_null(),
        }
    }
    assert!(records.iter().all(|r| no_nulls(&r["payload"])));

    // Retrieval direction: --flexo unwraps, splits per root, names files.
    let json_path = dir.join("commit.json");
    fs::write(&json_path, serde_json::to_string(&records).unwrap()).unwrap();
    let out = sysmlv2(&[
        "convert",
        "--to",
        "text",
        "--flexo",
        json_path.to_str().unwrap(),
        "-o",
        outdir.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let alpha = fs::read_to_string(outdir.join("alpha.sysml")).unwrap();
    let beta = fs::read_to_string(outdir.join("beta.sysml")).unwrap();
    assert!(alpha.contains("package Alpha"));
    assert!(beta.contains("package Beta"));
    // Split files re-parse clean.
    let out = sysmlv2(&["check", outdir.join("alpha.sysml").to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn convert_flexo_derives_the_ownership_back_references_flexo_omits() {
    // Flexo MMS returns elements without `owningRelationship` and
    // `owningRelatedElement`. Under --flexo every JSON target reads such
    // a payload as it reads one carrying them; without it the payload is
    // refused rather than lifted with every owned element as a root.
    let dir = std::env::temp_dir().join(format!("sysmlv2-flexo-owning-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("alpha.sysml"),
        "package Alpha { part def P { part q; } part p : P; part r :> p.q; }",
    )
    .unwrap();
    fs::write(
        dir.join("beta.sysml"),
        "package Beta { private import Alpha::*; part b : P; }",
    )
    .unwrap();
    let out = sysmlv2(&[
        "convert",
        "--to",
        "compact-json",
        "--flexo",
        dir.join("alpha.sysml").to_str().unwrap(),
        dir.join("beta.sysml").to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let records: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    let mut stripped = records.clone();
    for record in stripped.as_array_mut().unwrap() {
        let payload = record["payload"].as_object_mut().unwrap();
        payload.remove("owningRelationship");
        payload.remove("owningRelatedElement");
    }
    let full_path = dir.join("full.json");
    let stripped_path = dir.join("stripped.json");
    fs::write(&full_path, records.to_string()).unwrap();
    fs::write(&stripped_path, stripped.to_string()).unwrap();

    let plain: Vec<&serde_json::Value> = stripped
        .as_array()
        .unwrap()
        .iter()
        .map(|r| &r["payload"])
        .collect();
    let plain_path = dir.join("plain.json");
    fs::write(&plain_path, serde_json::to_string(&plain).unwrap()).unwrap();
    for to in ["text", "compact-json", "full-json", "compact-cbor"] {
        let out = sysmlv2(&["convert", "--to", to, plain_path.to_str().unwrap()]);
        assert!(!out.status.success(), "--to {to}: {}", stdout(&out));
        assert!(
            stderr(&out).contains("omits the inverse ownership ends"),
            "--to {to}: {}",
            stderr(&out)
        );
    }

    for to in ["compact-json", "full-json", "compact-cbor"] {
        let read = |input: &Path| {
            let out = sysmlv2(&["convert", "--to", to, "--flexo", input.to_str().unwrap()]);
            assert!(out.status.success(), "--to {to}: {}", stderr(&out));
            out.stdout
        };
        assert_eq!(read(&stripped_path), read(&full_path), "--to {to}");
    }
    let split = |input: &Path, name: &str| {
        let outdir = dir.join(name);
        fs::create_dir_all(&outdir).unwrap();
        let out = sysmlv2(&[
            "convert",
            "--to",
            "text",
            "--flexo",
            input.to_str().unwrap(),
            "-o",
            outdir.to_str().unwrap(),
        ]);
        assert!(out.status.success(), "{}", stderr(&out));
        ["alpha.sysml", "beta.sysml"].map(|f| fs::read_to_string(outdir.join(f)).unwrap())
    };
    let from_stripped = split(&stripped_path, "from-stripped");
    assert_eq!(from_stripped, split(&full_path, "from-full"));
    assert!(
        from_stripped[0].contains("part r :> "),
        "{}",
        from_stripped[0]
    );
    let out = sysmlv2(&[
        "check",
        dir.join("from-stripped/alpha.sysml").to_str().unwrap(),
        dir.join("from-stripped/beta.sysml").to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn lift_drops_is_variable_on_usage_metaclasses() {
    // Some producers mark plain attribute usages `isVariable: true`;
    // `var` is a KerML-only prefix, so the lifted SysML must not print it.
    let dir = std::env::temp_dir().join(format!("sysmlv2-isvar-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let json = serde_json::json!([
        { "@type": "Namespace", "@id": "00000000-0000-0000-0000-00000000000a",
          "ownedRelationship": [ {"@id": "00000000-0000-0000-0000-00000000000b"} ] },
        { "@type": "OwningMembership", "@id": "00000000-0000-0000-0000-00000000000b",
          "owningRelatedElement": {"@id": "00000000-0000-0000-0000-00000000000a"},
          "ownedRelatedElement": [ {"@id": "00000000-0000-0000-0000-00000000000c"} ] },
        { "@type": "Package", "@id": "00000000-0000-0000-0000-00000000000c",
          "declaredName": "P",
          "owningRelationship": {"@id": "00000000-0000-0000-0000-00000000000b"},
          "ownedRelationship": [ {"@id": "00000000-0000-0000-0000-00000000000d"} ] },
        { "@type": "OwningMembership", "@id": "00000000-0000-0000-0000-00000000000d",
          "owningRelatedElement": {"@id": "00000000-0000-0000-0000-00000000000c"},
          "ownedRelatedElement": [ {"@id": "00000000-0000-0000-0000-00000000000e"} ] },
        { "@type": "AttributeUsage", "@id": "00000000-0000-0000-0000-00000000000e",
          "declaredName": "a", "isVariable": true,
          "owningRelationship": {"@id": "00000000-0000-0000-0000-00000000000d"} }
    ]);
    let path = dir.join("foreign-producer.json");
    fs::write(&path, serde_json::to_string(&json).unwrap()).unwrap();
    let out = sysmlv2(&["convert", "--to", "text", path.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(
        !text.contains("var "),
        "no `var` for AttributeUsage:\n{text}"
    );
    assert!(text.contains("attribute a"));
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn check_reports_unused_private_imports() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-unused-import-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let defs = dir.join("defs.sysml");
    let uses = dir.join("uses.sysml");
    fs::write(&defs, "package Defs { part def Wheel; }\n").unwrap();
    fs::write(
        &uses,
        "package U {\n    private import Defs::*;\n    part def P;\n}\n",
    )
    .unwrap();

    // Warning under plain check --lib (exit 0)…
    let out = sysmlv2(&[
        "check",
        defs.to_str().unwrap(),
        uses.to_str().unwrap(),
        "--lib",
        lib.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let err = stderr(&out);
    assert!(err.contains("unused private import"), "{err}");
    assert!(
        err.contains("uses.sysml:2"),
        "position points at the import: {err}"
    );

    // …failure under --strict.
    let out = sysmlv2(&[
        "check",
        "--strict",
        defs.to_str().unwrap(),
        uses.to_str().unwrap(),
        "--lib",
        lib.to_str().unwrap(),
    ]);
    assert!(!out.status.success());

    // As JSON: a referential-stage warning located in the second
    // input, although the library units come first in the model.
    let out = sysmlv2(&[
        "check",
        "--format",
        "json",
        defs.to_str().unwrap(),
        uses.to_str().unwrap(),
        "--lib",
        lib.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let doc: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("stdout is JSON");
    let f = doc["findings"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["message"] == "unused private import")
        .unwrap_or_else(|| panic!("{doc}"));
    assert_eq!(f["stage"], "referential");
    assert_eq!(f["severity"], "warn");
    assert_eq!(f["unit"], 1);
    assert_eq!(f["unitName"], uses.display().to_string());
    assert_eq!(f["line"], 2);
}

#[test]
fn check_strict_promotes_warnings_to_failure() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-strict-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    // Unresolved reference: a warning with --lib, silent without.
    let model = dir.join("m.sysml");
    fs::write(
        &model,
        "package P { private import Missing::*; part def D; }",
    )
    .unwrap();
    let lib_dir = dir.join("lib");
    fs::create_dir_all(&lib_dir).unwrap();
    fs::write(
        lib_dir.join("std.sysml"),
        "standard library package Base { part def B; }",
    )
    .unwrap();
    let lib = lib_dir.to_str().unwrap();
    let m = model.to_str().unwrap();

    // Default: warning, exit 0.
    let out = sysmlv2(&["check", "--lib", lib, m]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stderr(&out).contains("warning"), "{}", stderr(&out));

    // Strict: same findings, exit 1.
    let out = sysmlv2(&["check", "--strict", "--lib", lib, m]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("--strict: warnings are failures"));

    // Strict on a clean model still passes.
    let clean = dir.join("c.sysml");
    fs::write(&clean, "package Q { part def D; part d : D; }").unwrap();
    let out = sysmlv2(&["check", "--strict", "--lib", lib, clean.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn flexo_partial_model_round_trips_with_recovery() {
    // A work-in-progress model with unresolved references committed to
    // Flexo must be recoverable — the full-form payload carries
    // schema-valid TextualRepresentation annotations and the reverse
    // conversion restores the exact source references.
    let dir = std::env::temp_dir().join(format!("sysmlv2-recov-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let src = "package P {\n    private import Missing::*;\n    part def D;\n    part x : UnknownType;\n}";
    let model = dir.join("wip.sysml");
    fs::write(&model, src).unwrap();

    let out = sysmlv2(&[
        "convert",
        "--to",
        "full-json",
        "--flexo",
        model.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let payload = dir.join("commit.json");
    fs::write(&payload, stdout(&out)).unwrap();

    let out = sysmlv2(&[
        "convert",
        "--to",
        "text",
        "--flexo",
        payload.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("part x : UnknownType"), "{text}");
    assert!(text.contains("import Missing::*"), "{text}");
    assert!(!stderr(&out).contains("cannot name"), "{}", stderr(&out));
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn compact_json_rederives_to_full_preserving_ids() {
    // The compact→full re-derivation cell of the conversion matrix:
    // derived properties are recomputed in place, so every element keeps
    // its @id (a stored payload upgrades without breaking external
    // references to its elements).
    let dir = std::env::temp_dir().join(format!("sysmlv2-rederive-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let src =
        "package P {\n    port def K;\n    part a { port p : K; }\n    part b { port q : ~K; }\n}";
    let model = dir.join("m.sysml");
    fs::write(&model, src).unwrap();

    let out = sysmlv2(&["convert", "--to", "compact-json", model.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let compact_path = dir.join("m.json");
    fs::write(&compact_path, stdout(&out)).unwrap();

    let out = sysmlv2(&[
        "convert",
        "--to",
        "full-json",
        compact_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let compact: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&compact_path).unwrap()).unwrap();
    let full: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    let ids = |v: &serde_json::Value| -> std::collections::HashSet<String> {
        v.as_array()
            .unwrap()
            .iter()
            .filter_map(|e| e["@id"].as_str().map(str::to_string))
            .collect()
    };
    let (cids, fids) = (ids(&compact), ids(&full));
    assert!(
        cids.is_subset(&fids),
        "compact ids must survive re-derivation"
    );
    // Derived properties are present (spot-check the conjugated def).
    let conj = full
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["@type"] == "ConjugatedPortDefinition")
        .expect("~K present");
    assert_eq!(conj["isConjugated"], serde_json::Value::Bool(true));
    assert_eq!(conj["qualifiedName"].as_str().unwrap(), "P::K::'~K'");
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn kpar_round_trips_and_checks() {
    // KerML 10.3 project archives: pack textual units with .project.json
    // + .meta.json (index, SHA-256 checksums), then read them back
    // through check and convert.
    let dir = std::env::temp_dir().join(format!("sysmlv2-kpar-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("a.sysml"), "package A { part def X; }\n").unwrap();
    fs::write(dir.join("b.sysml"), "package B { part y : A::X; }\n").unwrap();
    let archive = dir.join("ab.kpar");

    let out = sysmlv2(&[
        "convert",
        "--to",
        "kpar",
        "-o",
        archive.to_str().unwrap(),
        dir.join("a.sysml").to_str().unwrap(),
        dir.join("b.sysml").to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));

    let out = sysmlv2(&["check", archive.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        !stderr(&out).contains("checksum"),
        "no checksum warnings expected: {}",
        stderr(&out)
    );

    let out = sysmlv2(&["convert", "--to", "compact-json", archive.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let els: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    let pkgs: Vec<&str> = els
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["@type"] == "Package")
        .filter_map(|e| e["declaredName"].as_str())
        .collect();
    assert_eq!(pkgs, ["A", "B"]);
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn kpar_reads_the_normative_archive() {
    // The SysML-v2-Release publishes the standard libraries as KPAR
    // files — the conformance oracle for the archive format. The blob
    // lives in the sparse spec-refs checkout's object store; self-skip
    // when it is not materializable (e.g. offline partial clone).
    let repo = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../spec-refs/SysML-v2-Release");
    let out = Command::new("git")
        .args([
            "-C",
            repo.to_str().unwrap(),
            "cat-file",
            "blob",
            "HEAD:sysml.library.kpar/Kernel_Data_Type_Library-1.0.0.kpar",
        ])
        .output();
    let Ok(out) = out else {
        eprintln!("skipping: git unavailable");
        return;
    };
    if !out.status.success() {
        eprintln!("skipping: normative kpar blob not materializable");
        return;
    }
    let dir = std::env::temp_dir().join(format!("sysmlv2-kpar-norm-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let archive = dir.join("kdt.kpar");
    fs::write(&archive, &out.stdout).unwrap();

    let out = sysmlv2(&["check", archive.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        !stderr(&out).contains("checksum"),
        "the normative checksums must verify: {}",
        stderr(&out)
    );
    let out = sysmlv2(&["convert", "--to", "compact-json", archive.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stdout(&out).contains("ScalarValues"));
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn query_finds_parts_by_usage_type() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-query-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package Demo {
            part def Wheel;
            part def Engine;
            part def Vehicle {
                attribute mass = 1200;
                part front : Wheel;
                part rear : Wheel;
                part engine : Engine;
            }
            part car : Vehicle[1];
        }",
    )
    .unwrap();

    // The motivating query: parts of Vehicle typed by Wheel, one element
    // per line as `qualified::name (Metaclass)`.
    let out = sysmlv2(&[
        "query",
        input.to_str().unwrap(),
        "ownedFeature(Demo::Vehicle)->select { in p; p istype Demo::Wheel }",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(
        stdout(&out),
        "Demo::Vehicle::front (PartUsage)\nDemo::Vehicle::rear (PartUsage)\n"
    );

    // Plain value query.
    let out = sysmlv2(&["query", input.to_str().unwrap(), "Demo::car.mass + 10"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "1210\n");

    // A malformed expression reports a diagnostic and exits 1.
    let out = sysmlv2(&["query", input.to_str().unwrap(), "1 +"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("<query>"), "{}", stderr(&out));

    // An unresolved reference exits 1.
    let out = sysmlv2(&["query", input.to_str().unwrap(), "Demo::nonexistent"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("unresolved"), "{}", stderr(&out));

    // Exactly one expression argument is required.
    let out = sysmlv2(&["query", input.to_str().unwrap(), "1 + 1", "2 + 2"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("exactly one"), "{}", stderr(&out));

    fs::remove_dir_all(&dir).ok();
}

#[test]
fn query_reads_multiple_files_and_stdin() {
    use std::io::Write as _;
    use std::process::Stdio;

    let dir = std::env::temp_dir().join(format!("sysmlv2-query-multi-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let defs = dir.join("defs.sysml");
    let uses = dir.join("uses.sysml");
    fs::write(&defs, "package Defs { part def Wheel; }").unwrap();
    fs::write(&uses, "package Uses { import Defs::*; part w : Wheel[1]; }").unwrap();

    // Cross-file query: both files form one model.
    let out = sysmlv2(&[
        "query",
        uses.to_str().unwrap(),
        defs.to_str().unwrap(),
        "Uses::w istype Defs::Wheel",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "true\n");

    // Stdin via `-`.
    let mut child = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .args(["query", "-", "size(ownedMember(P))"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .unwrap();
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"package P { part def A; part def B; }")
        .unwrap();
    let out = child.wait_with_output().unwrap();
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "2\n");

    fs::remove_dir_all(&dir).ok();
}

// --- viz -------------------------------------------------------------------

#[test]
fn viz_view_selects_diagram_and_unknown_view_fails() {
    let dir =
        std::env::temp_dir().join(format!("sysmlv2-cli-test-viz-view-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let model = dir.join("m.sysml");
    std::fs::write(
        &model,
        "package P {\n\
         \x20 part a { port p; }\n\
         \x20 part b { port q; }\n\
         \x20 connection c1 connect a.p to b.q;\n\
         \x20 state def S { state On; state Off; transition first On then Off; }\n\
         \x20 action def A { action s1; first s1 then done; }\n\
         \x20 part c { event occurrence e1; }\n\
         \x20 part d { event occurrence e2; }\n\
         \x20 message m1 from c.e1 to d.e2;\n\
         }",
    )
    .unwrap();

    let run = |view: &str| {
        let out = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
            .args(["viz", model.to_str().unwrap(), "--view", view])
            .output()
            .expect("run");
        assert!(out.status.success(), "view {view}");
        String::from_utf8(out.stdout).unwrap()
    };
    let ic = run("interconnection");
    assert!(ic.contains("rectangle"), "{ic}");
    assert!(ic.contains(" : c1\n"), "{ic}");
    // The short spellings name the same views.
    assert_eq!(run("ic"), ic);
    let state = run("state");
    assert!(state.contains("<<state def>>"), "{state}");
    assert!(state.contains("-->"), "{state}");
    let action = run("action");
    assert!(action.contains("<<action def>>"), "{action}");
    assert!(action.contains("--> [*]"), "{action}");
    let seq = run("sequence");
    assert!(seq.contains("participant"), "{seq}");
    assert!(seq.contains(" ->> "), "{seq}");
    assert!(seq.contains(" : m1"), "{seq}");
    assert_eq!(run("seq"), seq);
    let mixed = run("mixed");
    assert!(mixed.contains("rectangle"), "{mixed}");
    assert!(mixed.contains("<<state def>>"), "{mixed}");

    let out = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .args([
            "viz",
            model.to_str().unwrap(),
            "--color",
            "--line-style",
            "ortho",
            "--link-template",
            "x://{file}:{line}",
        ])
        .output()
        .expect("run");
    assert!(out.status.success());
    let styled = String::from_utf8(out.stdout).unwrap();
    assert!(styled.contains("skinparam linetype ortho"), "{styled}");
    assert!(styled.contains("BackgroundColor<<part def>>"), "{styled}");
    assert!(styled.contains("[[x://"), "{styled}");

    // A view or a routing the repertoire does not have is a usage
    // error, listing what is accepted, like any other enumerated option.
    for (flag, value) in [("--view", "usecase"), ("--line-style", "curvy")] {
        let out = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
            .args(["viz", model.to_str().unwrap(), flag, value])
            .output()
            .expect("run");
        assert!(!out.status.success());
        let err = String::from_utf8(out.stderr).unwrap();
        assert!(
            err.contains(&format!("invalid value '{value}' for '{flag}")),
            "{err}"
        );
        assert!(err.contains("possible values"), "{err}");
    }
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn viz_emits_structure_diagram_from_stdin() {
    let mut child = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .args(["viz", "-"])
        .stdin(std::process::Stdio::piped())
        .stdout(std::process::Stdio::piped())
        .spawn()
        .expect("spawn");
    use std::io::Write as _;
    child
        .stdin
        .take()
        .unwrap()
        .write_all(b"package P { part def A; part a : A; }")
        .unwrap();
    let out = child.wait_with_output().expect("wait");
    assert!(out.status.success());
    let text = String::from_utf8(out.stdout).unwrap();
    assert!(text.starts_with("@startuml\n"), "{text}");
    assert!(text.contains("<<part def>>"), "{text}");
    assert!(text.contains("..>"), "{text}");
    assert!(text.ends_with("@enduml\n"), "{text}");
}

#[test]
fn viz_element_scopes_and_unknown_element_fails() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-viz-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let model = dir.join("m.sysml");
    std::fs::write(
        &model,
        "package P { part def A { part def B; } part def C; }",
    )
    .unwrap();

    let out = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .args(["viz", model.to_str().unwrap(), "--element", "P::A"])
        .output()
        .expect("run");
    assert!(out.status.success());
    let text = String::from_utf8(out.stdout).unwrap();
    assert!(text.contains("\"A\""), "{text}");
    assert!(!text.contains("\"C\""), "{text}");

    let out = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .args(["viz", model.to_str().unwrap(), "--element", "P::Nope"])
        .output()
        .expect("run");
    assert!(!out.status.success());
    let err = String::from_utf8(out.stderr).unwrap();
    assert!(err.contains("element not found"), "{err}");
}

/// `viz --element` on a view usage draws in the style of the view's
/// rendering: its own `render` member's, else the one its definition
/// declares. `--view` overrides either.
#[test]
fn viz_element_view_takes_an_inherited_rendering() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-viz-rendering-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let model = dir.join("m.sysml");
    fs::write(
        &model,
        "package P {
            port def Jack;
            part def Amp { port line : Jack; }
            part def Speaker { port feed : Jack; }
            part rig {
                part amp : Amp;
                part main : Speaker;
                connect amp.line to main.feed;
            }
            view def Wiring { render Views::asInterconnectionDiagram; }
            view wiring : Wiring { expose rig; }
            view outline : Wiring {
                expose rig;
                render Views::asTreeDiagram;
            }
        }",
    )
    .unwrap();
    let (model, lib) = (model.to_str().unwrap(), lib.to_str().unwrap());
    let viz = |args: &[&str]| {
        let out = sysmlv2(&[&["viz", model, "--lib", lib], args].concat());
        assert!(out.status.success(), "{}", stderr(&out));
        stdout(&out)
    };
    // The rendering the definition declares: parts as blocks, with ports.
    let wiring = viz(&["--element", "P::wiring"]);
    assert!(wiring.contains("rectangle \"rig\""), "{wiring}");
    assert!(wiring.contains("port \"line : Jack\""), "{wiring}");
    // The view's own rendering wins over the inherited one.
    let outline = viz(&["--element", "P::outline"]);
    assert!(outline.contains("class \"rig\""), "{outline}");
    assert!(!outline.contains("port \""), "{outline}");
    // An explicit --view overrides an inherited rendering.
    let tree = viz(&["--element", "P::wiring", "--view", "tree"]);
    assert!(tree.contains("class \"rig\""), "{tree}");
}

#[test]
fn convert_min_qual_respells_references() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-minqual-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package Lib {\n\
         \x20   part def Wheel;\n\
         }\n\
         package Car {\n\
         \x20   private import Lib::*;\n\
         \x20   part w : Lib::Wheel;\n\
         }\n",
    )
    .unwrap();
    let json = dir.join("m.json");
    let out = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-json",
        "-o",
        json.to_str().unwrap(),
    ]);
    assert!(out.status.success());
    // Plain JSON → text prints the always-correct $::-rooted paths…
    let plain = sysmlv2(&["convert", json.to_str().unwrap(), "--to", "text"]);
    assert!(plain.status.success());
    assert!(
        stdout(&plain).contains("part w : $::Lib::Wheel;"),
        "{}",
        stdout(&plain)
    );
    // …and --min-qual respells them minimally, reparse-verified.
    let min = sysmlv2(&[
        "convert",
        json.to_str().unwrap(),
        "--to",
        "text",
        "--min-qual",
    ]);
    assert!(min.status.success());
    assert!(stdout(&min).contains("part w : Wheel;"), "{}", stdout(&min));
    // The flag guards its cell of the conversion matrix.
    let bad = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        "text",
        "--min-qual",
    ]);
    assert!(!bad.status.success());
}

#[test]
fn convert_compact_cbor_round_trip() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-cbor-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(&input, "package P { part def V; part v : V; }").unwrap();

    // text → compact-cbor (binary, via -o).
    let cbor_path = dir.join("m.s2c");
    let out = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "-o",
        cbor_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let bytes = fs::read(&cbor_path).unwrap();
    assert!(
        bytes.starts_with(sysmlv2_cbor::MAGIC),
        "payload opens with the RFC 9277 magic"
    );

    // The binary form re-expands to exactly the direct compact JSON.
    let out = sysmlv2(&[
        "convert",
        cbor_path.to_str().unwrap(),
        "--to",
        "compact-json",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let via_cbor: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    let out = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "compact-json"]);
    let direct: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert_eq!(via_cbor, direct);

    // …through the full-form re-derivation…
    let out = sysmlv2(&["convert", cbor_path.to_str().unwrap(), "--to", "full-json"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let via_cbor: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    let out = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "full-json"]);
    let direct: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert_eq!(via_cbor, direct);

    // …and all the way back to textual notation.
    let out = sysmlv2(&["convert", cbor_path.to_str().unwrap(), "--to", "text"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("part def V"), "lifted text:\n{text}");

    // CBOR to raw stdout matches the file bytes.
    let out = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "compact-cbor"]);
    assert!(out.status.success());
    assert_eq!(out.stdout, bytes);

    // --flexo wraps JSON change records; refused for the binary form.
    let out = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "--flexo",
    ]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("--flexo"));

    // A corrupt payload errors cleanly.
    fs::write(dir.join("bad.s2c"), [0x84, 0x19, 0xFF, 0xFF]).unwrap();
    let out = sysmlv2(&[
        "convert",
        dir.join("bad.s2c").to_str().unwrap(),
        "--to",
        "text",
    ]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("CBOR"));
}

#[test]
fn convert_full_cbor_matches_full_json() {
    let dir =
        std::env::temp_dir().join(format!("sysmlv2-cli-test-fullcbor-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(&input, "package P { part def V; part v : V; }").unwrap();

    let out = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "full-cbor"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let decoded = sysmlv2_cbor::from_full_cbor(&out.stdout).expect("full payload decodes");

    let out = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "full-json"]);
    let full: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert_eq!(decoded, full);

    // A full .s2c input normalizes to compact like full JSON input.
    let full_path = dir.join("m.s2c");
    fs::write(&full_path, sysmlv2_cbor::to_full_cbor(&full).unwrap()).unwrap();
    let out = sysmlv2(&[
        "convert",
        full_path.to_str().unwrap(),
        "--to",
        "compact-json",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let compact: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert!(compact.as_array().unwrap().len() < full.as_array().unwrap().len() + 1);
}

#[test]
fn convert_elide_ids_round_trips() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-elide-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package P { part def V; part v : V { attribute :>> x; } part def W { attribute x; } }",
    )
    .unwrap();

    let plain = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "compact-cbor"]);
    assert!(plain.status.success(), "{}", stderr(&plain));
    let elided = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "--elide-ids",
    ]);
    assert!(elided.status.success(), "{}", stderr(&elided));
    assert!(
        elided.stdout.len() < plain.stdout.len(),
        "elision shrinks the payload"
    );

    // The elided payload converts back to the identical compact JSON.
    let cbor_path = dir.join("m.s2c");
    fs::write(&cbor_path, &elided.stdout).unwrap();
    let via = sysmlv2(&[
        "convert",
        cbor_path.to_str().unwrap(),
        "--to",
        "compact-json",
    ]);
    assert!(via.status.success(), "{}", stderr(&via));
    let direct = sysmlv2(&["convert", input.to_str().unwrap(), "--to", "compact-json"]);
    assert_eq!(
        serde_json::from_str::<serde_json::Value>(&stdout(&via)).unwrap(),
        serde_json::from_str::<serde_json::Value>(&stdout(&direct)).unwrap()
    );

    // --elide-ids is a compact-cbor emit option.
    let out = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        "compact-json",
        "--elide-ids",
    ]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("--elide-ids"));
}

#[test]
fn convert_delta_emit_and_apply() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-delta-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let v1 = dir.join("v1.sysml");
    let v2 = dir.join("v2.sysml");
    fs::write(&v1, "package P { part def V; part v : V; }").unwrap();
    fs::write(
        &v2,
        "package P { part def V; part v : V; part def N { attribute x; } }",
    )
    .unwrap();

    // Base snapshot, then a delta of v2 against it.
    let base_path = dir.join("base.s2c");
    let out = sysmlv2(&[
        "convert",
        v1.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "-o",
        base_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let delta = sysmlv2(&[
        "convert",
        v2.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "--delta-base",
        base_path.to_str().unwrap(),
    ]);
    assert!(delta.status.success(), "{}", stderr(&delta));
    let full = sysmlv2(&["convert", v2.to_str().unwrap(), "--to", "compact-cbor"]);
    assert!(
        delta.stdout.len() < full.stdout.len(),
        "delta under snapshot"
    );

    // Apply the delta back through convert: delta.s2c + base → text.
    let delta_path = dir.join("delta.s2c");
    fs::write(&delta_path, &delta.stdout).unwrap();
    let out = sysmlv2(&[
        "convert",
        delta_path.to_str().unwrap(),
        "--delta-base",
        base_path.to_str().unwrap(),
        "--to",
        "text",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("part def N"), "applied model lifts: {text}");

    // Without the base, a delta input is refused with guidance.
    let out = sysmlv2(&["convert", delta_path.to_str().unwrap(), "--to", "text"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("--delta-base"), "{}", stderr(&out));

    // Wrong base refuses hard.
    let other = dir.join("other.s2c");
    let out = sysmlv2(&[
        "convert",
        v2.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "-o",
        other.to_str().unwrap(),
    ]);
    assert!(out.status.success());
    let out = sysmlv2(&[
        "convert",
        delta_path.to_str().unwrap(),
        "--delta-base",
        other.to_str().unwrap(),
        "--to",
        "text",
    ]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("base digest"), "{}", stderr(&out));
}

#[test]
fn convert_elided_delta_emit_and_apply() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-elided-delta-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let v1 = dir.join("v1.sysml");
    let v2 = dir.join("v2.sysml");
    fs::write(&v1, "package P { part def V; part v : V; }").unwrap();
    fs::write(
        &v2,
        "package P { part def V; part v : V; part def N { attribute x; } }",
    )
    .unwrap();
    let base_path = dir.join("base.s2c");
    let out = sysmlv2(&[
        "convert",
        v1.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "-o",
        base_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));

    // --elide-ids composes with --delta-base: created ids leave the wire.
    let explicit = sysmlv2(&[
        "convert",
        v2.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "--delta-base",
        base_path.to_str().unwrap(),
    ]);
    assert!(explicit.status.success(), "{}", stderr(&explicit));
    let elided = sysmlv2(&[
        "convert",
        v2.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "--delta-base",
        base_path.to_str().unwrap(),
        "--elide-ids",
    ]);
    assert!(elided.status.success(), "{}", stderr(&elided));
    assert!(
        elided.stdout.len() < explicit.stdout.len(),
        "elision shrinks the delta ({} < {})",
        elided.stdout.len(),
        explicit.stdout.len()
    );

    // The elided delta applies back to the same text.
    let delta_path = dir.join("delta.s2c");
    fs::write(&delta_path, &elided.stdout).unwrap();
    let out = sysmlv2(&[
        "convert",
        delta_path.to_str().unwrap(),
        "--delta-base",
        base_path.to_str().unwrap(),
        "--to",
        "text",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stdout(&out).contains("part def N"),
        "applied model lifts: {}",
        stdout(&out)
    );

    // A portable delta without a base is a usage error: the dependency
    // is declared on the argument.
    let out = sysmlv2(&[
        "convert",
        v2.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "--delta-portable",
    ]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("--delta-base"), "{}", stderr(&out));

    // Portable + elided is refused with guidance.
    let out = sysmlv2(&[
        "convert",
        v2.to_str().unwrap(),
        "--to",
        "compact-cbor",
        "--delta-base",
        base_path.to_str().unwrap(),
        "--delta-portable",
        "--elide-ids",
    ]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("strict deltas only"),
        "{}",
        stderr(&out)
    );
}

// ---------------------------------------------------------------------------
// Ambient model context: SYSMLV2_MODEL_DIR fills in
// omitted input files, SYSMLV2_LIB_DIR fills in --lib.

/// A model directory with two units (one nested), plus entries the
/// discovery walk must skip: a hidden directory and a non-model file.
fn ambient_dir(tag: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("sysmlv2-ambient-{tag}-{}", std::process::id()));
    fs::remove_dir_all(&dir).ok();
    fs::create_dir_all(dir.join("sub")).unwrap();
    fs::create_dir_all(dir.join(".hidden")).unwrap();
    fs::write(dir.join("a.sysml"), "package A { part def V; part v : V; }").unwrap();
    fs::write(dir.join("sub/b.kerml"), "package B { class C; }").unwrap();
    fs::write(dir.join(".hidden/h.sysml"), "this is not a model {").unwrap();
    fs::write(dir.join("notes.txt"), "not a model either").unwrap();
    dir
}

#[test]
fn ambient_model_dir_supplies_inputs_with_provenance() {
    let dir = ambient_dir("check");
    let env = [("SYSMLV2_MODEL_DIR", dir.to_str().unwrap())];

    // check: both units found (hidden + non-model entries skipped), and
    // the provenance line names the count, the directory, the variable.
    let out = sysmlv2_env(&["check"], &env);
    assert!(out.status.success(), "{}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.contains(&format!(
            "sysmlv2: model = 2 files from {} (SYSMLV2_MODEL_DIR)",
            dir.display()
        )),
        "missing/wrong provenance line:\n{err}"
    );

    // parse: per-file summaries in deterministic (sorted, depth-first)
    // order — a.sysml before sub/b.kerml.
    let out = sysmlv2_env(&["parse"], &env);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    let a = text.find("a.sysml:").expect("a.sysml summary");
    let b = text.find("b.kerml:").expect("b.kerml summary");
    assert!(a < b, "discovery order not deterministic:\n{text}");

    // --quiet suppresses the provenance note, nothing else.
    let out = sysmlv2_env(&["check", "-q"], &env);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        !stderr(&out).contains("sysmlv2: model ="),
        "{}",
        stderr(&out)
    );

    fs::remove_dir_all(&dir).ok();
}

#[test]
fn ambient_explicit_inputs_win() {
    // The ambient directory holds a file that would fail the run; an
    // explicit input must shadow it completely (and no provenance line
    // prints, because nothing was ambient).
    let dir = std::env::temp_dir().join(format!("sysmlv2-ambient-shadow-{}", std::process::id()));
    fs::remove_dir_all(&dir).ok();
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("broken.sysml"), "part def {").unwrap();
    let good = dir.join("good.txt"); // outside discovery, explicit only
    fs::write(&good, "package G { part def W; }").unwrap();

    let out = sysmlv2_env(
        &["check", good.to_str().unwrap()],
        &[("SYSMLV2_MODEL_DIR", dir.to_str().unwrap())],
    );
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        !stderr(&out).contains("sysmlv2: model ="),
        "{}",
        stderr(&out)
    );

    fs::remove_dir_all(&dir).ok();
}

#[test]
fn no_inputs_and_no_var_names_both_remedies() {
    for verb in ["check", "convert", "verify", "parse", "viz"] {
        let args: Vec<&str> = if verb == "convert" {
            vec![verb, "--to", "compact-json"]
        } else {
            vec![verb]
        };
        let out = sysmlv2(&args);
        assert!(!out.status.success(), "{verb} should fail without inputs");
        let err = stderr(&out);
        assert!(
            err.contains("provide input files") && err.contains("SYSMLV2_MODEL_DIR"),
            "`{verb}` error must name both remedies:\n{err}"
        );
    }
}

#[test]
fn ambient_empty_directory_reports_the_variable() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-ambient-empty-{}", std::process::id()));
    fs::remove_dir_all(&dir).ok();
    fs::create_dir_all(&dir).unwrap();
    let out = sysmlv2_env(&["check"], &[("SYSMLV2_MODEL_DIR", dir.to_str().unwrap())]);
    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(
        err.contains("no .sysml/.kerml files") && err.contains("SYSMLV2_MODEL_DIR"),
        "{err}"
    );
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn fmt_ambient_is_check_only() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-ambient-fmt-{}", std::process::id()));
    fs::remove_dir_all(&dir).ok();
    fs::create_dir_all(&dir).unwrap();
    let messy = "package  P{part def  V;}";
    fs::write(dir.join("m.sysml"), messy).unwrap();
    let env = [("SYSMLV2_MODEL_DIR", dir.to_str().unwrap())];

    // In-place fmt refuses ambient inputs outright — the file stays put.
    let out = sysmlv2_env(&["fmt"], &env);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("--check only"), "{}", stderr(&out));
    assert_eq!(fs::read_to_string(dir.join("m.sysml")).unwrap(), messy);

    // So does --stdout (it is not the read-only verification mode).
    let out = sysmlv2_env(&["fmt", "--stdout"], &env);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("--check only"), "{}", stderr(&out));

    // --check runs ambiently: exit 1 on the unformatted file, untouched.
    let out = sysmlv2_env(&["fmt", "--check"], &env);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("would reformat"), "{}", stderr(&out));
    assert_eq!(fs::read_to_string(dir.join("m.sysml")).unwrap(), messy);

    // And passes once the file is formatted (explicit rewrite first).
    let out = sysmlv2_env(&["fmt", dir.join("m.sysml").to_str().unwrap()], &env);
    assert!(out.status.success(), "{}", stderr(&out));
    let out = sysmlv2_env(&["fmt", "--check"], &env);
    assert!(out.status.success(), "{}", stderr(&out));

    fs::remove_dir_all(&dir).ok();
}

#[test]
fn ambient_eval_and_query_take_bare_expressions() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-ambient-eval-{}", std::process::id()));
    fs::remove_dir_all(&dir).ok();
    fs::create_dir_all(&dir).unwrap();
    fs::write(
        dir.join("m.sysml"),
        "package Demo { part def Wheel; part w : Wheel; attribute x = 2 + 3; }",
    )
    .unwrap();
    let env = [("SYSMLV2_MODEL_DIR", dir.to_str().unwrap())];

    // The leading positional is a qualified name, not a file.
    let out = sysmlv2_env(&["eval", "Demo::x"], &env);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stdout(&out).contains("Demo::x = 5"), "{}", stdout(&out));

    // --all with no positionals at all.
    let out = sysmlv2_env(&["eval", "--all"], &env);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stdout(&out).contains("x = 5"), "{}", stdout(&out));

    // The leading positional is the query expression.
    let out = sysmlv2_env(&["query", "Demo::x + 1"], &env);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "6\n");

    // Without the variable, the same invocations name both remedies.
    let out = sysmlv2(&["query", "Demo::x + 1"]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("SYSMLV2_MODEL_DIR"),
        "{}",
        stderr(&out)
    );

    fs::remove_dir_all(&dir).ok();
}

#[test]
fn lib_dir_env_enables_referential_checks() {
    let base = std::env::temp_dir().join(format!("sysmlv2-ambient-lib-{}", std::process::id()));
    fs::remove_dir_all(&base).ok();
    let lib = base.join("lib");
    let model = base.join("model");
    fs::create_dir_all(&lib).unwrap();
    fs::create_dir_all(&model).unwrap();
    fs::write(lib.join("l.kerml"), "package L { class Base; }").unwrap();
    // One resolvable library reference, one unresolved name: the warning
    // proves the referential stage actually ran off the env variable.
    fs::write(
        model.join("m.sysml"),
        "package P { part def V; part q : Missing; }",
    )
    .unwrap();
    let m = model.join("m.sysml");

    // Without any library the local referential stage still runs.
    let out = sysmlv2(&["check", m.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("Missing") && stderr(&out).contains("warning"),
        "{}",
        stderr(&out)
    );

    // SYSMLV2_LIB_DIR alone switches the referential stage on.
    let out = sysmlv2_env(
        &["check", m.to_str().unwrap()],
        &[
            ("SYSMLV2_LIB_DIR", lib.to_str().unwrap()),
            ("SYSMLV2_LIB_CACHE", "off"),
        ],
    );
    assert!(out.status.success(), "{}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.contains("Missing") && err.contains("warning"),
        "referential stage did not run via SYSMLV2_LIB_DIR:\n{err}"
    );

    fs::remove_dir_all(&base).ok();
}

#[test]
fn check_runs_model_semantics_without_a_library() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-no-lib-semantics-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("bad.sysml");
    fs::write(&input, "package P { part def D; part x : D[2..1]; }").unwrap();
    let out = sysmlv2(&["check", input.to_str().unwrap()]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("lower bound 2 exceeds upper bound 1"),
        "{}",
        stderr(&out)
    );
}

/// Help text with line wrapping collapsed, so assertions survive
/// clap's width-dependent layout.
fn flat(text: &str) -> String {
    text.split_whitespace().collect::<Vec<_>>().join(" ")
}

#[test]
fn help_documents_ambient_variables_statically() {
    // With no variable set: the long-about paragraph names both
    // variables, inputs render optional with the doc-comment wording,
    // and --lib carries its env tag.
    let out = sysmlv2(&["--help"]);
    assert!(out.status.success());
    let help = flat(&stdout(&out));
    assert!(help.contains("Ambient model context"), "{help}");
    assert!(
        help.contains("SYSMLV2_MODEL_DIR") && help.contains("SYSMLV2_LIB_DIR"),
        "{help}"
    );
    // The dynamic line's unique marker is its tail phrase — the static
    // long-about paragraph also contains "model context".
    assert!(
        !help.contains("file inputs may be omitted"),
        "no dynamic line when unset:\n{help}"
    );

    let out = sysmlv2(&["check", "--help"]);
    assert!(out.status.success());
    let help = flat(&stdout(&out));
    assert!(
        help.contains("[FILES]..."),
        "inputs must render optional:\n{help}"
    );
    assert!(
        help.contains("optional when SYSMLV2_MODEL_DIR is set"),
        "{help}"
    );
    assert!(help.contains("[env: SYSMLV2_LIB_DIR"), "{help}");
    assert!(!help.contains("file inputs may be omitted"), "{help}");
}

#[test]
fn help_echoes_active_ambient_context() {
    let dir = ambient_dir("help");
    let env = [("SYSMLV2_MODEL_DIR", dir.to_str().unwrap())];

    // Top level: the existing examples stay, the context line lands
    // after them with the directory and the live file count.
    let out = sysmlv2_env(&["--help"], &env);
    assert!(out.status.success());
    let help = flat(&stdout(&out));
    assert!(help.contains("EXAMPLES:"), "{help}");
    let idx_examples = help.find("EXAMPLES:").unwrap();
    let idx_context = help
        .find("file inputs may be omitted")
        .expect("context line missing");
    assert!(
        idx_context > idx_examples,
        "context line must trail the footer:\n{help}"
    );
    assert!(
        help.contains(&flat(&format!(
            "model context: {} (SYSMLV2_MODEL_DIR — 2 model files); file inputs may be omitted",
            dir.display()
        ))),
        "{help}"
    );

    // Ambient-honoring verbs echo it; fmt names its carve-out; lsp
    // takes no inputs and stays silent.
    let out = sysmlv2_env(&["check", "--help"], &env);
    let help = flat(&stdout(&out));
    assert!(
        help.contains("file inputs may be omitted") && help.contains("EXAMPLES:"),
        "{help}"
    );
    let out = sysmlv2_env(&["fmt", "--help"], &env);
    assert!(
        flat(&stdout(&out)).contains("omitted (--check only)"),
        "{}",
        stdout(&out)
    );
    let out = sysmlv2_env(&["lsp", "--help"], &env);
    assert!(
        !flat(&stdout(&out)).contains("file inputs may be omitted"),
        "{}",
        stdout(&out)
    );

    // An empty context directory still confirms, honestly.
    let empty = std::env::temp_dir().join(format!("sysmlv2-help-empty-{}", std::process::id()));
    fs::remove_dir_all(&empty).ok();
    fs::create_dir_all(&empty).unwrap();
    let out = sysmlv2_env(
        &["--help"],
        &[("SYSMLV2_MODEL_DIR", empty.to_str().unwrap())],
    );
    assert!(
        flat(&stdout(&out)).contains("no model files"),
        "{}",
        stdout(&out)
    );

    fs::remove_dir_all(&dir).ok();
    fs::remove_dir_all(&empty).ok();
}

// ---------------------------------------------------------------------------
// Inspection verbs: describe / members.

fn sysmlv2_in(cwd: &Path, args: &[&str], env: &[(&str, &str)]) -> Output {
    let mut cmd = Command::new(env!("CARGO_BIN_EXE_sysmlv2"));
    cmd.current_dir(cwd);
    cmd.env_remove("SYSMLV2_MODEL_DIR")
        .env_remove("SYSMLV2_LIB_DIR");
    for (k, v) in env {
        cmd.env(k, v);
    }
    cmd.args(args).output().expect("failed to run sysmlv2")
}

#[test]
fn describe_and_members_inspect_elements() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-inspect-{}", std::process::id()));
    fs::remove_dir_all(&dir).ok();
    fs::create_dir_all(&dir).unwrap();
    let defs = dir.join("defs.sysml");
    let veh = dir.join("veh.sysml");
    fs::write(&defs, "package Defs { part def Wheel; }").unwrap();
    fs::write(
        &veh,
        "package Veh { import Defs::*; part def Chassis; part w : Wheel; }",
    )
    .unwrap();

    let out = sysmlv2(&[
        "describe",
        defs.to_str().unwrap(),
        veh.to_str().unwrap(),
        "Veh::w",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    for line in [
        "Veh::w",
        "metaclass  PartUsage",
        "owner      Veh",
        "type       Defs::Wheel",
        // The import membership is not an owned member: two siblings.
        "position   2 of 2",
    ] {
        assert!(text.contains(line), "describe missing {line:?}:\n{text}");
    }
    assert!(
        text.contains("location") && text.contains("veh.sysml:1:"),
        "{text}"
    );

    let out = sysmlv2(&[
        "members",
        defs.to_str().unwrap(),
        veh.to_str().unwrap(),
        "Veh",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    let lines: Vec<&str> = text.lines().collect();
    // Owned members in declaration order, name column padded.
    assert_eq!(lines.len(), 2, "{text}");
    assert!(lines[0].starts_with("Chassis "), "{text}");
    assert!(lines[0].ends_with("PartDefinition"), "{text}");
    assert!(lines[1].starts_with("w "), "{text}");
    assert!(lines[1].ends_with("PartUsage"), "{text}");

    // Unresolved name exits 1; a missing qualified name is its own error.
    let out = sysmlv2(&["describe", veh.to_str().unwrap(), "Veh::nope"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("cannot resolve"), "{}", stderr(&out));
    let out = sysmlv2(&["members", veh.to_str().unwrap()]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("exactly one qualified name"),
        "{}",
        stderr(&out)
    );

    fs::remove_dir_all(&dir).ok();
}

#[test]
fn ambient_describe_and_members_take_bare_names() {
    // The model directory is named like the root package (a real
    // hazard on case-insensitive filesystems): the bare qualified name
    // must classify as a name — only an existing *file* counts as an
    // explicit input.
    let base = std::env::temp_dir().join(format!("sysmlv2-inspect-amb-{}", std::process::id()));
    fs::remove_dir_all(&base).ok();
    let model = base.join("demo");
    fs::create_dir_all(&model).unwrap();
    fs::write(
        model.join("m.sysml"),
        "package Demo { part def V; part v : V; }",
    )
    .unwrap();
    let env = [("SYSMLV2_MODEL_DIR", "demo")];

    let out = sysmlv2_in(&base, &["-q", "members", "Demo"], &env);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(
        text.contains("V ") && text.contains("PartDefinition"),
        "{text}"
    );
    assert!(text.contains("v ") && text.contains("PartUsage"), "{text}");

    let out = sysmlv2_in(&base, &["-q", "describe", "Demo::v"], &env);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(
        text.contains("metaclass  PartUsage") && text.contains("type       Demo::V"),
        "{text}"
    );

    fs::remove_dir_all(&base).ok();
}

#[test]
fn payload_reports_digests_and_finds_delta_bases() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-payload-{}", std::process::id()));
    fs::remove_dir_all(&dir).ok();
    let snaps = dir.join("snaps");
    fs::create_dir_all(&snaps).unwrap();
    fs::write(dir.join("a.sysml"), "package P { part def V; part v : V; }").unwrap();
    fs::write(
        dir.join("b.sysml"),
        "package P { part def V; part v : V; part w : V; }",
    )
    .unwrap();
    // A decoy snapshot the base scan must not match.
    fs::write(dir.join("c.sysml"), "package Q { part def X; }").unwrap();
    let a_s2c = snaps.join("a.s2c");
    let c_s2c = snaps.join("c.s2c");
    let edit = dir.join("edit.s2c");
    for (src, base, out) in [
        ("a.sysml", None, &a_s2c),
        ("c.sysml", None, &c_s2c),
        ("b.sysml", Some(&a_s2c), &edit),
    ] {
        let src = dir.join(src);
        let mut args = vec!["convert", src.to_str().unwrap(), "--to", "compact-cbor"];
        if let Some(base) = base {
            args.extend(["--delta-base", base.to_str().unwrap()]);
        }
        args.extend(["-o", out.to_str().unwrap()]);
        let run = sysmlv2(&args);
        assert!(run.status.success(), "{}", stderr(&run));
    }

    // Snapshot summary carries its state digest.
    let out = sysmlv2(&["payload", a_s2c.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let summary: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("valid JSON");
    assert_eq!(summary["form"], "compact");
    let digest = summary["stateDigest"]
        .as_str()
        .expect("state digest")
        .to_string();

    // Delta summary: base digest equals that state digest, and the
    // directory scan pins exactly the matching snapshot.
    let out = sysmlv2(&[
        "payload",
        edit.to_str().unwrap(),
        "--find-base",
        snaps.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let summary: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("valid JSON");
    assert_eq!(summary["form"], "delta");
    assert_eq!(summary["delta"]["baseDigest"].as_str().unwrap(), digest);
    let matches = summary["delta"]["baseMatches"].as_array().unwrap();
    assert_eq!(matches.len(), 1, "one matching base: {matches:?}");
    assert_eq!(matches[0].as_str().unwrap(), a_s2c.to_str().unwrap());

    // No snapshot matches → the verb fails, so it scripts as a check.
    let empty = dir.join("empty");
    fs::create_dir_all(&empty).unwrap();
    let out = sysmlv2(&[
        "payload",
        edit.to_str().unwrap(),
        "--find-base",
        empty.to_str().unwrap(),
    ]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("no snapshot"), "{}", stderr(&out));

    fs::remove_dir_all(&dir).ok();
}

#[test]
fn payload_delta_from_pairs_by_id_and_applies_back() {
    // The payload-identity diff: a rename with stable ids is a pure
    // update (the model-deriving `convert --delta-base` path would
    // re-derive and rebase ids, splitting the rename into
    // delete+create). Claims ride the delta; --apply-to reproduces the
    // target exactly, digest-verified.
    let dir = std::env::temp_dir().join(format!("sysmlv2-pdelta-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let model = dir.join("m.sysml");
    fs::write(&model, "package P {\n    part def A;\n    part a : A;\n}").unwrap();
    let out = sysmlv2(&["convert", "--to", "compact-json", model.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let base_path = dir.join("base.json");
    fs::write(&base_path, stdout(&out)).unwrap();

    // Rename one element in place — every @id untouched.
    let mut target: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    let mut renamed = 0;
    for e in target.as_array_mut().unwrap() {
        if e["declaredName"] == "A" {
            e["declaredName"] = serde_json::json!("Renamed");
            renamed += 1;
        }
    }
    assert_eq!(renamed, 1);
    let target_path = dir.join("target.json");
    fs::write(&target_path, serde_json::to_string(&target).unwrap()).unwrap();

    let delta_path = dir.join("edit.s2c");
    let out = sysmlv2(&[
        "payload",
        target_path.to_str().unwrap(),
        "--delta-from",
        base_path.to_str().unwrap(),
        "--claim-project",
        "11111111-1111-1111-1111-111111111111",
        "--claim-service",
        "urn:example:svc",
        "-o",
        delta_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));

    let out = sysmlv2(&["payload", delta_path.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let summary: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert_eq!(summary["delta"]["changes"]["updates"], 1, "{summary}");
    assert_eq!(summary["delta"]["changes"]["creates"], 0, "{summary}");
    assert_eq!(summary["delta"]["changes"]["deletes"], 0, "{summary}");
    let claims = summary["delta"]["claims"].as_array().unwrap();
    assert!(
        claims
            .iter()
            .any(|c| c["key"] == 0 && c["id"] == "11111111-1111-1111-1111-111111111111"),
        "{claims:?}"
    );
    assert!(
        claims
            .iter()
            .any(|c| c["key"] == 2 && c["text"] == "urn:example:svc"),
        "{claims:?}"
    );

    // Apply back: result == target element-for-element, and the
    // report's result digest is the target's own state digest.
    let applied_path = dir.join("applied.json");
    let out = sysmlv2(&[
        "payload",
        delta_path.to_str().unwrap(),
        "--apply-to",
        base_path.to_str().unwrap(),
        "-o",
        applied_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let report: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert_eq!(report["baseMatched"], true, "{report}");
    let out = sysmlv2(&["payload", target_path.to_str().unwrap()]);
    let target_summary: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert_eq!(report["resultDigest"], target_summary["stateDigest"]);
    let applied: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&applied_path).unwrap()).unwrap();
    let ids = |v: &serde_json::Value| -> Vec<String> {
        let mut ids: Vec<String> = v
            .as_array()
            .unwrap()
            .iter()
            .map(|e| e["@id"].as_str().unwrap().to_string())
            .collect();
        ids.sort();
        ids
    };
    assert_eq!(ids(&applied), ids(&target));
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn payload_ids_prints_the_delta_canonical_sequence() {
    // --ids exposes the strict-delta index space: the sequence is the
    // same for a compact .json and its .s2c encoding, one entry per
    // element, alongside the state digest.
    let dir = std::env::temp_dir().join(format!("sysmlv2-pids-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let model = dir.join("m.sysml");
    fs::write(&model, "package P {\n    part def A;\n    part a : A;\n}").unwrap();
    let out = sysmlv2(&["convert", "--to", "compact-json", model.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let json_path = dir.join("m.json");
    fs::write(&json_path, stdout(&out)).unwrap();
    let s2c_path = dir.join("m.s2c");
    let out = sysmlv2(&[
        "convert",
        "--to",
        "compact-cbor",
        json_path.to_str().unwrap(),
        "-o",
        s2c_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));

    let seq = |path: &Path| -> serde_json::Value {
        let out = sysmlv2(&["payload", path.to_str().unwrap(), "--ids"]);
        assert!(out.status.success(), "{}", stderr(&out));
        serde_json::from_str(&stdout(&out)).unwrap()
    };
    let from_json = seq(&json_path);
    let from_s2c = seq(&s2c_path);
    assert_eq!(from_json["ids"], from_s2c["ids"]);
    assert_eq!(from_json["stateDigest"], from_s2c["stateDigest"]);
    assert_eq!(
        from_json["ids"].as_array().unwrap().len(),
        usize::try_from(from_json["elements"].as_u64().unwrap()).unwrap()
    );
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn payload_tables_exports_the_versioned_codec_artifact() {
    // The vendorable tables artifact: one self-contained JSON document
    // carrying everything a consumer needs to label s2c structure —
    // magic, version axes, flags, kind legend, both ordinal spaces
    // with presence defaults, and the enum vocabularies.
    let out = sysmlv2(&["payload", "--tables"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let doc: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert_eq!(doc["magic"], "d9d9f7da24533243");
    for axis in ["layout", "tables", "scheme"] {
        assert!(doc["versions"][axis].as_u64().unwrap() >= 1, "{axis}");
    }
    assert_eq!(doc["flags"]["delta"], 4);
    assert_eq!(doc["flags"]["explicitIds"], 64);
    assert_eq!(doc["kinds"]["bool"], 0);
    let metaclasses = doc["metaclasses"].as_array().unwrap();
    assert!(metaclasses.len() > 100);
    assert_eq!(
        metaclasses.len(),
        doc["fullMetaclasses"].as_array().unwrap().len(),
        "both ordinal spaces cover the concrete metaclasses"
    );
    // Wire code = array position, spelled explicitly too.
    for (i, m) in metaclasses.iter().enumerate().take(5) {
        assert_eq!(m["code"], i as u64);
    }
    // Presence defaults where the kind has one.
    let ns = metaclasses
        .iter()
        .find(|m| m["name"] == "Namespace")
        .expect("Namespace is concrete");
    let is_implied = ns["fields"]
        .as_array()
        .unwrap()
        .iter()
        .find(|f| f["prop"] == "isImpliedIncluded")
        .unwrap();
    assert_eq!(is_implied["kind"], 0);
    assert_eq!(is_implied["default"], false);
    let vk = doc["enums"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["name"] == "VisibilityKind")
        .unwrap();
    assert_eq!(
        vk["values"].as_array().unwrap().len(),
        3,
        "closed vocabulary present"
    );
    // Inputs are refused — the artifact is not payload-specific.
    let out = sysmlv2(&["payload", "--tables", "whatever.s2c"]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("no payload inputs"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn convert_library_exports_the_resolved_stdlib() {
    // --library emits the standard library itself: every element of
    // the --lib units under its normative KerML 9.1 id, internally
    // complete (no dangling references), and digest-identical between
    // the JSON and s2c encodings. The complement of a normal
    // conversion, whose library references dangle by design and land
    // exactly on this export's ids.
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let lib = lib.to_str().unwrap().to_string();
    let dir = std::env::temp_dir().join(format!("sysmlv2-libexp-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let json_path = dir.join("stdlib.json");
    let out = sysmlv2(&[
        "convert",
        "--library",
        "--lib",
        &lib,
        "--to",
        "compact-json",
        "-o",
        json_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let els: serde_json::Value =
        serde_json::from_str(&fs::read_to_string(&json_path).unwrap()).unwrap();
    let els = els.as_array().unwrap();
    assert!(els.len() > 50_000, "{} elements", els.len());
    let ids: std::collections::HashSet<&str> =
        els.iter().map(|e| e["@id"].as_str().unwrap()).collect();
    assert!(
        ids.contains("14c0aa22-5489-59b5-b438-ded26e83ba31"),
        "normative ScalarValues::Real id"
    );
    // Internally complete: every reference lands on an exported element.
    let mut owned: std::collections::HashSet<&str> = std::collections::HashSet::new();
    for e in els {
        for (_, v) in e.as_object().unwrap() {
            match v {
                serde_json::Value::Object(o) => {
                    if let Some(r) = o.get("@id").and_then(serde_json::Value::as_str) {
                        assert!(ids.contains(r), "dangling ref {r}");
                    }
                }
                serde_json::Value::Array(a) => {
                    for x in a {
                        if let Some(r) = x.get("@id").and_then(serde_json::Value::as_str) {
                            assert!(ids.contains(r), "dangling ref {r}");
                        }
                    }
                }
                _ => {}
            }
        }
        for k in ["ownedRelationship", "ownedRelatedElement"] {
            for x in e
                .get(k)
                .and_then(serde_json::Value::as_array)
                .into_iter()
                .flatten()
            {
                owned.insert(x["@id"].as_str().unwrap());
            }
        }
    }
    // The unowned roots are exactly the per-unit namespaces.
    let roots: Vec<&serde_json::Value> = els
        .iter()
        .filter(|e| !owned.contains(e["@id"].as_str().unwrap()))
        .collect();
    assert!(roots.len() > 50, "{} unit roots", roots.len());
    assert!(
        roots.iter().all(|e| e["@type"] == "Namespace"),
        "every unowned root is a unit namespace"
    );

    // The s2c encoding digests identically to the JSON export.
    let s2c_path = dir.join("stdlib.s2c");
    let out = sysmlv2(&[
        "convert",
        "--library",
        "--lib",
        &lib,
        "--to",
        "compact-cbor",
        "-o",
        s2c_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let digest_of = |p: &Path| -> String {
        let out = sysmlv2(&["payload", p.to_str().unwrap()]);
        assert!(out.status.success(), "{}", stderr(&out));
        let d: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
        d["stateDigest"].as_str().unwrap().to_string()
    };
    assert_eq!(digest_of(&json_path), digest_of(&s2c_path));

    // Guards: --library without --lib, with inputs, or to a textual
    // target refuses cleanly.
    let out = sysmlv2(&["convert", "--library", "--to", "compact-json"]);
    assert!(!out.status.success());
    let out = sysmlv2(&[
        "convert",
        "--library",
        "--lib",
        &lib,
        "--to",
        "compact-json",
        "some-model.sysml",
    ]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("no inputs"), "{}", stderr(&out));
    let out = sysmlv2(&["convert", "--library", "--lib", &lib, "--to", "text"]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("compact-json, compact-cbor, full-json or full-cbor"),
        "{}",
        stderr(&out)
    );
    // The conversion flags --library does not compose with are declared
    // on the argument, so the combination is a usage error.
    for flag in ["--flexo", "--min-qual", "--elide-ids"] {
        let out = sysmlv2(&[
            "convert",
            "--library",
            "--lib",
            &lib,
            "--to",
            "compact-json",
            flag,
        ]);
        assert!(!out.status.success());
        assert!(
            stderr(&out).contains(&format!("cannot be used with '{flag}'")),
            "{}",
            stderr(&out)
        );
    }
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn convert_library_full_form_validates_and_carries_the_heritage() {
    // --library --to full-json: the standard library itself in the full
    // form — every element of the --lib units with its derived
    // properties and the implied relationships the prepared library
    // materialized, schema-valid, internally complete but for the
    // library's own unresolved spellings (which ride recovery notes as
    // a user model's do), and under a closure level the inherited
    // memberships of its types.
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let lib = lib.to_str().unwrap().to_string();
    let dir = std::env::temp_dir().join(format!("sysmlv2-libfull-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let export = |name: &str, extra: &[&str]| -> Vec<serde_json::Value> {
        let path = dir.join(name);
        let mut args = vec![
            "convert",
            "--library",
            "--lib",
            &lib,
            "--to",
            "full-json",
            "-o",
            path.to_str().unwrap(),
        ];
        args.extend_from_slice(extra);
        let out = sysmlv2_env(&args, &[("SYSMLV2_AMBIENT", "off")]);
        assert!(out.status.success(), "{}", stderr(&out));
        let text = fs::read_to_string(&path).unwrap();
        fs::remove_file(&path).ok();
        match serde_json::from_str::<serde_json::Value>(&text).unwrap() {
            serde_json::Value::Array(els) => els,
            other => panic!("not an element array: {other}"),
        }
    };
    let els = export("stdlib-full.json", &[]);
    assert!(els.len() > 150_000, "{} elements", els.len());
    let ids: std::collections::HashSet<&str> =
        els.iter().map(|e| e["@id"].as_str().unwrap()).collect();
    assert_eq!(ids.len(), els.len(), "ids are unique");
    assert!(
        ids.contains("14c0aa22-5489-59b5-b438-ded26e83ba31"),
        "normative ScalarValues::Real id"
    );
    // The prepared library's implied relationships are in the array and
    // under their owners.
    let implied: Vec<&serde_json::Value> = els.iter().filter(|e| e["isImplied"] == true).collect();
    assert!(
        implied.len() > 50_000,
        "{} implied relationships",
        implied.len()
    );
    assert!(els.iter().all(|e| e["isImpliedIncluded"] == true));
    let by_id: std::collections::HashMap<&str, &serde_json::Value> = els
        .iter()
        .map(|e| (e["@id"].as_str().unwrap(), e))
        .collect();
    for rel in implied.iter().take(500) {
        // Owned by an element (a specialization, a redefinition) or, a
        // connector, by a membership: either owner lists it.
        let (owner, list) = match rel["owningRelatedElement"]["@id"].as_str() {
            Some(owner) => (owner, "ownedRelationship"),
            None => (
                rel["owningRelationship"]["@id"].as_str().unwrap(),
                "ownedRelatedElement",
            ),
        };
        let listed = by_id[owner][list]
            .as_array()
            .unwrap()
            .iter()
            .any(|r| r["@id"] == rel["@id"]);
        assert!(listed, "{owner}.{list} lists its implied {}", rel["@id"]);
    }
    // Internally complete, but for the library's own unresolved
    // spellings: every dangling id is one a recovery note spells.
    let noted: std::collections::HashSet<String> = els
        .iter()
        .filter(|e| e["language"] == "x-sysmlv2-unresolved-reference")
        .map(|e| {
            uuid::Uuid::new_v5(
                &uuid::Uuid::NAMESPACE_OID,
                format!("unresolved:{}", e["body"].as_str().unwrap()).as_bytes(),
            )
            .to_string()
        })
        .collect();
    let mut dangling = std::collections::BTreeSet::new();
    for e in &els {
        for (_, v) in e.as_object().unwrap() {
            let refs = v
                .as_array()
                .map(Vec::as_slice)
                .unwrap_or(std::slice::from_ref(v));
            for r in refs {
                if let Some(id) = r.get("@id").and_then(serde_json::Value::as_str) {
                    if !ids.contains(id) && !noted.contains(id) {
                        dangling.insert(id.to_string());
                    }
                }
            }
        }
    }
    assert!(dangling.is_empty(), "dangling references: {dangling:?}");
    // Schema-valid, the same check the corpus full form passes, with the
    // one documented departure (INTEROP.md): a numeric literal no JSON
    // number denotes exactly keeps its own spelling as a string where the
    // schema wants a number (the library's `pi` carries one such).
    let schema = sysmlv2_testkit::published_schema();
    let failures: Vec<String> = sysmlv2_testkit::validate_elements(&schema, &els)
        .into_iter()
        .filter(|f| {
            !(f.starts_with("LiteralRational @ /value: \"")
                || f.starts_with("LiteralInteger @ /value: \""))
        })
        .collect();
    assert!(
        failures.is_empty(),
        "{} schema violations:\n{}",
        failures.len(),
        failures.join("\n")
    );
    // Parts::Part: its own features at the passthrough level, the
    // inherited ones under a closure level.
    let part = els
        .iter()
        .find(|e| e["qualifiedName"] == "Parts::Part")
        .expect("Parts::Part");
    assert_eq!(part["ownedFeature"].as_array().unwrap().len(), 8);
    assert_eq!(part["inheritedFeature"], serde_json::json!([]));
    let closed = export("stdlib-full-closure.json", &["--closures", "closure"]);
    assert_eq!(
        closed.len(),
        els.len(),
        "a closure level adds values, never rows"
    );
    let part = closed
        .iter()
        .find(|e| e["qualifiedName"] == "Parts::Part")
        .expect("Parts::Part");
    let inherited = part["inheritedFeature"].as_array().unwrap();
    assert!(
        inherited.len() > 50,
        "{} inherited features",
        inherited.len()
    );
    let names: Vec<&str> = inherited
        .iter()
        .filter_map(|r| closed.iter().find(|e| e["@id"] == r["@id"]))
        .filter_map(|e| e["declaredName"].as_str())
        .collect();
    assert!(
        names.contains(&"portionOf") && names.contains(&"timeEnclosedOccurrences"),
        "Occurrences and Items features arrive through the written heritage: {names:?}"
    );
    assert_eq!(
        part["feature"].as_array().unwrap().len(),
        8 + inherited.len()
    );
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn convert_closures_writes_the_inheritance_closures_on_request() {
    // The default full form is the passthrough level: `[]` for the four
    // closure names and the owned side for `feature`, whatever
    // `isImpliedIncluded` says. `--closures closure` writes the
    // specification's values over the written heritage, `closure-implied`
    // with the implied library heritage too; neither adds a row or moves
    // an id. The option belongs to the full form alone.
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let lib = lib.to_str().unwrap().to_string();
    let dir = std::env::temp_dir().join(format!("sysmlv2-closures-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let model = dir.join("export.sysml");
    fs::write(
        &model,
        "package Export {\n    port def Out { out attribute v : ScalarValues::Real; }\n    part def Box {\n        port i : ~Out;\n        attribute a : ScalarValues::Real = 1.0;\n        attribute sum : ScalarValues::Real = a + 2.0;\n    }\n    part def Big :> Box;\n}\n",
    )
    .unwrap();
    let export = |closures: Option<&str>| -> Vec<serde_json::Value> {
        let mut args = vec![
            "convert",
            model.to_str().unwrap(),
            "--to",
            "full-json",
            "--lib",
            &lib,
        ];
        if let Some(level) = closures {
            args.extend(["--closures", level]);
        }
        let out = sysmlv2(&args);
        assert!(out.status.success(), "{}", stderr(&out));
        serde_json::from_str::<serde_json::Value>(&stdout(&out))
            .unwrap()
            .as_array()
            .unwrap()
            .clone()
    };
    let big = |els: &[serde_json::Value]| -> serde_json::Value {
        els.iter()
            .find(|e| e["declaredName"] == "Big")
            .expect("Big")
            .clone()
    };
    let default = export(None);
    let passthrough = export(Some("passthrough"));
    assert_eq!(default, passthrough, "passthrough is the default");
    let b = big(&default);
    assert_eq!(b["isImpliedIncluded"], true);
    assert_eq!(b["inheritedMembership"], serde_json::json!([]));
    assert_eq!(b["inheritedFeature"], serde_json::json!([]));
    assert_eq!(b["feature"], serde_json::json!([]));
    let written = export(Some("closure"));
    let b = big(&written);
    assert_eq!(b["inheritedMembership"].as_array().unwrap().len(), 3);
    assert_eq!(b["inheritedFeature"].as_array().unwrap().len(), 3);
    assert_eq!(b["feature"].as_array().unwrap().len(), 3);
    let implied = export(Some("closure-implied"));
    let b = big(&implied);
    assert!(
        b["inheritedMembership"].as_array().unwrap().len() > 50,
        "{}",
        b["inheritedMembership"]
    );
    // Values only: the rows and their ids are the default's.
    let ids = |els: &[serde_json::Value]| -> Vec<String> {
        els.iter()
            .map(|e| e["@id"].as_str().unwrap().to_string())
            .collect()
    };
    assert_eq!(ids(&default), ids(&written));
    assert_eq!(ids(&default), ids(&implied));
    // Without a library (the single-unit path) the written heritage is
    // still there, and the ids are the default export's at every level.
    let export_nolib = |closures: Option<&str>| -> Vec<serde_json::Value> {
        let mut args = vec!["convert", model.to_str().unwrap(), "--to", "full-json"];
        if let Some(level) = closures {
            args.extend(["--closures", level]);
        }
        let out = sysmlv2(&args);
        assert!(out.status.success(), "{}", stderr(&out));
        serde_json::from_str::<serde_json::Value>(&stdout(&out))
            .unwrap()
            .as_array()
            .unwrap()
            .clone()
    };
    let nolib_default = export_nolib(None);
    let nolib_written = export_nolib(Some("closure"));
    let nolib_implied = export_nolib(Some("closure-implied"));
    assert_eq!(ids(&nolib_default), ids(&nolib_written));
    assert_eq!(ids(&nolib_default), ids(&nolib_implied));
    assert_eq!(
        big(&nolib_default)["inheritedFeature"],
        serde_json::json!([])
    );
    let b = big(&nolib_written);
    assert_eq!(b["inheritedFeature"].as_array().unwrap().len(), 3);
    assert_eq!(nolib_default.len(), nolib_written.len());
    // A compact target has no closures to write.
    let out = sysmlv2(&[
        "convert",
        model.to_str().unwrap(),
        "--to",
        "compact-json",
        "--closures",
        "closure",
    ]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("--closures applies to --to full-json or full-cbor"),
        "{}",
        stderr(&out)
    );
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn payload_encode_is_payload_identity_pure() {
    // --encode is the store-side inverse of a snapshot decode: the
    // producer's ids and content are authoritative, so the encoded
    // payload digests identically to its JSON source — including for
    // payloads whose ids no session derivation would mint (a store's
    // own identity space).
    let dir = std::env::temp_dir().join(format!("sysmlv2-pencode-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let foreign = serde_json::json!([{
        "@type": "Package",
        "@id": "0f0e0d0c-0b0a-0908-0706-050403020100",
        "declaredName": "StoreOwned",
        "elementId": "0f0e0d0c-0b0a-0908-0706-050403020100",
        "isImpliedIncluded": false,
        "ownedRelationship": [],
        "owningRelationship": null,
    }]);
    let json_path = dir.join("s.json");
    fs::write(&json_path, serde_json::to_string(&foreign).unwrap()).unwrap();
    let s2c_path = dir.join("s.s2c");
    let out = sysmlv2(&[
        "payload",
        json_path.to_str().unwrap(),
        "--encode",
        "-o",
        s2c_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let digest_of = |p: &Path| -> serde_json::Value {
        let out = sysmlv2(&["payload", p.to_str().unwrap()]);
        assert!(out.status.success(), "{}", stderr(&out));
        serde_json::from_str::<serde_json::Value>(&stdout(&out)).unwrap()["stateDigest"].clone()
    };
    assert_eq!(digest_of(&json_path), digest_of(&s2c_path));
    // The foreign id survives — nothing re-derived it.
    let out = sysmlv2(&["payload", s2c_path.to_str().unwrap(), "--ids"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let ids: serde_json::Value = serde_json::from_str(&stdout(&out)).unwrap();
    assert_eq!(ids["ids"][0], "0f0e0d0c-0b0a-0908-0706-050403020100");
    fs::remove_dir_all(&dir).ok();
}

// ---------------------------------------------------------------------------
// Refactor verb: extract / inline through the CLI —
// ambient reads, explicit paths for in-place writes, --dry-run diffs.
// ---------------------------------------------------------------------------

const REFACTOR_RIG: &str = "package Rig {
    part def A;
    part engine : A {
        attribute mass = 100;
    }
}
";

const REFACTOR_EXTRACTED: &str = "package Rig {
    part def A;
    part def Engine :> A {
        attribute mass = 100;
    }
    part engine : Engine;
}
";

#[test]
fn refactor_help_documents_both_directions() {
    let out = sysmlv2(&["refactor", "--help"]);
    assert!(out.status.success());
    let help = stdout(&out);
    for expected in ["extract", "inline", "byte-for-byte"] {
        assert!(help.contains(expected), "missing {expected:?}:\n{help}");
    }
    let out = sysmlv2(&["refactor", "extract", "--help"]);
    let help = stdout(&out);
    for expected in [
        "sysmlv2 refactor extract model.sysml Rig::engine",
        "--name",
        "--dry-run",
    ] {
        assert!(help.contains(expected), "missing {expected:?}:\n{help}");
    }
}

#[test]
fn refactor_extract_and_inline_round_trip_in_place() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-refactor-roundtrip-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("model.sysml");
    fs::write(&file, REFACTOR_RIG).unwrap();
    let path = file.to_str().unwrap();

    let out = sysmlv2(&["refactor", "extract", path, "Rig::engine"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("extracted 'Engine' from `Rig::engine`"),
        "{}",
        stderr(&out)
    );
    assert_eq!(fs::read_to_string(&file).unwrap(), REFACTOR_EXTRACTED);

    let out = sysmlv2(&["refactor", "inline", path, "Rig::Engine"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(
        fs::read_to_string(&file).unwrap(),
        REFACTOR_RIG,
        "inline(extract(usage)) must restore the file byte-for-byte"
    );
}

#[test]
fn refactor_dry_run_prints_the_diff_and_writes_nothing() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-refactor-dryrun-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("model.sysml");
    fs::write(&file, REFACTOR_RIG).unwrap();
    let path = file.to_str().unwrap();

    let out = sysmlv2(&[
        "refactor",
        "extract",
        path,
        "Rig::engine",
        "--name",
        "Motor",
        "--dry-run",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let diff = stdout(&out);
    assert!(diff.contains(&format!("--- {path}")), "{diff}");
    assert!(diff.contains("@@ -3,3 +3,4 @@"), "{diff}");
    assert!(diff.contains("-    part engine : A {"), "{diff}");
    assert!(diff.contains("+    part def Motor :> A {"), "{diff}");
    assert!(diff.contains("+    part engine : Motor;"), "{diff}");
    assert_eq!(
        fs::read_to_string(&file).unwrap(),
        REFACTOR_RIG,
        "--dry-run must not write"
    );
}

#[test]
fn refactor_ambient_inputs_apply_to_dry_run_only() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-refactor-ambient-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    fs::write(dir.join("model.sysml"), REFACTOR_RIG).unwrap();
    let env = [("SYSMLV2_MODEL_DIR", dir.to_str().unwrap())];

    // Bare in-place run refuses, naming both remedies.
    let out = sysmlv2_env(&["refactor", "extract", "Rig::engine"], &env);
    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(
        err.contains("--dry-run only") && err.contains("explicit paths"),
        "{err}"
    );
    // The dry run reads ambient inputs and prints the diff.
    let out = sysmlv2_env(
        &["refactor", "extract", "Rig::engine", "--dry-run", "-q"],
        &env,
    );
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stdout(&out).contains("+    part engine : Engine;"),
        "{}",
        stdout(&out)
    );
    assert_eq!(
        fs::read_to_string(dir.join("model.sysml")).unwrap(),
        REFACTOR_RIG
    );
}

#[test]
fn refactor_refusals_name_their_reason_and_touch_nothing() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-refactor-refuse-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("model.sysml");
    fs::write(&file, REFACTOR_RIG).unwrap();
    let path = file.to_str().unwrap();

    // Extract of a definition: the eligibility gate's named refusal.
    let out = sysmlv2(&["refactor", "extract", path, "Rig::A"]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("not an extractable usage"),
        "{}",
        stderr(&out)
    );
    // Unknown name.
    let out = sysmlv2(&["refactor", "inline", path, "Rig::Nope"]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("cannot resolve `Rig::Nope`"),
        "{}",
        stderr(&out)
    );
    // Name collision.
    let out = sysmlv2(&["refactor", "extract", path, "Rig::engine", "--name", "A"]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("name `A` is already declared"),
        "{}",
        stderr(&out)
    );
    // stdin is never rewritable.
    let out = sysmlv2(&["refactor", "extract", "-", "Rig::engine"]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("stdin"), "{}", stderr(&out));
    assert_eq!(fs::read_to_string(&file).unwrap(), REFACTOR_RIG);
}

#[test]
fn refactor_inline_reports_unused_imports_cross_file() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-refactor-imports-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let defs = dir.join("defs.sysml");
    let uses = dir.join("use.sysml");
    fs::write(
        &defs,
        "package Defs {\n    part def Kit;\n    part def Tool;\n}\n",
    )
    .unwrap();
    fs::write(
        &uses,
        "package Use {\n    private import Defs::*;\n    part tool : Tool;\n}\n",
    )
    .unwrap();

    let out = sysmlv2(&[
        "refactor",
        "inline",
        defs.to_str().unwrap(),
        uses.to_str().unwrap(),
        "Defs::Tool",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let err = stderr(&out);
    assert!(
        err.contains("note: import now unused") && err.contains("Defs::*"),
        "{err}"
    );
    assert_eq!(
        fs::read_to_string(&defs).unwrap(),
        "package Defs {\n    part def Kit;\n}\n"
    );
    assert_eq!(
        fs::read_to_string(&uses).unwrap(),
        "package Use {\n    private import Defs::*;\n    part tool;\n}\n"
    );
}

#[test]
fn refactor_cross_file_write_refusal_is_all_or_nothing() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-refactor-write-refusal-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let defs = dir.join("defs.sysml");
    let uses = dir.join("use.sysml");
    let defs_src = "package Defs {\n    part def Kit;\n    part def Tool;\n}\n";
    let uses_src = "package Use {\n    private import Defs::*;\n    part tool : Tool;\n}\n";
    fs::write(&defs, defs_src).unwrap();
    fs::write(&uses, uses_src).unwrap();

    let original_permissions = fs::metadata(&uses).unwrap().permissions();
    let mut readonly = original_permissions.clone();
    readonly.set_readonly(true);
    fs::set_permissions(&uses, readonly).unwrap();
    let out = sysmlv2(&[
        "refactor",
        "inline",
        defs.to_str().unwrap(),
        uses.to_str().unwrap(),
        "Defs::Tool",
    ]);
    fs::set_permissions(&uses, original_permissions).unwrap();

    assert!(!out.status.success());
    let err = stderr(&out);
    assert!(err.contains("refactor was not written"), "{err}");
    assert!(!err.contains(" — rewrote "), "{err}");
    assert_eq!(fs::read_to_string(&defs).unwrap(), defs_src);
    assert_eq!(fs::read_to_string(&uses).unwrap(), uses_src);
    fs::remove_dir_all(dir).ok();
}

/// AA7g: the generated-provenance rules run in CI through `lint` —
/// unit/name attribution exact, severities and exit codes per the
/// standing contract, config overrides normal, and `--fix` /
/// `--fix-deletes` neither edit generated content nor consume the
/// findings (they deliberately carry no fixes).
#[test]
fn lint_runs_generated_rules_with_sidecar_attribution() {
    use sysmlv2_lint::{Config, canonical_member_text, canonicalization_digest};
    use sysmlv2_model::structure::{member_structure_digest, sha256_hex};

    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-lint-generated-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();

    const MEMBER: &str =
        "#TransformMeta::Generated part def <'R-1'> beam {\n\tdoc /* emits the beam */\n}";
    let config = Config::default();
    let canonical = canonical_member_text(MEMBER, &config).expect("member formats");
    let spelling = format!("sha256:{}", sha256_hex(canonical.as_bytes()));
    let structure = member_structure_digest(MEMBER).expect("member parses");
    let policy = canonicalization_digest(&config);
    let script_digest = format!("sha256:{}", "b".repeat(64));
    let input_digest = format!("sha256:{}", "c".repeat(64));

    let indented = MEMBER
        .split('\n')
        .map(|l| {
            if l.is_empty() {
                String::new()
            } else {
                format!("\t{l}")
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    let content = format!("package Flashlight {{\n{indented}\n}}\n");
    let sidecar = |record_extra: &str, with_record: bool| {
        let record = if with_record {
            format!(
                "\tmetadata <'sync/R-1'> pR1 : TransformMeta::TransformProvenance about Flashlight::beam {{\n\
                 \t\ttransformId = \"sync\";\n\t\tkey = \"R-1\";\n\
                 \t\tspellingDigest = \"{spelling}\";\n\
                 \t\tstructureDigest = \"{structure}\";\n\
                 \t\tpolicyDigest = \"{policy}\";\n{record_extra}\t}}\n"
            )
        } else {
            String::new()
        };
        format!(
            "#TransformMeta::ProvenanceStore package <'provenance:Flashlight'> flashlightProvenance {{\n\
             \tmetadata <'sync/@state'> syncState : TransformMeta::TransformState {{\n\
             \t\ttransformId = \"sync\";\n\
             \t\ttransformerPath = \"scripts/reqs.transform.ts\";\n\
             \t\tscriptDigest = \"{script_digest}\";\n\
             \t\tmetadata source0 : TransformMeta::TransformSource {{\n\
             \t\t\tsourceAlias = \"source\";\n\
             \t\t\tsourceRef = \"reqs.csv\";\n\
             \t\t\tinputDigest = \"{input_digest}\";\n\t\t}}\n\t}}\n{record}}}\n"
        )
    };

    let m = dir.join("m.sysml");
    let side = dir.join("m.provenance.sysml");
    fs::write(&m, &content).unwrap();
    fs::write(&side, sidecar("", true)).unwrap();
    let paths = [m.to_str().unwrap(), side.to_str().unwrap()];

    // Clean fixture: silent, success.
    let out = sysmlv2(&["lint", paths[0], paths[1]]);
    assert!(out.status.success(), "{}", stderr(&out));
    // The rule id as it is printed, not the bare prefix: the scratch
    // directory's own name carries that prefix and appears in every
    // location line.
    assert!(!stderr(&out).contains("[generated-"), "{}", stderr(&out));

    // A tampered member surfaces generated-element-modified at its
    // content-unit location — warn by default (exit 0), a failure
    // under --strict, and silent when configured off.
    fs::write(
        &m,
        content.replace("emits the beam", "emits the tampered beam"),
    )
    .unwrap();
    let out = sysmlv2(&["lint", paths[0], paths[1]]);
    assert!(out.status.success(), "{}", stderr(&out));
    let err = stderr(&out);
    assert!(err.contains("[generated-element-modified]"), "{err}");
    assert!(
        err.contains("m.sysml:"),
        "content attribution missing: {err}"
    );
    let out = sysmlv2(&["lint", "--strict", paths[0], paths[1]]);
    assert!(!out.status.success(), "--strict escalates warnings");
    let out = sysmlv2(&[
        "lint",
        "--rule=generated-element-modified=off",
        paths[0],
        paths[1],
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        !stderr(&out).contains("generated-element-modified"),
        "{}",
        stderr(&out)
    );

    // --fix / --fix-deletes: generated findings carry no fixes — the
    // finding still reports and no file moves.
    let tampered = fs::read_to_string(&m).unwrap();
    let side_text = fs::read_to_string(&side).unwrap();
    let out = sysmlv2(&["lint", "--fix", "--fix-deletes", paths[0], paths[1]]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("[generated-element-modified]"),
        "{}",
        stderr(&out)
    );
    assert_eq!(
        fs::read_to_string(&m).unwrap(),
        tampered,
        "generated content untouched"
    );
    assert_eq!(
        fs::read_to_string(&side).unwrap(),
        side_text,
        "sidecar untouched"
    );

    // Ownership corruption (marker without a record) is an error —
    // nonzero exit, attributed with the exact rule id.
    fs::write(&m, &content).unwrap();
    fs::write(&side, sidecar("", false)).unwrap();
    let out = sysmlv2(&["lint", paths[0], paths[1]]);
    assert!(!out.status.success(), "corruption must fail the lint run");
    let err = stderr(&out);
    assert!(err.contains("[generated-provenance-invalid]"), "{err}");
    // Config can still disable the rule entirely.
    let out = sysmlv2(&[
        "lint",
        "--rule=generated-provenance-invalid=off",
        paths[0],
        paths[1],
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
}

const SPLIT_RIG: &str = "package Lib { part def Thing; }
package R {
    private import Lib::*;
    package A { part def X; part t : Thing; }
    package B { part def Y :> A::X; }
    part r : A::X;
}
";

#[test]
fn refactor_split_dry_run_prints_the_tree_and_writes_nothing() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-split-dryrun-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("model.sysml");
    fs::write(&file, SPLIT_RIG).unwrap();
    let path = file.to_str().unwrap();
    let out = sysmlv2(&["refactor", "split", path, "R", "--dry-run", "--slug"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let err = stderr(&out);
    assert!(err.contains("model/A.sysml: `R::A`"), "{err}");
    assert!(err.contains("model/B.sysml: `R::B`"), "{err}");
    let text = stdout(&out);
    assert!(text.contains("model/A.sysml (new)"), "{text}");
    assert!(text.contains("part t : Lib::Thing;"), "{text}");
    assert!(text.contains("+    public import A;"), "{text}");
    assert_eq!(fs::read_to_string(&file).unwrap(), SPLIT_RIG);
    assert!(!dir.join("model").exists());
}

#[test]
fn refactor_split_writes_new_files_and_refuses_to_overwrite() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-split-write-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&dir);
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("model.sysml");
    fs::write(&file, SPLIT_RIG).unwrap();
    let path = file.to_str().unwrap();
    let out_dir = dir.join("parts");
    let out = sysmlv2(&[
        "refactor",
        "split",
        path,
        "R",
        "--dir",
        out_dir.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("split `R` — rewrote"),
        "{}",
        stderr(&out)
    );
    let a = fs::read_to_string(out_dir.join("A.sysml")).unwrap();
    assert_eq!(a, "package A { part def X; part t : Lib::Thing; }\n");
    let root = fs::read_to_string(&file).unwrap();
    assert!(
        root.contains("    public import A;\n    public import B;\n"),
        "{root}"
    );
    assert!(!root.contains("package A"), "{root}");
    // The split model checks clean as three files.
    let out = sysmlv2(&[
        "check",
        path,
        out_dir.join("A.sysml").to_str().unwrap(),
        out_dir.join("B.sysml").to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    // Running again refuses: the files exist and nothing is rewritten.
    fs::write(&file, SPLIT_RIG).unwrap();
    let out = sysmlv2(&[
        "refactor",
        "split",
        path,
        "R",
        "--dir",
        out_dir.to_str().unwrap(),
    ]);
    assert!(!out.status.success());
    assert!(stderr(&out).contains("already exists"), "{}", stderr(&out));
    assert_eq!(fs::read_to_string(&file).unwrap(), SPLIT_RIG);
}

/// `members` lists an element by the specification's `name`: a feature
/// that declares no name is listed by its naming feature — the return
/// parameter `result`, the redefined feature's name — not as anonymous.
#[test]
fn members_list_unnamed_features_by_their_effective_name() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-members-names-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("m.sysml");
    fs::write(
        &file,
        "package M {
            part def Car { part engine; attribute mass; }
            calc def Area { in x; return : Real = x; }
            part car : Car { part :>> engine; attribute :>> mass = 5; part :>> nope; }
        }",
    )
    .unwrap();
    let out = sysmlv2(&["members", file.to_str().unwrap(), "M::Area"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    let lines: Vec<&str> = text.lines().collect();
    assert_eq!(lines.len(), 2, "{text}");
    assert!(lines[0].starts_with("x "), "{text}");
    assert!(lines[1].starts_with("result "), "{text}");
    // A redefining feature is listed by the redefined feature's name — as
    // written when the redefinition did not resolve.
    let out = sysmlv2(&["members", file.to_str().unwrap(), "M::car"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    for expected in ["engine ", "mass ", "nope "] {
        assert!(
            text.lines().any(|l| l.starts_with(expected)),
            "{expected}: {text}"
        );
    }
    assert!(!text.contains("anonymous"), "{text}");
    // `eval --all` labels a valued feature the same way.
    let out = sysmlv2(&["eval", "--all", file.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stdout(&out).contains("mass = 5"), "{}", stdout(&out));
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn lint_format_json_writes_one_report_to_stdout() {
    let dir =
        std::env::temp_dir().join(format!("sysmlv2-cli-test-lint-json-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    let src = "package P {\n    attribute def Real;\n    calc def T {\n        in force : Real;\n        in radius : Real;\n        return t : Real = force * 2;\n    }\n}\n";
    fs::write(&input, src).unwrap();

    let out = sysmlv2(&[
        "lint",
        "--format",
        "json",
        "--rule",
        "unused-parameter=warn",
        input.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    // The report is the whole of stdout; the text tallies stay off stderr.
    assert!(!stderr(&out).contains("warning(s)"), "{}", stderr(&out));
    let doc: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("stdout is JSON");
    assert_eq!(
        doc["summary"],
        serde_json::json!({"errors": 0, "warnings": 1, "infos": 0, "hints": 0, "suppressed": 0})
    );
    let f = &doc["findings"][0];
    assert_eq!(f["stage"], "lint");
    assert_eq!(f["rule"], "unused-parameter");
    assert_eq!(f["severity"], "warn");
    assert!(f["message"].as_str().unwrap().contains("`radius`"), "{f}");
    assert_eq!(f["unit"], 0);
    assert_eq!(f["unitName"], input.display().to_string());
    assert_eq!(f["line"], 5);
    assert!(f["col"].as_u64().is_some() && f["endLine"] == 5, "{f}");
    let start = usize::try_from(f["start"].as_u64().unwrap()).unwrap();
    let end = usize::try_from(f["end"].as_u64().unwrap()).unwrap();
    assert_eq!(&src[start..end], "radius", "{f}");
    assert_eq!(f["fix"]["deletes"], true);
    assert_eq!(
        f["fix"]["edits"][0]["unitName"],
        input.display().to_string()
    );
    assert_eq!(
        fs::read_to_string(&input).unwrap(),
        src,
        "no --fix, no write"
    );

    // A configuration finding has no location: nulls, not zeros.
    let out = sysmlv2(&[
        "lint",
        "--format",
        "json",
        "--rule",
        "no-such=warn",
        input.to_str().unwrap(),
    ]);
    let doc: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("stdout is JSON");
    let f = &doc["findings"][0];
    assert_eq!(f["rule"], "lint-config");
    assert!(
        f["unit"].is_null() && f["unitName"].is_null() && f["line"].is_null(),
        "{f}"
    );
}

#[test]
fn check_format_json_reports_stages_with_the_same_exit_codes() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-check-json-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let good = dir.join("good.sysml");
    let bad = dir.join("bad.sysml");
    fs::write(&good, "package P;").unwrap();
    fs::write(&bad, "package Q { part x : ; }").unwrap();

    let out = sysmlv2(&["check", "--format", "json", good.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));
    let doc: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("stdout is JSON");
    assert_eq!(doc["findings"], serde_json::json!([]));
    assert_eq!(doc["summary"]["errors"], 0);

    // Two inputs: the broken one is a parse-stage error located in the
    // right file; the clean one still goes through the model stage.
    let out = sysmlv2(&[
        "check",
        "--format",
        "json",
        good.to_str().unwrap(),
        bad.to_str().unwrap(),
    ]);
    assert!(!out.status.success());
    assert!(!stderr(&out).contains("error(s)"), "{}", stderr(&out));
    let doc: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("stdout is JSON");
    let f = &doc["findings"][0];
    assert_eq!(f["stage"], "parse");
    assert_eq!(f["severity"], "error");
    assert!(f["rule"].is_null(), "{f}");
    assert_eq!(f["unit"], 1);
    assert_eq!(f["unitName"], bad.display().to_string());
    assert_eq!(f["line"], 1);
    assert!(
        f["fix"].is_null() && f["alternatives"] == serde_json::json!([]),
        "{f}"
    );
    assert_eq!(
        doc["summary"]["errors"],
        doc["findings"].as_array().unwrap().len()
    );

    // Text mode is untouched: stderr diagnostics, empty stdout.
    let out = sysmlv2(&["check", bad.to_str().unwrap()]);
    assert!(stdout(&out).is_empty(), "{}", stdout(&out));
    assert!(stderr(&out).contains("error(s)"), "{}", stderr(&out));
}

#[test]
fn check_format_json_names_the_rule_a_semantic_finding_reports() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-check-json-rule-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let model = dir.join("model.sysml");
    fs::write(
        &model,
        "constraint c;\npart q : Missing;\npart p { satisfy c; }\n",
    )
    .unwrap();

    let out = sysmlv2(&["check", "--format", "json", model.to_str().unwrap()]);
    assert!(!out.status.success());
    let doc: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("stdout is JSON");
    let at_stage = |stage: &str| {
        doc["findings"]
            .as_array()
            .unwrap()
            .iter()
            .find(|f| f["stage"] == stage)
            .unwrap_or_else(|| panic!("no {stage} finding: {doc}"))
    };
    // The rule the semantic finding's message names is its `rule`; the
    // unresolved reference names none.
    let semantic = at_stage("semantic");
    assert_eq!(
        semantic["rule"], "validateSatisfyRequirementUsageReference",
        "{semantic}"
    );
    assert!(at_stage("referential")["rule"].is_null(), "{doc}");
    let _ = fs::remove_dir_all(&dir);
}

#[test]
fn lint_format_json_locates_findings_past_a_parse_failure() {
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-cli-test-lint-json-mixed-{}",
        std::process::id()
    ));
    fs::create_dir_all(&dir).unwrap();
    let bad = dir.join("bad.sysml");
    let good = dir.join("good.sysml");
    fs::write(&bad, "package Q { part x : ; }").unwrap();
    let src = "package P {\n    attribute def Real;\n    calc def T {\n        in force : Real;\n        in radius : Real;\n        return t : Real = force * 2;\n    }\n}\n";
    fs::write(&good, src).unwrap();

    // The broken first input never reaches the model, so the clean
    // second input is model unit 0 but input 1: every location in
    // the report must say input 1.
    let out = sysmlv2(&[
        "lint",
        "--format",
        "json",
        "--rule",
        "unused-parameter=warn",
        "--rule",
        "no-such=warn",
        bad.to_str().unwrap(),
        good.to_str().unwrap(),
    ]);
    assert!(!out.status.success(), "parse errors fail the run");
    let doc: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("stdout is JSON");
    let findings = doc["findings"].as_array().unwrap();
    let by_rule = |rule: &str| {
        findings
            .iter()
            .find(|f| f["rule"] == rule)
            .unwrap_or_else(|| panic!("no {rule} finding: {doc}"))
    };
    let parse = findings
        .iter()
        .find(|f| f["stage"] == "parse")
        .unwrap_or_else(|| panic!("{doc}"));
    assert_eq!(parse["unit"], 0);
    assert_eq!(parse["unitName"], bad.display().to_string());
    let config = by_rule("lint-config");
    assert!(
        config["unit"].is_null() && config["unitName"].is_null(),
        "{config}"
    );
    let unused = by_rule("unused-parameter");
    assert_eq!(unused["unit"], 1);
    assert_eq!(unused["unitName"], good.display().to_string());
    assert_eq!(unused["line"], 5);
    let edit = &unused["fix"]["edits"][0];
    assert_eq!(edit["unit"], 1);
    assert_eq!(edit["unitName"], good.display().to_string());
    let start = usize::try_from(edit["start"].as_u64().unwrap()).unwrap();
    let end = usize::try_from(edit["end"].as_u64().unwrap()).unwrap();
    assert!(src[start..end].contains("radius"), "{edit}");
    assert_eq!(doc["summary"]["errors"], 1);
    assert_eq!(doc["summary"]["warnings"], 2);
}

#[test]
fn piped_output_ends_quietly_when_the_reader_closes() {
    // A reader that closes the pipe early (`sysmlv2 … | head`) must end
    // the run without a panic banner: no message, exit status 0. The
    // model is large enough that the writer blocks on the pipe before it
    // can finish, so the closed read end is always observed — for one
    // JSON document streamed to stdout, one large text dump, and one
    // line-per-item listing.
    use std::fmt::Write as _;
    use std::io::Read as _;
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-pipe-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let model = dir.join("big.sysml");
    let mut text = String::from("package Big {\n");
    for i in 0..3000 {
        writeln!(text, "    part def P{i} {{ attribute a : Real = {i}; }}").unwrap();
    }
    text.push_str("}\n");
    fs::write(&model, &text).unwrap();
    let model = model.to_str().unwrap();
    for args in [
        vec!["convert", model, "--to", "compact-json"],
        vec!["parse", model, "--ast"],
        vec!["members", model, "Big"],
    ] {
        let mut child = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
            .env_remove("SYSMLV2_MODEL_DIR")
            .env_remove("SYSMLV2_LIB_DIR")
            .args(&args)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .expect("spawn");
        let mut head = [0u8; 64];
        let mut child_stdout = child.stdout.take().unwrap();
        child_stdout
            .read_exact(&mut head)
            .expect("some output arrives");
        drop(child_stdout);
        let out = child.wait_with_output().expect("wait");
        let err = String::from_utf8_lossy(&out.stderr);
        assert_eq!(out.status.code(), Some(0), "{args:?}: {err}");
        assert!(err.is_empty(), "{args:?}: {err}");
    }
    fs::remove_dir_all(&dir).ok();
}

#[test]
fn model_extensions_are_recognized_whatever_their_case() {
    // A file name's extension decides both whether an argument is a
    // model source at all and which dialect it parses in, and neither
    // question turns on the case it is spelled in: `K.KerML` is KerML,
    // and `M.SysML` is a file rather than a name to evaluate.
    let dir = std::env::temp_dir().join(format!("sysmlv2-ext-case-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let kerml = dir.join("K.KerML");
    fs::write(&kerml, "package K {\n    struct S;\n}\n").unwrap();
    let sysml = dir.join("M.SysML");
    fs::write(
        &sysml,
        "package P {\n    attribute x : ScalarValues::Integer = 3;\n}\n",
    )
    .unwrap();

    // `struct` is KerML-only, so this parses only in the KerML dialect.
    let out = sysmlv2(&["check", kerml.to_str().unwrap()]);
    assert!(out.status.success(), "{}", stderr(&out));

    let out = sysmlv2(&["eval", sysml.to_str().unwrap(), "P::x"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stdout(&out).contains("P::x = 3"), "{}", stdout(&out));

    // …and an archive built from such a file packs and reads back.
    let archive = dir.join("p.kpar");
    let out = sysmlv2(&[
        "convert",
        sysml.to_str().unwrap(),
        "--to",
        "kpar",
        "-o",
        archive.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let out = sysmlv2(&["convert", archive.to_str().unwrap(), "--to", "compact-json"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(stdout(&out).contains("\"@id\""), "{}", stdout(&out));
    fs::remove_dir_all(&dir).ok();
}

/// Every verb parses, and the parser's bound only turns unbounded input
/// into a diagnostic on a stack that reaches the bound. Input nested to
/// it is ordinary input with nothing to report — a kilobyte and a half
/// here — and on a stack too small for it the descent ends the process:
/// no diagnostic, no unwind, no exit status worth reading.
///
/// A process's own thread is the small stack: eight megabytes by
/// default, which an unoptimized build already overruns, and less
/// wherever the host caps it. The run is shrunk to two megabytes where
/// the shell can shrink it, so the reservation is what carries the
/// descent in either build.
#[test]
fn a_verb_parses_at_the_nesting_bound() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-deep-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let deep = dir.join("deep.sysml");
    // One level is the package, so the braces within it stop one short.
    let levels = sysmlv2_parser::parser::MAX_NESTING as usize - 1;
    fs::write(
        &deep,
        format!(
            "package P {{ {}part x;{} }}\n",
            "part x { ".repeat(levels),
            "}".repeat(levels)
        ),
    )
    .unwrap();

    let out = check_under_a_small_stack(deep.to_str().unwrap());
    assert!(
        out.status.success(),
        "nesting the parser accepts has nothing to report: {:?}, {}",
        out.status,
        stderr(&out)
    );
    assert!(stderr(&out).is_empty(), "{}", stderr(&out));
    fs::remove_dir_all(&dir).ok();
}

#[cfg(unix)]
fn check_under_a_small_stack(file: &str) -> Output {
    // `ulimit` caps the process's own thread and nothing else, so a
    // reserved thread is unaffected by it — which is the point.
    Command::new("/bin/sh")
        .arg("-c")
        .arg(r#"ulimit -s 2048 2>/dev/null; exec "$0" check "$1""#)
        .arg(env!("CARGO_BIN_EXE_sysmlv2"))
        .arg(file)
        .env_remove("SYSMLV2_MODEL_DIR")
        .env_remove("SYSMLV2_LIB_DIR")
        .output()
        .expect("failed to run sysmlv2")
}

#[cfg(not(unix))]
fn check_under_a_small_stack(file: &str) -> Output {
    sysmlv2(&["check", file])
}

/// A subprocess makes a stack-overflow regression an ordinary test
/// failure, including when nested if-nodes omit their action keyword.
#[test]
fn else_if_chains_respect_the_nesting_bound() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-else-if-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let source = dir.join("chain.sysml");
    for prefix in ["if true {} else ", "action if true {} else "] {
        for links in [32, 1000] {
            fs::write(
                &source,
                format!("action a {{ {}{{}} }}", prefix.repeat(links)),
            )
            .unwrap();
            let out = sysmlv2(&["parse", source.to_str().unwrap()]);
            assert!(
                out.status.code().is_some(),
                "parser aborted: {}",
                stderr(&out)
            );
            if links == 32 {
                assert!(out.status.success(), "{}", stderr(&out));
            } else {
                assert!(!out.status.success());
                assert!(
                    stderr(&out).contains("nesting is too deep"),
                    "{}",
                    stderr(&out)
                );
            }
        }
    }
    fs::remove_dir_all(dir).unwrap();
}

/// `--number-format` re-spells non-terminating rationals in `eval`,
/// `query` and `verify --ranges`; without it the output is the exact
/// fraction it always was, and a spec the toolkit cannot read is a
/// usage error naming the problem.
#[test]
fn number_format_respells_printed_values() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-numfmt-{}", std::process::id()));
    fs::remove_dir_all(&dir).ok();
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("m.sysml");
    fs::write(
        &file,
        "package M {\n    attribute third = 2 / 6;\n    attribute mixed = 7 / 3;\n    \
         attribute tenth = 0.1;\n    attribute x : ScalarValues::Real[1];\n    \
         assert constraint lo { x >= 0 }\n    assert constraint hi { 3 * x <= 1 }\n}\n",
    )
    .unwrap();
    let file = file.to_str().unwrap();
    let eval = |spec: Option<&str>| -> String {
        let mut args = vec!["eval", file, "M::third", "M::mixed", "M::tenth"];
        if let Some(spec) = spec {
            args.splice(1..1, ["--number-format", spec]);
        }
        let out = sysmlv2(&args);
        assert!(out.status.success(), "{spec:?}: {}", stderr(&out));
        stdout(&out)
    };
    assert_eq!(
        eval(None),
        "M::third = 1/3\nM::mixed = 7/3\nM::tenth = 0.1\n"
    );
    for (spec, third, mixed) in [
        ("exact,mixed=true", "1/3", "2 1/3"),
        ("approx,digits=3", "≈0.333", "≈2.33"),
        ("overline", "0.3\u{305}", "2.3\u{305}"),
        ("parens", "0.(3)", "2.(3)"),
        ("unicode", "¹/₃", "2¹/₃"),
        ("unicode,glyphs=true,slash=fraction", "⅓", "2⅓"),
    ] {
        assert_eq!(
            eval(Some(spec)),
            format!("M::third = {third}\nM::mixed = {mixed}\nM::tenth = 0.1\n"),
            "{spec}"
        );
    }
    // It may follow the positionals too.
    let out = sysmlv2(&["query", file, "(1/3, 2/7)", "--number-format", "parens"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(stdout(&out), "0.(3)\n0.(285714)\n");
    let out = sysmlv2(&["verify", "--ranges", "--number-format", "unicode", file]);
    assert!(
        stdout(&out).contains("x ∈ [0, ¹/₃]"),
        "{}{}",
        stdout(&out),
        stderr(&out)
    );
    let out = sysmlv2(&["verify", "--ranges", file]);
    assert!(stdout(&out).contains("x ∈ [0, 1/3]"), "{}", stdout(&out));

    let out = sysmlv2(&[
        "eval",
        "--number-format",
        "overline,width=3",
        file,
        "M::third",
    ]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("unknown setting `width`"),
        "{}",
        stderr(&out)
    );
    // A command that prints no values does not take it.
    let out = sysmlv2(&["parse", "--number-format", "parens", file]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    // Values past the double's range keep their digits.
    let big = dir.join("big.sysml");
    fs::write(
        &big,
        "package B {\n    attribute huge = 10 ** 400 / 3;\n}\n",
    )
    .unwrap();
    let out = sysmlv2(&[
        "eval",
        "--number-format",
        "approx,digits=3",
        big.to_str().unwrap(),
        "B::huge",
    ]);
    assert_eq!(stdout(&out), "B::huge = ≈3.33e399\n", "{}", stderr(&out));
    fs::remove_dir_all(&dir).ok();
}

/// `--value-units as-written` prints quantities in the units they were
/// written in: `eval` and `query` values (inside sequences too),
/// `verify --ranges` ranges and the values behind a violated verdict,
/// `verify --solve` witnesses, and `viz`'s `= value` lines. Without it, or
/// with `si`, the output is the evaluator's units as before; a value the
/// flag does not take is a usage error listing the possible ones.
#[test]
fn value_units_respell_printed_quantities() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-units-{}", std::process::id()));
    fs::remove_dir_all(&dir).ok();
    fs::create_dir_all(&dir).unwrap();
    let file = dir.join("b.sysml");
    fs::write(
        &file,
        "package B {\n    attribute m; attribute s;\n    \
         attribute 'in' { attribute unitConversion { attribute referenceUnit = m; \
         attribute conversionFactor = 0.0254; } }\n    \
         part def Board {\n        attribute w = 10 ['in'];\n        \
         attribute area = w * (4 ['in']);\n        attribute speed = w / (2 [s]);\n        \
         attribute footprint[1];\n        \
         assert constraint fits { footprint <= w * (3 ['in']) }\n        \
         assert constraint slow { speed <= 1 ['in'] / (1 [s]) }\n    }\n}\n",
    )
    .unwrap();
    let file = file.to_str().unwrap();
    let run = |args: &[&str], units: Option<&str>| -> String {
        let mut args = args.to_vec();
        if let Some(units) = units {
            args.extend(["--value-units", units]);
        }
        let out = sysmlv2(&args);
        assert!(
            out.status.code().is_some_and(|c| c <= 1),
            "{args:?}: {}",
            stderr(&out)
        );
        stdout(&out)
    };
    let eval = [
        "eval",
        file,
        "B::Board::speed",
        "B::Board::area",
        "B::Board::w",
    ];
    let si_eval =
        "B::Board::speed = 0.127 [m/s]\nB::Board::area = 0.0258064 [m**2]\nB::Board::w = 10 [in]\n";
    assert_eq!(run(&eval, None), si_eval);
    assert_eq!(run(&eval, Some("si")), si_eval);
    assert_eq!(
        run(&eval, Some("as-written")),
        "B::Board::speed = 5 [in/s]\nB::Board::area = 40 [in**2]\nB::Board::w = 10 [in]\n"
    );
    let query = ["query", file, "(B::Board::speed, B::Board::area, 3)"];
    assert_eq!(run(&query, None), "0.127 [m/s]\n0.0258064 [m**2]\n3\n");
    assert_eq!(run(&query, Some("as-written")), "5 [in/s]\n40 [in**2]\n3\n");

    let verify = ["verify", "--ranges", file];
    let si = run(&verify, None);
    assert_eq!(
        si,
        format!(
            "{file}:9:34  fits (AssertConstraintUsage): satisfied (propagation: holds for all values in the narrowed ranges)\n\
             {file}:10:34  slow (AssertConstraintUsage): VIOLATED (with speed = 0.127 [m/s])\n\
             1 satisfied, 1 violated, 0 undecided\n\n\
             narrowed ranges:\n  footprint ∈ [\u{2212}∞, 0.0193548] [m**2]\n"
        )
    );
    assert_eq!(run(&verify, Some("si")), si);
    let written = run(&verify, Some("as-written"));
    assert!(
        written.contains("VIOLATED (with speed = 5 [in/s])"),
        "{written}"
    );
    assert!(
        written.contains("footprint ∈ [\u{2212}∞, 30] [in**2]"),
        "{written}"
    );
    // The verdicts are the same either way.
    assert!(
        written.contains("1 satisfied, 1 violated, 0 undecided"),
        "{written}"
    );
    assert!(si.contains("1 satisfied, 1 violated, 0 undecided"), "{si}");

    let viz = ["viz", file];
    let si = run(&viz, None);
    assert!(
        si.contains("area = 0.0258064 [m**2]") && si.contains("speed = 0.127 [m/s]"),
        "{si}"
    );
    let written = run(&viz, Some("as-written"));
    assert!(
        written.contains("area = 40 [in**2]") && written.contains("speed = 5 [in/s]"),
        "{written}"
    );
    assert!(written.contains("w = 10 [in]"), "{written}");

    // A witness z3 finds for a constraint propagation cannot decide.
    if Command::new("z3")
        .arg("--version")
        .output()
        .is_ok_and(|o| o.status.success())
    {
        let open = dir.join("open.sysml");
        fs::write(
            &open,
            "package O {\n    attribute m;\n    \
             attribute 'in' { attribute unitConversion { attribute referenceUnit = m; \
             attribute conversionFactor = 0.0254; } }\n    \
             attribute x[1]; attribute y[1];\n    \
             assert constraint sum { x + y == 2 ['in'] * (3 ['in']) }\n}\n",
        )
        .unwrap();
        let solve = ["verify", "--solve", open.to_str().unwrap()];
        let si = run(&solve, None);
        assert!(
            si.contains("z3: satisfiable") && si.contains("[m**2]"),
            "{si}"
        );
        let written = run(&solve, Some("as-written"));
        assert!(written.contains("z3: satisfiable"), "{written}");
        assert!(
            written.contains("[in**2]") && !written.contains("[m**2]"),
            "{written}"
        );
    }

    // A violated verdict's sequence value, and the number format alongside.
    let seq = dir.join("seq.sysml");
    fs::write(
        &seq,
        "package S {\n    attribute m; attribute s;\n    \
         attribute 'in' { attribute unitConversion { attribute referenceUnit = m; \
         attribute conversionFactor = 0.0254; } }\n    attribute w = 10 ['in'];\n    \
         attribute pair = (w * (4 ['in']), w / (2 [s]));\n    \
         attribute third = 1 ['in'] / (3 [s]);\n    \
         assert constraint same { pair == (w * (3 ['in']), w / (2 [s])) }\n}\n",
    )
    .unwrap();
    let seq = seq.to_str().unwrap();
    let si = run(&["verify", seq], None);
    assert!(
        si.contains("VIOLATED (with pair = (0.0258064 [m**2], 0.127 [m/s]), w = 10 [in])"),
        "{si}"
    );
    let written = run(&["verify", seq], Some("as-written"));
    assert!(
        written.contains("VIOLATED (with pair = (40 [in**2], 5 [in/s]), w = 10 [in])"),
        "{written}"
    );
    let third = [
        "eval",
        seq,
        "S::third",
        "--number-format",
        "approx,digits=3",
    ];
    assert_eq!(run(&third, None), "S::third = ≈0.00847 [m/s]\n");
    assert_eq!(
        run(&third, Some("as-written")),
        "S::third = ≈0.333 [in/s]\n"
    );

    // The CLI spells it in kebab case; the wire spelling is a usage error.
    let out = sysmlv2(&[
        "eval",
        file,
        "B::Board::speed",
        "--value-units",
        "asWritten",
    ]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("[possible values: si, as-written]"),
        "{}",
        stderr(&out)
    );
    // A command that prints no values does not take it.
    let out = sysmlv2(&["parse", "--value-units", "as-written", file]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    fs::remove_dir_all(&dir).ok();
}

/// `sysmlv2 lsp --value-hint-units as-written` starts the server with
/// value and range hints in the units they were written in; a client's
/// `initializationOptions.valueHintUnits` still wins.
#[test]
fn lsp_value_hint_units_sets_the_server_default() {
    use std::io::{BufRead, BufReader, Read, Write};
    let text = "package U {\n    attribute m; attribute s;\n    \
                attribute 'in' { attribute unitConversion { attribute referenceUnit = m; \
                attribute conversionFactor = 0.0254; } }\n    \
                attribute d = 10 ['in'];\n    attribute v = d / (2 [s]);\n}\n";
    let hints = |flag: Option<&str>, init: serde_json::Value| -> Vec<String> {
        let mut cmd = Command::new(env!("CARGO_BIN_EXE_sysmlv2"));
        cmd.env_remove("SYSMLV2_MODEL_DIR")
            .env_remove("SYSMLV2_LIB_DIR")
            .arg("lsp");
        if let Some(flag) = flag {
            cmd.args(["--value-hint-units", flag]);
        }
        let mut child = cmd
            .stdin(std::process::Stdio::piped())
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::null())
            .spawn()
            .expect("lsp starts");
        let mut stdin = child.stdin.take().unwrap();
        let mut reader = BufReader::new(child.stdout.take().unwrap());
        let mut send = |msg: serde_json::Value| {
            let body = msg.to_string();
            write!(stdin, "Content-Length: {}\r\n\r\n{body}", body.len()).unwrap();
            stdin.flush().unwrap();
        };
        let mut recv_id = |id: i64| -> serde_json::Value {
            loop {
                let mut len = 0usize;
                loop {
                    let mut line = String::new();
                    reader.read_line(&mut line).unwrap();
                    let line = line.trim_end();
                    if line.is_empty() {
                        break;
                    }
                    if let Some(n) = line.strip_prefix("Content-Length: ") {
                        len = n.parse().unwrap();
                    }
                }
                let mut body = vec![0u8; len];
                reader.read_exact(&mut body).unwrap();
                let msg: serde_json::Value = serde_json::from_slice(&body).unwrap();
                if msg["id"] == id && msg.get("method").is_none() {
                    return msg;
                }
            }
        };
        send(
            serde_json::json!({"jsonrpc": "2.0", "id": 1, "method": "initialize",
            "params": {"capabilities": {}, "initializationOptions": init}}),
        );
        recv_id(1);
        send(serde_json::json!({"jsonrpc": "2.0", "method": "initialized", "params": {}}));
        send(
            serde_json::json!({"jsonrpc": "2.0", "method": "textDocument/didOpen",
            "params": {"textDocument": {"uri": "file:///w/u.sysml", "languageId": "sysml",
                "version": 1, "text": text}}}),
        );
        send(
            serde_json::json!({"jsonrpc": "2.0", "id": 2, "method": "textDocument/inlayHint",
            "params": {"textDocument": {"uri": "file:///w/u.sysml"},
                "range": {"start": {"line": 0, "character": 0}, "end": {"line": 6, "character": 0}}}}),
        );
        let reply = recv_id(2);
        send(serde_json::json!({"jsonrpc": "2.0", "id": 3, "method": "shutdown"}));
        recv_id(3);
        send(serde_json::json!({"jsonrpc": "2.0", "method": "exit"}));
        drop(stdin);
        child.wait().unwrap();
        reply["result"]
            .as_array()
            .unwrap()
            .iter()
            .map(|h| h["label"].as_str().unwrap().to_string())
            .collect()
    };
    let none = serde_json::Value::Null;
    assert!(hints(None, none.clone()).contains(&" = 0.127 [m/s]".to_string()));
    assert!(hints(Some("as-written"), none.clone()).contains(&" = 5 [in/s]".to_string()));
    assert!(hints(Some("si"), none).contains(&" = 0.127 [m/s]".to_string()));
    assert!(
        hints(
            Some("as-written"),
            serde_json::json!({"valueHintUnits": "si"})
        )
        .contains(&" = 0.127 [m/s]".to_string())
    );
    let out = sysmlv2(&["lsp", "--value-hint-units", "asWritten"]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    // `--value-units`, the other commands' spelling, names the same flag.
    let out = sysmlv2(&["lsp", "--value-units", "bogus"]);
    assert_eq!(out.status.code(), Some(2), "{}", stderr(&out));
    assert!(
        stderr(&out).contains("--value-hint-units"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn json_text_exports_use_and_validate_the_output_dialect() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-lift-dialect-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let source = dir.join("source.kerml");
    fs::write(&source, "package P { class A; feature f : A; }").unwrap();
    let input = dir.join("input.json");
    let result = sysmlv2(&[
        "convert",
        source.to_str().unwrap(),
        "--to",
        "compact-json",
        "-o",
        input.to_str().unwrap(),
    ]);
    assert!(result.status.success(), "{}", stderr(&result));
    for minimal in [false, true] {
        let outdir = dir.join(if minimal { "minimal" } else { "ordinary" });
        fs::create_dir_all(&outdir).unwrap();
        let mut args = vec![
            "convert",
            input.to_str().unwrap(),
            "--to",
            "text",
            "-o",
            outdir.to_str().unwrap(),
        ];
        if minimal {
            args.push("--min-qual");
        }
        let result = sysmlv2(&args);
        assert!(result.status.success(), "{}", stderr(&result));
        let path = outdir.join("document-1.kerml");
        assert!(path.exists());
        let checked = sysmlv2(&["check", path.to_str().unwrap()]);
        assert!(checked.status.success(), "{}", stderr(&checked));
    }
    for (metaclass, declaration) in [("Feature", "feature f;\n"), ("Type", "type f;\n")] {
        let slice = dir.join("slice.json");
        fs::write(&slice, r#"[{"@id":"00000000-0000-0000-0000-000000000001","@type":"Feature","declaredName":"f","owningRelationship":{"@id":"00000000-0000-0000-0000-000000000002"}}]"#.replace("Feature", metaclass)).unwrap();
        for minimal in [false, true] {
            for extension in ["KerML", "sysml"] {
                let target = dir.join(format!("slice-{metaclass}-{minimal}.{extension}"));
                let mut args = vec![
                    "convert",
                    slice.to_str().unwrap(),
                    "--to",
                    "text",
                    "-o",
                    target.to_str().unwrap(),
                ];
                if minimal {
                    args.push("--min-qual");
                }
                let result = sysmlv2(&args);
                if extension == "KerML" {
                    assert!(result.status.success(), "{}", stderr(&result));
                    assert_eq!(fs::read_to_string(&target).unwrap(), declaration);
                } else {
                    assert!(!result.status.success());
                    assert!(!target.exists(), "refusal must not write partial text");
                }
            }
        }
        let outdir = dir.join(format!("refused-{metaclass}"));
        fs::create_dir_all(&outdir).unwrap();
        let result = sysmlv2(&[
            "convert",
            slice.to_str().unwrap(),
            "--to",
            "text",
            "-o",
            outdir.to_str().unwrap(),
        ]);
        assert!(!result.status.success());
        assert_eq!(fs::read_dir(&outdir).unwrap().count(), 0);
    }
    fs::remove_dir_all(&dir).unwrap();
}

/// Foreign producers' payloads, which the corpus cannot stand in for:
/// with `SYSMLV2_FOREIGN_EXPORTS` naming a directory of interchange JSON
/// (pilot exports, Flexo retrievals), every file read with `--flexo` must
/// get past ownership repair, dialect detection and the SysML-only guard.
/// Failures of other kinds are reported but do not fail the test; the
/// payloads are not the toolkit's to ship, so the test skips without them.
#[test]
fn foreign_exports_get_past_ownership_and_dialect_handling() {
    let Some(root) = std::env::var_os("SYSMLV2_FOREIGN_EXPORTS") else {
        eprintln!("skipping: SYSMLV2_FOREIGN_EXPORTS not set");
        return;
    };
    let lib = sysmlv2_testkit::library_dir();
    fn json_files(dir: &Path, out: &mut Vec<std::path::PathBuf>) {
        for entry in fs::read_dir(dir).unwrap().flatten() {
            let path = entry.path();
            if path.is_dir() {
                json_files(&path, out);
            } else if path.extension().is_some_and(|e| e == "json") {
                out.push(path);
            }
        }
    }
    let mut files = Vec::new();
    json_files(Path::new(&root), &mut files);
    files.sort();
    assert!(
        !files.is_empty(),
        "no .json under {}",
        Path::new(&root).display()
    );
    let (mut converted, mut other) = (0, Vec::new());
    let mut regressions = Vec::new();
    for path in &files {
        let out = sysmlv2(&[
            "convert",
            path.to_str().unwrap(),
            "--flexo",
            "--to",
            "full-json",
            "--lib",
            lib.to_str().unwrap(),
            "-o",
            "/dev/null",
        ]);
        if out.status.success() {
            converted += 1;
            continue;
        }
        let error = stderr(&out);
        let first = error
            .lines()
            .find(|l| l.starts_with("error"))
            .unwrap_or("")
            .to_string();
        if [
            "omits the inverse ownership ends",
            "has no SysML declaration of its own",
            ".kerml does not parse",
        ]
        .iter()
        .any(|needle| error.contains(needle))
        {
            regressions.push(format!("{}: {first}", path.display()));
        } else {
            other.push(format!("{}: {first}", path.display()));
        }
    }
    eprintln!(
        "{converted} of {} converted; other failures:\n{}",
        files.len(),
        other.join("\n")
    );
    assert!(regressions.is_empty(), "{}", regressions.join("\n"));
}

#[test]
fn tree_prints_the_ownership_tree_as_text_and_json() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-cli-test-tree-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package Demo {\n    attribute def Mass;\n    part def Vehicle {\n        attribute mass : Mass;\n    }\n}\n",
    )
    .unwrap();
    let path = input.to_str().unwrap();

    // One element: its relationships, their elements, the ends as references.
    let out = sysmlv2(&["tree", path, "Demo::Vehicle"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert_eq!(
        stdout(&out),
        "Demo::Vehicle [PartDefinition]\n\
         └─ FeatureMembership\n\
         \x20  └─ mass [AttributeUsage]\n\
         \x20     ├─ FeatureTyping\n\
         \x20     │  └─ type → Demo::Mass [AttributeDefinition]\n\
         \x20     └─ OwningMembership\n\
         \x20        └─ (anonymous) [Multiplicity]\n"
    );

    // No name: every top-level element.
    let out = sysmlv2(&["tree", path]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(
        text.starts_with("Demo [Package]\n├─ OwningMembership\n│  └─ Mass [AttributeDefinition]\n"),
        "{text}"
    );
    // The attribute's last member is its default multiplicity.
    assert!(text.ends_with("└─ (anonymous) [Multiplicity]\n"), "{text}");

    // The depth limit marks what it leaves out.
    let out = sysmlv2(&["tree", path, "Demo::Vehicle", "--depth", "1"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(
        stdout(&out).ends_with("mass [AttributeUsage] …\n"),
        "{}",
        stdout(&out)
    );

    // JSON carries the same tree, ids on request.
    let out = sysmlv2(&["tree", path, "Demo::Vehicle", "--format", "json", "--ids"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let json: serde_json::Value = serde_json::from_str(&stdout(&out)).expect("valid JSON");
    let vehicle = &json[0];
    assert_eq!(vehicle["metaclass"], "PartDefinition");
    assert_eq!(vehicle["qualifiedName"], "Demo::Vehicle");
    assert!(vehicle["id"].is_string(), "{vehicle}");
    let typing = &vehicle["relationships"][0]["children"][0]["relationships"][0];
    assert_eq!(typing["metaclass"], "FeatureTyping");
    assert_eq!(typing["references"][0]["property"], "type");
    assert_eq!(
        typing["references"][0]["target"]["qualifiedName"],
        "Demo::Mass"
    );
    assert!(
        typing["references"][0]["target"]["id"].is_string(),
        "{typing}"
    );

    // References can be left out.
    let out = sysmlv2(&["tree", path, "Demo::Vehicle", "--no-references"]);
    assert!(out.status.success(), "{}", stderr(&out));
    assert!(!stdout(&out).contains('→'), "{}", stdout(&out));

    // An unknown name and a second name are errors.
    let out = sysmlv2(&["tree", path, "Demo::Nope"]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("cannot resolve `Demo::Nope`"),
        "{}",
        stderr(&out)
    );
    let out = sysmlv2(&["tree", path, "Demo::Vehicle", "Demo::Mass"]);
    assert!(!out.status.success());
    assert!(
        stderr(&out).contains("at most one qualified name"),
        "{}",
        stderr(&out)
    );
}

#[test]
fn tree_with_the_library_spells_library_targets_and_implied_relationships() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let dir =
        std::env::temp_dir().join(format!("sysmlv2-cli-test-tree-lib-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package Demo {\n    part def Vehicle {\n        attribute mass : ScalarValues::Real;\n    }\n}\n",
    )
    .unwrap();
    let path = input.to_str().unwrap();
    let lib = lib.to_str().unwrap();

    // A library target is spelled, with its metaclass, and never expanded.
    let out = sysmlv2(&["tree", path, "Demo::Vehicle", "--lib", lib]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(
        text.contains("└─ type → ScalarValues::Real [DataType] [library]\n"),
        "{text}"
    );
    assert!(!text.contains("(implied)"), "{text}");

    // The implied relationships are opt-in: the kind's library base.
    let out = sysmlv2(&["tree", path, "Demo::Vehicle", "--lib", lib, "--implied"]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(text.contains("Subclassification (implied)\n"), "{text}");
    assert!(
        text.contains("superclassifier → Parts::Part [PartDefinition] [library]\n"),
        "{text}"
    );

    // A library element as the root walks the library.
    let out = sysmlv2(&[
        "tree",
        path,
        "ScalarValues::Real",
        "--lib",
        lib,
        "--depth",
        "1",
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text = stdout(&out);
    assert!(
        text.starts_with("ScalarValues::Real [DataType] [library]\n"),
        "{text}"
    );
}
