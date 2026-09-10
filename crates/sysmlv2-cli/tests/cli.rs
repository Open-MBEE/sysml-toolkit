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
        "members", "lsp",
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-convert");
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

#[test]
fn plain_full_json_preserves_unresolved_reference_spelling() {
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-full-recovery");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-fmt");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-ranges");
    fs::create_dir_all(&dir).unwrap();
    let input = dir.join("m.sysml");
    fs::write(
        &input,
        "package Demo {\n\
         \x20   attribute def Real;\n\
         \x20   attribute def Integer;\n\
         \x20   attribute wingSpan : Real;\n\
         \x20   attribute count : Integer;\n\
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
fn check_reports_rustc_style_diagnostics() {
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-check");
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
    assert!(err.contains("bad.sysml:1:"), "location missing: {err}");
}

#[test]
fn lint_flags_unused_parameters_and_deletes_only_behind_the_guard() {
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-lint");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-lint-rules");
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
fn convert_json_back_to_text() {
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-lift");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-lib");
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
fn lift_drops_is_variable_on_usage_metaclasses() {
    // Some producers mark plain attribute usages `isVariable: true`;
    // `var` is a KerML-only prefix, so the lifted SysML must not print it.
    let dir = std::env::temp_dir().join(format!("sysmlv2-isvar-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    let json = serde_json::json!([
        { "@type": "Namespace", "@id": "00000000-0000-0000-0000-00000000000a",
          "ownedRelationship": [ {"@id": "00000000-0000-0000-0000-00000000000b"} ] },
        { "@type": "OwningMembership", "@id": "00000000-0000-0000-0000-00000000000b",
          "ownedRelatedElement": [ {"@id": "00000000-0000-0000-0000-00000000000c"} ] },
        { "@type": "Package", "@id": "00000000-0000-0000-0000-00000000000c",
          "declaredName": "P",
          "ownedRelationship": [ {"@id": "00000000-0000-0000-0000-00000000000d"} ] },
        { "@type": "OwningMembership", "@id": "00000000-0000-0000-0000-00000000000d",
          "ownedRelatedElement": [ {"@id": "00000000-0000-0000-0000-00000000000e"} ] },
        { "@type": "AttributeUsage", "@id": "00000000-0000-0000-0000-00000000000e",
          "declaredName": "a", "isVariable": true }
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-unused-import");
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
            part car : Vehicle;
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
    fs::write(&uses, "package Uses { import Defs::*; part w : Wheel; }").unwrap();

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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-viz-view");
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

    let out = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .args(["viz", model.to_str().unwrap(), "--view", "usecase"])
        .output()
        .expect("run");
    assert!(!out.status.success());
    let err = String::from_utf8(out.stderr).unwrap();
    assert!(err.contains("unknown view"), "{err}");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-viz");
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

#[test]
fn convert_min_qual_respells_references() {
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-minqual");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-cbor");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-fullcbor");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-elide");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-delta");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-elided-delta");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-no-lib-semantics");
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
        from_json["elements"].as_u64().unwrap() as usize
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
        stderr(&out).contains("compact-json or compact-cbor"),
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-refactor-roundtrip");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-refactor-dryrun");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-refactor-ambient");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-refactor-refuse");
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
    let dir = std::env::temp_dir().join("sysmlv2-cli-test-refactor-imports");
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

    let dir = std::env::temp_dir().join("sysmlv2-cli-test-lint-generated");
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
    assert!(!stderr(&out).contains("generated-"), "{}", stderr(&out));

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
