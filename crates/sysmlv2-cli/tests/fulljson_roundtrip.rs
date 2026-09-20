//! Full-form JSON → text sentinels: converting a model's *full* JSON back
//! to text must print exactly what the compact-JSON path prints. Minimal
//! repros for two lift defects — view `filter` clauses
//! dropped, and positional invocation arguments re-rendered as named —
//! plus the inverse guard that genuinely named arguments stay named.

use std::fs;
use std::path::Path;
use std::process::{Command, Output};

fn sysmlv2(args: &[&str]) -> Output {
    Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .args(args)
        .output()
        .expect("failed to run sysmlv2")
}

fn stderr(out: &Output) -> String {
    String::from_utf8_lossy(&out.stderr).into_owned()
}

const FILTER_MODEL: &str = "package FilterDemo {
    part def Widget;
    part w : Widget;

    view widgets {
        expose FilterDemo::*;
        filter @SysML::PartUsage;
    }
}";

const POSITIONAL_ARGS_MODEL: &str = "package ArgsDemo {
    calc def Power {
        in voltage : ScalarValues::Real;
        in current : ScalarValues::Real;
        return : ScalarValues::Real = voltage * current;
    }
    part battery {
        attribute p : ScalarValues::Real = Power(1.5, 2.1 / 30);
    }
}";

const NAMED_ARGS_MODEL: &str = "package ArgsDemo {
    calc def Power {
        in voltage : ScalarValues::Real;
        in current : ScalarValues::Real;
        return : ScalarValues::Real = voltage * current;
    }
    part battery {
        attribute p : ScalarValues::Real = Power(voltage = 1.5, current = 2.1 / 30);
    }
}";

/// `model` → (`--to form` JSON) → text, via the CLI with the corpus library.
fn text_via(dir: &Path, lib: &Path, name: &str, model: &str, form: &str) -> String {
    let input = dir.join(format!("{name}.sysml"));
    fs::write(&input, model).unwrap();
    let json_path = dir.join(format!("{name}.{form}.json"));
    let out = sysmlv2(&[
        "convert",
        input.to_str().unwrap(),
        "--to",
        form,
        "--lib",
        lib.to_str().unwrap(),
        "-o",
        json_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    let text_path = dir.join(format!("{name}.{form}.sysml"));
    let out = sysmlv2(&[
        "convert",
        json_path.to_str().unwrap(),
        "--to",
        "text",
        "--lib",
        lib.to_str().unwrap(),
        "-o",
        text_path.to_str().unwrap(),
    ]);
    assert!(out.status.success(), "{}", stderr(&out));
    fs::read_to_string(&text_path).unwrap()
}

#[test]
fn full_json_to_text_matches_compact_path() {
    let lib = sysmlv2_testkit::workspace_root().join("spec-refs/SysML-v2-Release/sysml.library");
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let dir = std::env::temp_dir().join(format!("sysmlv2-fulljson-rt-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();

    let cases = [
        ("filter", FILTER_MODEL),
        ("positional_args", POSITIONAL_ARGS_MODEL),
        ("named_args", NAMED_ARGS_MODEL),
    ];
    for (name, model) in cases {
        let from_compact = text_via(&dir, &lib, name, model, "compact-json");
        let from_full = text_via(&dir, &lib, name, model, "full-json");
        assert_eq!(
            from_full, from_compact,
            "{name}: full-json → text diverges from compact-json → text"
        );
    }

    // The interesting constructs actually survived — the identity above
    // must not be vacuous.
    let filter_text = text_via(&dir, &lib, "filter", FILTER_MODEL, "full-json");
    assert!(filter_text.contains("filter @"), "{filter_text}");
    let positional = text_via(
        &dir,
        &lib,
        "positional_args",
        POSITIONAL_ARGS_MODEL,
        "full-json",
    );
    assert!(positional.contains("Power(1.5, 2.1 / 30)"), "{positional}");
    let named = text_via(&dir, &lib, "named_args", NAMED_ARGS_MODEL, "full-json");
    assert!(named.contains("voltage = 1.5"), "{named}");

    fs::remove_dir_all(&dir).ok();
}
