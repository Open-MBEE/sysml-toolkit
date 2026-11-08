//! Graph-format selection across the CLI's conversion routes.
use serde_json::Value;
use std::{fs, path::PathBuf, process::Command};
use sysmlv2_model::{migration::validate_conditional_graph_format, model::GraphFormat};
use sysmlv2_transform::Session;

const SOURCE: &str = "package P {
    class C { feature a; }
    feature ready; feature hot;
    feature ok = ready and not hot;
    feature instance = new C(1);
}";

fn run(args: &[&str]) -> Vec<u8> {
    let out = Command::new(env!("CARGO_BIN_EXE_sysmlv2"))
        .env_remove("SYSMLV2_MODEL_DIR")
        .env_remove("SYSMLV2_LIB_DIR")
        .env_remove("SYSMLV2_GRAPH_FORMAT")
        .args(args)
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "{args:?}: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    out.stdout
}

fn directory(test: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("sysmlv2-format-{test}-{}", std::process::id()));
    fs::create_dir_all(&dir).unwrap();
    dir
}

fn session(format: GraphFormat) -> Session {
    Session::from_sources_with_graph_format(
        vec![("model.kerml".into(), SOURCE.into())],
        None,
        format,
    )
    .unwrap()
}

fn check_snapshot(bytes: &[u8], format: GraphFormat) -> Value {
    assert_eq!(sysmlv2_cbor::graph_format(bytes).unwrap(), format);
    let value = session(format).decode_cbor(bytes).unwrap();
    validate_conditional_graph_format(&value, format).unwrap();
    value
}

#[test]
fn text_and_library_binary_conversions_keep_the_selected_format() {
    let dir = directory("binary");
    let input = dir.join("model.kerml");
    fs::write(&input, SOURCE).unwrap();
    let lib = dir.join("library");
    fs::create_dir_all(&lib).unwrap();
    fs::write(lib.join("types.kerml"), SOURCE).unwrap();
    for (name, format) in [
        ("legacy", GraphFormat::LegacyV2),
        ("canonical", GraphFormat::CanonicalV3),
    ] {
        for (target, extra) in [
            ("compact-cbor", &[][..]),
            ("compact-cbor", &["--elide-ids"][..]),
            ("full-cbor", &[][..]),
        ] {
            let mut args = vec![
                "convert",
                input.to_str().unwrap(),
                "--graph-format",
                name,
                "--to",
                target,
            ];
            args.extend(extra);
            check_snapshot(&run(&args), format);
        }
        for target in ["compact-cbor", "full-cbor"] {
            check_snapshot(
                &run(&[
                    "convert",
                    "--library",
                    "--lib",
                    lib.to_str().unwrap(),
                    "--graph-format",
                    name,
                    "--to",
                    target,
                ]),
                format,
            );
        }
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn json_and_binary_inputs_normalize_in_the_selected_format() {
    let dir = directory("normalize");
    let input = dir.join("model.kerml");
    fs::write(&input, SOURCE).unwrap();
    for (name, format) in [
        ("legacy", GraphFormat::LegacyV2),
        ("canonical", GraphFormat::CanonicalV3),
    ] {
        for (extension, target) in [
            ("json", "compact-json"),
            ("s2c", "compact-cbor"),
            ("full.json", "full-json"),
            ("full.s2c", "full-cbor"),
        ] {
            let path = dir.join(format!("input.{extension}"));
            fs::write(
                &path,
                run(&[
                    "convert",
                    input.to_str().unwrap(),
                    "--graph-format",
                    name,
                    "--to",
                    target,
                ]),
            )
            .unwrap();
            let convert = |target: &str, extra: &[&str]| {
                let mut args = vec![
                    "convert",
                    path.to_str().unwrap(),
                    "--graph-format",
                    name,
                    "--to",
                    target,
                ];
                args.extend(extra);
                run(&args)
            };
            let json: Value = serde_json::from_slice(&convert("compact-json", &[])).unwrap();
            validate_conditional_graph_format(&json, format).unwrap();
            assert!(
                json.as_array()
                    .unwrap()
                    .iter()
                    .any(|e| e["@type"] == "ConstructorExpression")
            );
            for extra in [&[][..], &["--elide-ids"][..]] {
                assert_eq!(
                    check_snapshot(&convert("compact-cbor", extra), format),
                    json
                );
            }
            check_snapshot(&convert("full-cbor", &[]), format);
            // Normalizing again must preserve both shape and identities.
            let normalized = dir.join("normalized.json");
            fs::write(&normalized, serde_json::to_vec(&json).unwrap()).unwrap();
            let again: Value = serde_json::from_slice(&run(&[
                "convert",
                normalized.to_str().unwrap(),
                "--graph-format",
                name,
                "--to",
                "compact-json",
            ]))
            .unwrap();
            assert_eq!(again, json);
        }
    }
    fs::remove_dir_all(dir).unwrap();
}

#[test]
fn conversion_deltas_keep_the_selected_format_and_apply_to_the_base() {
    let dir = directory("delta");
    let input = dir.join("model.kerml");
    for (name, format) in [
        ("legacy", GraphFormat::LegacyV2),
        ("canonical", GraphFormat::CanonicalV3),
    ] {
        fs::write(&input, SOURCE).unwrap();
        let base = run(&[
            "convert",
            input.to_str().unwrap(),
            "--graph-format",
            name,
            "--to",
            "compact-json",
        ]);
        let base_value: Value = serde_json::from_slice(&base).unwrap();
        let base_path = dir.join("base.json");
        fs::write(&base_path, base).unwrap();
        fs::write(&input, SOURCE.replace("new C(1)", "new C(2)")).unwrap();
        let json_path = dir.join("target.json");
        let cbor_path = dir.join("target.s2c");
        for (path, target) in [(&json_path, "compact-json"), (&cbor_path, "compact-cbor")] {
            fs::write(
                path,
                run(&[
                    "convert",
                    input.to_str().unwrap(),
                    "--graph-format",
                    name,
                    "--to",
                    target,
                ]),
            )
            .unwrap();
        }
        for path in [&input, &json_path, &cbor_path] {
            let target: Value = serde_json::from_slice(&run(&[
                "convert",
                path.to_str().unwrap(),
                "--graph-format",
                name,
                "--to",
                "compact-json",
            ]))
            .unwrap();
            let expected = sysmlv2_cbor::rebase_ids(&base_value, &target).unwrap();
            for extra in [&[][..], &["--elide-ids"][..], &["--delta-portable"][..]] {
                let mut args = vec![
                    "convert",
                    path.to_str().unwrap(),
                    "--graph-format",
                    name,
                    "--to",
                    "compact-cbor",
                    "--delta-base",
                    base_path.to_str().unwrap(),
                ];
                args.extend(extra);
                let bytes = run(&args);
                assert_eq!(sysmlv2_cbor::graph_format(&bytes).unwrap(), format);
                let (applied, _) = session(format)
                    .apply_delta_cbor_to(&bytes, &base_value, false)
                    .unwrap();
                validate_conditional_graph_format(&applied, format).unwrap();
                assert_eq!(
                    sysmlv2_cbor::delta_canonical(&applied).unwrap(),
                    sysmlv2_cbor::delta_canonical(&expected).unwrap()
                );
            }
        }
    }
    fs::remove_dir_all(dir).unwrap();
}
