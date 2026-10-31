//! A store holds the graph-normal spelling (`graph_normalize`: defaults
//! elided, backpointers spelled, ids sorted). For every corpus file, the
//! compact JSON graph-normalized must lift to exactly the text the compact
//! JSON itself lifts to: an elided default that read differently would
//! change a model on every round trip through a store (an elided
//! `isComposite: false` lifted `ref part` as `part`).

use std::fs;
use sysmlv2_parser::json::to_compact_json;
use sysmlv2_parser::lift::from_compact_json;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};
use sysmlv2_parser::print::print_source;

#[test]
fn corpus_graph_normalized_payloads_lift_as_their_source() {
    let files = sysmlv2_testkit::corpus_files();
    assert!(files.len() > 340, "expected the full corpus checkout");
    let mut failures = Vec::new();
    for path in files {
        let src = fs::read_to_string(&path).unwrap();
        let parsed = if path.extension().is_some_and(|e| e == "kerml") {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        let compact = to_compact_json(&parsed.unit);
        // The compact leg is roundtrip.rs's subject; here it is the
        // reference, and one that does not lift is a failure, not a skip.
        let reference = match from_compact_json(&compact) {
            Ok(reference) => reference,
            Err(e) => {
                failures.push(format!("{}: compact JSON refused: {e}", path.display()));
                continue;
            }
        };
        let reference = print_source(&reference.unit);
        let normalized = sysmlv2_cbor::graph_normalize(&compact).unwrap();
        match from_compact_json(&normalized) {
            Ok(lifted) if print_source(&lifted.unit) == reference => {}
            Ok(lifted) => {
                let text = print_source(&lifted.unit);
                let line = reference
                    .lines()
                    .zip(text.lines())
                    .find(|(a, b)| a != b)
                    .map(|(a, b)| format!("{a:?} became {b:?}"))
                    .unwrap_or_else(|| "line counts differ".into());
                failures.push(format!("{}: {line}", path.display()));
            }
            Err(e) => failures.push(format!("{}: refused: {e}", path.display())),
        }
    }
    assert!(
        failures.is_empty(),
        "{} corpus files lift differently once graph-normalized:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
