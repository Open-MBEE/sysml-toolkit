//! Negative corpus: malformed inputs with asserted diagnostic
//! quality, one fixture per parsing-hazard family under
//! `tests/negative/`.
//!
//! Expectations are embedded rustc-UI-style: a `//~ ERROR <substring>`
//! comment asserts that an error whose span *starts on that line*
//! carries the substring in its message (`//~^` moves the expectation
//! one line up per caret). The match is exact in both directions —
//! every marker must be satisfied by a distinct diagnostic, and every
//! diagnostic must be claimed by a marker — so the corpus also proves
//! the parser *recovers* between errors instead of cascading, and that
//! valid members surrounding an error stay diagnostic-free.
//!
//! Diagnostics come from the same stages as `sysmlv2 check` without
//! `--lib`: parse diagnostics plus body-context validation.

use std::fs;
use std::path::PathBuf;
use sysmlv2_parser::diag::Severity;
use sysmlv2_parser::parser::{Parse, parse_kerml_source, parse_source};
use sysmlv2_parser::span::LineIndex;

struct Expectation {
    line: u32,
    substring: String,
    matched: bool,
}

/// Parse the `//~ ERROR` markers out of a fixture. `^` moves the
/// expected line up, `v` moves it down (for stacking several
/// expectations that all land on the end-of-input line).
fn expectations(src: &str) -> Vec<Expectation> {
    let mut out = Vec::new();
    for (i, text) in src.lines().enumerate() {
        let Some(pos) = text.find("//~") else {
            continue;
        };
        let rest = &text[pos + 3..];
        let carets = rest.chars().take_while(|&c| c == '^').count();
        let vees = rest.chars().take_while(|&c| c == 'v').count();
        let rest = rest[carets + vees..].trim_start();
        let Some(msg) = rest.strip_prefix("ERROR") else {
            panic!("malformed marker (only `//~[^^…|vv…] ERROR <substring>`): {text}");
        };
        out.push(Expectation {
            line: (i + 1 - carets + vees) as u32,
            substring: msg.trim().to_owned(),
            matched: false,
        });
    }
    out
}

#[test]
fn negative_corpus_diagnostics() {
    let dir = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/negative");
    let mut fixtures: Vec<PathBuf> = fs::read_dir(&dir)
        .expect("tests/negative exists")
        .flatten()
        .map(|e| e.path())
        .filter(|p| {
            matches!(
                p.extension().and_then(|e| e.to_str()),
                Some("sysml" | "kerml")
            )
        })
        .collect();
    fixtures.sort();
    assert!(fixtures.len() >= 8, "negative fixtures present");

    let mut report = String::new();
    for path in &fixtures {
        let name = path.file_name().unwrap().to_string_lossy().into_owned();
        let src = fs::read_to_string(path).unwrap();
        let kerml = path.extension().is_some_and(|e| e == "kerml");
        let Parse { unit, diagnostics } = if kerml {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        let mut diags = diagnostics;
        diags.extend(sysmlv2_parser::check::validate(&unit));

        let index = LineIndex::new(&src);
        let mut expected = expectations(&src);
        assert!(
            !expected.is_empty(),
            "{name}: a negative fixture must expect at least one error"
        );

        for d in &diags {
            if d.severity != Severity::Error {
                continue;
            }
            assert!(
                (d.span.end as usize) <= src.len(),
                "{name}: diagnostic span {:?} exceeds the source",
                d.span
            );
            let line = index.line_col(d.span.start).line;
            let claimed = expected
                .iter_mut()
                .find(|e| !e.matched && e.line == line && d.message.contains(&e.substring));
            match claimed {
                Some(e) => e.matched = true,
                None => report.push_str(&format!(
                    "  {name}:{line}: unexpected error: {}\n",
                    d.message
                )),
            }
        }
        for e in &expected {
            if !e.matched {
                report.push_str(&format!(
                    "  {name}:{}: expected error not produced: {}\n",
                    e.line, e.substring
                ));
            }
        }
    }
    assert!(report.is_empty(), "negative-corpus mismatches:\n{report}");
}
