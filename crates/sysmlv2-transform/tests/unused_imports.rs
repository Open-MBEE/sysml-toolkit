//! Gates for the unused-private-import check.
//!
//! The check's contract is *provably feeds nothing*: three conditions
//! (resolver provenance, reference-site owner chains, textual member
//! mentions) must all say unused. The fixtures pin each condition; the
//! corpus gate ratchets the finding count and pins the two hazard
//! families that shaped the design — flow-payload typings (no reference
//! site is recorded for `message … of Payload`, so only the textual
//! condition protects them) and the spec's doc-carrier imports (genuinely
//! unused, and must stay reported).

use sysmlv2_transform::Session;

fn findings(sources: Vec<(&str, &str)>) -> Vec<(usize, sysmlv2_transform::Span)> {
    let mut s = Session::from_sources(
        sources
            .into_iter()
            .map(|(n, t)| (n.to_string(), t.to_string()))
            .collect(),
    )
    .unwrap();
    s.unused_private_imports()
}

#[test]
fn used_import_is_not_reported() {
    let f = findings(vec![(
        "a.sysml",
        "package T {\n    private import Defs::*;\n    package Defs { part def W; }\n    part w : W;\n}\n",
    )]);
    assert!(f.is_empty(), "{f:?}");
}

#[test]
fn unused_private_import_is_reported() {
    // Cross-file: the imported namespace lives elsewhere, so its member
    // names never appear in the importing unit — all three conditions
    // agree. (A same-file sibling import is conservatively kept alive by
    // the textual condition, since the sibling's own declarations
    // mention the member names.)
    let f = findings(vec![
        ("defs.sysml", "package Defs { part def W; }\n"),
        (
            "a.sysml",
            "package T {\n    private import Defs::*;\n    part def P;\n}\n",
        ),
    ]);
    assert_eq!(f.len(), 1, "{f:?}");
    // The span is the whole member — the removal range.
    let (_, span) = f[0];
    assert_eq!(span.start, 16);
    assert_eq!(span.end, 39);
}

#[test]
fn public_import_is_never_reported() {
    // Public imports re-export; unused-ness is not decidable locally.
    let f = findings(vec![(
        "a.sysml",
        "package T {\n    public import Defs::*;\n    package Defs { part def W; }\n    part def P;\n}\n",
    )]);
    assert!(f.is_empty(), "{f:?}");
}

#[test]
fn textual_mention_suppresses_the_finding() {
    // Historically the flow-payload shape recorded no reference site
    // (an `of Publish[1]` misparse, since fixed — `tests/refs.rs`
    // `payload_typings_record_sites`); the textual condition caught it
    // and stays as the backstop for the next unrecorded shape.
    let f = findings(vec![(
        "a.sysml",
        "package T {\n    private import Defs::*;\n    package Defs { item def Publish; }\n    occurrence def Seq {\n        part a; part b;\n        message m of Publish from a to b;\n    }\n}\n",
    )]);
    assert!(f.is_empty(), "{f:?}");
}

#[test]
fn corpus_ratchet() {
    let corpus = sysmlv2_testkit::workspace_root().join("spec-refs/SysML-v2-Release/sysml/src");
    if !corpus.exists() {
        eprintln!("corpus not initialized; skipping");
        return;
    }
    let paths = sysmlv2_testkit::user_files();
    let session = Session::open(&paths).unwrap();
    let mut session = session
        .with_library(&sysmlv2_testkit::library_dir())
        .unwrap();
    let findings = session.unused_private_imports();
    let named: Vec<(String, sysmlv2_transform::Span)> = findings
        .iter()
        .map(|(unit, span)| {
            let (_, name, _) = session.units().find(|(i, _, _)| i == unit).unwrap();
            (name.to_string(), *span)
        })
        .collect();
    // Ratchet: 33 at landing (each triaged — doc-carrier imports and
    // genuinely copy-pasted ones). May only move DOWN.
    assert!(
        named.len() <= 33,
        "unused-import findings grew ({}): {named:#?}",
        named.len()
    );
    // The flow-payload hazard family must never be flagged: these files
    // use their imports only through `message … of X` typings, which the
    // site table does not record.
    for hazard in ["17a-Sequence-Modeling", "17b-Sequence-Modeling"] {
        assert!(
            !named.iter().any(|(n, _)| n.contains(hazard)),
            "{hazard} flagged — the textual backstop regressed: {named:#?}"
        );
    }
    // A known-genuine finding must stay detected (the check can't just
    // go silent).
    assert!(
        named.iter().any(|(n, _)| n.contains("15_13")),
        "the doc-carrier family disappeared: {named:#?}"
    );
}
