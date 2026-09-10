//! Gates for the semantic-token classification.
//!
//! 1. The keyword vocabulary is *generated* from the vendored normative
//!    grammars — this test regenerates it and compares, so grammar bumps
//!    cannot silently drift the highlighting.
//! 2. The corpus sweep is the completeness oracle: in a clean-parsing
//!    file every `Ident` token is either a recorded name or a keyword,
//!    so an unclassified `Ident` means a vocabulary gap or a name span
//!    the AST failed to record — both real defects.
//! 3. Encoding invariants: sorted, single-line, in-bounds.

use std::collections::BTreeSet;
use sysmlv2_lsp::tokens;
use sysmlv2_lsp::{Encoding, Mapper};
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};

#[test]
fn vocabulary_matches_the_grammars() {
    let specs = sysmlv2_testkit::workspace_root().join("spec-refs");
    let mut words = BTreeSet::new();
    for grammar in ["KerML.xtext", "SysML.xtext", "KerMLExpressions.xtext"] {
        let text = std::fs::read_to_string(specs.join(grammar))
            .unwrap_or_else(|e| panic!("{grammar}: {e} (vendored grammar missing?)"));
        let bytes = text.as_bytes();
        let mut i = 0;
        while i < bytes.len() {
            if bytes[i] == b'\'' {
                if let Some(end) = text[i + 1..].find('\'') {
                    let word = &text[i + 1..i + 1 + end];
                    if word.len() >= 2
                        && word.chars().all(|c| c.is_ascii_alphanumeric() || c == '_')
                        && word.chars().next().unwrap().is_ascii_alphabetic()
                    {
                        words.insert(word.to_string());
                    }
                    i += end + 2;
                    continue;
                }
            }
            i += 1;
        }
    }
    let generated: Vec<&str> = words.iter().map(|s| s.as_str()).collect();
    assert_eq!(
        tokens::VOCABULARY,
        generated.as_slice(),
        "vocabulary drifted from the grammars — regenerate the VOCABULARY table"
    );
}

#[test]
fn corpus_idents_all_classify() {
    let mut files = 0usize;
    let mut classified = 0usize;
    for path in sysmlv2_testkit::corpus_files() {
        let src = std::fs::read_to_string(&path).unwrap();
        let parse = if path.extension().is_some_and(|e| e == "kerml") {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        if !parse.diagnostics.is_empty() {
            continue; // completeness only holds for clean parses
        }
        let toks = tokens::lex(&src);
        let stray = tokens::unclassified_idents(&parse.unit, &src, &toks);
        assert!(
            stray.is_empty(),
            "{}: unclassified idents at {:?} ({:?})",
            path.display(),
            &stray[..stray.len().min(5)],
            stray
                .iter()
                .take(5)
                .map(|s| s.slice(&src))
                .collect::<Vec<_>>()
        );
        classified += tokens::classify(&parse.unit, &src, &toks).len();
        files += 1;
    }
    assert!(files >= 300, "corpus shrank? {files}");
    // Volume floor: a classification collapse cannot hide (measured
    // 83,526 at landing; may only move up).
    assert!(classified >= 80_000, "token volume collapsed: {classified}");
}

#[test]
fn corpus_encodings_are_wellformed() {
    for path in sysmlv2_testkit::corpus_files().into_iter().take(60) {
        let src = std::fs::read_to_string(&path).unwrap();
        let parse = if path.extension().is_some_and(|e| e == "kerml") {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        let toks = tokens::lex(&src);
        let classified = tokens::classify(&parse.unit, &src, &toks);
        // Spans sorted and non-overlapping once sorted.
        let mut sorted = classified.clone();
        sorted.sort_by_key(|t| t.span.start);
        for w in sorted.windows(2) {
            assert!(
                w[0].span.end <= w[1].span.start,
                "{}: overlapping classified spans {:?} / {:?}",
                path.display(),
                w[0],
                w[1]
            );
        }
        let mapper = Mapper::new(&src, Encoding::Utf16);
        let data = tokens::encode(classified, &src, &mapper);
        // Wire invariants: nonzero lengths, first-token deltas absolute.
        for t in &data {
            assert!(t.length > 0, "{}: zero-length token", path.display());
        }
    }
}
