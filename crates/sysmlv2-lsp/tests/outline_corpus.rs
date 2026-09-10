//! Corpus sweep for the document outline: every corpus file's
//! symbol tree must satisfy the containment invariants VS Code enforces
//! by silently dropping violators — selectionRange within range, children
//! within their parent, well-formed ranges, non-empty names. A violation
//! here would render as a mysteriously incomplete Outline view.

use lsp_types::DocumentSymbol;
use sysmlv2_lsp::{Encoding, Mapper, document_symbols};
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};

fn check(
    symbols: &[DocumentSymbol],
    parent: Option<&DocumentSymbol>,
    file: &str,
    count: &mut usize,
) {
    for s in symbols {
        *count += 1;
        let r = s.range;
        let sel = s.selection_range;
        assert!(
            r.start <= r.end && sel.start <= sel.end,
            "{file}: malformed range on {:?}: {r:?} / {sel:?}",
            s.name
        );
        assert!(
            r.start <= sel.start && sel.end <= r.end,
            "{file}: selection escapes range on {:?}: {r:?} / {sel:?}",
            s.name
        );
        assert!(!s.name.is_empty(), "{file}: empty symbol name at {r:?}");
        if let Some(p) = parent {
            assert!(
                p.range.start <= r.start && r.end <= p.range.end,
                "{file}: child {:?} escapes parent {:?}",
                s.name,
                p.name
            );
        }
        if let Some(children) = &s.children {
            check(children, Some(s), file, count);
        }
    }
}

#[test]
fn corpus_outlines_satisfy_containment() {
    let mut files = 0usize;
    let mut symbols = 0usize;
    for path in sysmlv2_testkit::corpus_files() {
        let src = std::fs::read_to_string(&path).unwrap();
        let parse = if path.extension().is_some_and(|e| e == "kerml") {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        let mapper = Mapper::new(&src, Encoding::Utf16);
        let tree = document_symbols(&parse.unit, &src, &mapper);
        check(&tree, None, &path.display().to_string(), &mut symbols);
        files += 1;
    }
    // Coverage floor: the corpus is large and richly structured — a
    // collapse in symbol count means the walk lost a member family
    // (measured 19,367 at landing; the floor may only move up).
    assert!(files >= 300, "corpus shrank? {files} files");
    assert!(
        symbols >= 19_000,
        "outline coverage collapsed: {symbols} symbols"
    );
}
