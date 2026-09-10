//! Determinism gate (mirror of the parser's `determinism.rs`):
//! the byte output is a pure function of the input Value, and the wire
//! layout itself is pinned by an exact byte fixture so format drift is
//! a reviewed decision, never an accident.

use serde_json::Value;
use std::fs;
use std::path::PathBuf;
use sysmlv2_cbor::to_compact_cbor;

#[test]
fn encoding_is_a_pure_function() {
    let dir =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../sysmlv2-parser/tests/goldens/expected");
    let mut seen = 0usize;
    for entry in fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let v: Value = serde_json::from_str(&fs::read_to_string(&path).unwrap()).unwrap();
        assert_eq!(
            to_compact_cbor(&v).unwrap(),
            to_compact_cbor(&v).unwrap(),
            "{}: byte-identical across encodes",
            path.display()
        );
        seen += 1;
    }
    assert!(seen >= 150, "corpus present");
}

/// Two elements (a named Package owning an OwningMembership whose
/// member is external) exercising the whole layout: header, external
/// table, id table, presence bits (elementId mirror, boolean defaults,
/// empty lists, default visibility), map entries (string, local ref
/// list, external ref, local ref).
#[test]
fn wire_format_is_pinned() {
    let v: Value = serde_json::from_str(
        r#"[
 {"@type":"Package","@id":"00000000-0000-4000-8000-000000000001",
  "declaredName":"P","elementId":"00000000-0000-4000-8000-000000000001",
  "isImpliedIncluded":false,
  "ownedRelationship":[{"@id":"00000000-0000-4000-8000-000000000002"}],
  "owningRelationship":null},
 {"@type":"OwningMembership","@id":"00000000-0000-4000-8000-000000000002",
  "elementId":"00000000-0000-4000-8000-000000000002",
  "isImplied":false,"isImpliedIncluded":false,
  "memberElement":{"@id":"11111111-1111-4111-8111-111111111111"},
  "visibility":"public",
  "ownedRelatedElement":[],"ownedRelationship":[],
  "owningRelatedElement":{"@id":"00000000-0000-4000-8000-000000000001"}}
]"#,
    )
    .unwrap();
    let expected: &[u8] = &[
        0xD9, 0xD9, 0xF7, // tag(55799) — self-described CBOR
        0xDA, 0x24, 0x53, 0x32, 0x43, // tag(0x24533243) — "$S2C" (RFC 9277 file magic)
        0x85, // array(5) — owner-exception section under FLAG_IMPLIED_OWNERS
        0x1B, 0x00, 0x00, 0x00, 0x01, 0x00, 0x01, 0x01,
        0x20, // header word: layout 1 · tables 1 · scheme 1 · flags 0x20 (implied owners)
        0x81, // external table, 1 entry
        0x50, 0x11, 0x11, 0x11, 0x11, 0x11, 0x11, 0x41, 0x11, 0x81, 0x11, 0x11, 0x11, 0x11, 0x11,
        0x11, 0x11, // bstr(16) 11111111-1111-4111-8111-111111111111
        0x82, // id table, 2 entries
        0x50, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x01, // element 0 @id
        0x50, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x40, 0x00, 0x80, 0x00, 0x00, 0x00, 0x00, 0x00,
        0x00, 0x02, // element 1 @id
        0x82, // element list, 2 entries
        0x83, 0x18, 0x6D, // array(3), type 109 = Package
        0x18, 0x18, // presence: elementId mirror, isImpliedIncluded
        // (owningRelationship: null is DERIVED — no root claims the
        // Package — so owner elision spells nothing where flags 0 spelled a
        // presence bit)
        0xA2, // 2 non-default fields
        0x01, 0x61, 0x50, // declaredName: "P"
        0x05, 0x81, 0x01, // ownedRelationship: [element 1]
        0x83, 0x18, 0x6C, // array(3), type 108 = OwningMembership
        0x19, 0x86, 0x38, // presence incl. default visibility, empty lists
        0xA1, // 1 non-default field
        0x06, 0x02, // memberElement: external index 2
        // (owningRelatedElement: element 0 is DERIVED — the Package's
        // ownedRelationship lists this membership — so the former
        // map entry `0x0B 0x00` is gone)
        0xA1, // owner exceptions, 1 entry:
        0x01,
        0x01, // element 1 had NO owningRelationship key at all —
              // re-derivation must not add one (bit 1 = slot 0 absent)
    ];
    assert_eq!(to_compact_cbor(&v).unwrap(), expected);
}
