//! The unit-structure section: payloads carry each unit root's
//! element index and source path, so decoders can restore the model's
//! original file layout.

use serde_json::{Value, json};
use sysmlv2_cbor::{
    describe, from_cbor_with_units, from_compact_cbor, from_compact_cbor_units, to_compact_cbor,
    to_compact_cbor_with_units,
};

fn two_roots() -> Value {
    json!([
        { "@type": "Namespace", "@id": "0f000000-0000-5000-8000-000000000001",
          "elementId": "0f000000-0000-5000-8000-000000000001",
          "isImpliedIncluded": false, "ownedRelationship": [], "owningRelationship": null },
        { "@type": "Namespace", "@id": "0f000000-0000-5000-8000-000000000002",
          "elementId": "0f000000-0000-5000-8000-000000000002",
          "isImpliedIncluded": false, "ownedRelationship": [], "owningRelationship": null },
    ])
}

#[test]
fn units_round_trip() {
    let v = two_roots();
    let units = vec![
        (0usize, "sub/dir/a.sysml".to_owned()),
        (1, "b.kerml".to_owned()),
    ];
    let bytes = to_compact_cbor_with_units(&v, &units).expect("encodes");
    let (decoded, got) = from_compact_cbor_units(&bytes).expect("decodes");
    assert_eq!(decoded, v);
    assert_eq!(
        got,
        vec![
            (0u64, "sub/dir/a.sysml".to_owned()),
            (1, "b.kerml".to_owned())
        ]
    );
    // The plain decoders accept the payload too (structure ignored).
    assert_eq!(from_compact_cbor(&bytes).expect("decodes"), v);
    let (_, via_any) = from_cbor_with_units(&bytes, &|_| None).expect("decodes");
    assert_eq!(via_any.len(), 2);
}

#[test]
fn empty_units_encode_identically_to_none() {
    let v = two_roots();
    let plain = to_compact_cbor(&v).expect("encodes");
    let empty = to_compact_cbor_with_units(&v, &[]).expect("encodes");
    assert_eq!(plain, empty);
    let (_, units) = from_compact_cbor_units(&plain).expect("decodes");
    assert!(units.is_empty());
}

#[test]
fn describe_reports_units() {
    let v = two_roots();
    let units = vec![(0usize, "a.sysml".to_owned()), (1, "b.sysml".to_owned())];
    let bytes = to_compact_cbor_with_units(&v, &units).expect("encodes");
    let d = describe(&bytes).expect("describes");
    assert_eq!(
        d["units"],
        json!([{ "index": 0, "path": "a.sysml" }, { "index": 1, "path": "b.sysml" }])
    );
    // Payloads without the section have no `units` key at all.
    let d = describe(&to_compact_cbor(&v).expect("encodes")).expect("describes");
    assert!(d.get("units").is_none());
}

#[test]
fn bad_unit_tables_refuse() {
    let v = two_roots();
    assert!(to_compact_cbor_with_units(&v, &[(9, "x.sysml".into())]).is_err());
    assert!(to_compact_cbor_with_units(&v, &[(1, "a".into()), (0, "b".into())]).is_err());
    assert!(to_compact_cbor_with_units(&v, &[(0, String::new())]).is_err());
}
