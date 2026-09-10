//! Session ↔ compact-form CBOR wrappers round-trip through the
//! same lift path as interchange JSON.

use sysmlv2_transform::{Session, SessionError};

#[test]
fn session_cbor_is_the_compact_json_byte_form() {
    let src = "package P { part def V { attribute total; } part v : V; }";
    let s = Session::from_sources(vec![("t.sysml".into(), src.into())]).expect("parses");
    // The wrapper contract: the bytes decode to the identical compact
    // element array the session emits as JSON.
    let decoded = sysmlv2_cbor::from_compact_cbor(&s.to_compact_cbor()).expect("decodes");
    assert_eq!(decoded, s.to_compact_json());
}

#[test]
fn cbor_lift_restores_the_original_layout() {
    let src = "package P { part def V { attribute total; } part v : V; }";
    let s = Session::from_sources(vec![("t.sysml".into(), src.into())]).expect("parses");
    // The binary form carries the model's unit structure, so a reopened
    // session keeps the original unit names — and with them the
    // path-seeded ids: the round trip is identity, byte for byte.
    let via_cbor = Session::from_compact_cbor(&s.to_compact_cbor()).expect("lifts from CBOR");
    let names = |s: &Session| s.units().map(|(_, n, _)| n.to_owned()).collect::<Vec<_>>();
    assert_eq!(names(&via_cbor), vec!["t.sysml"]);
    assert_eq!(via_cbor.to_compact_json(), s.to_compact_json());
    assert_eq!(via_cbor.to_compact_cbor(), s.to_compact_cbor());
    // JSON carries no unit structure: that path still renames to
    // document-N and re-derives ids accordingly.
    let via_json = Session::from_interchange_json(&s.to_compact_json()).expect("lifts from JSON");
    assert_eq!(names(&via_json), vec!["document-1.sysml"]);
}

#[test]
fn invalid_payload_is_a_session_error() {
    let Err(err) = Session::from_compact_cbor(&[0xFF, 0x00]) else {
        panic!("garbage bytes must not open a session");
    };
    assert!(matches!(err, SessionError::Cbor(_)));
    assert!(err.to_string().contains("CBOR"), "{err}");
}
