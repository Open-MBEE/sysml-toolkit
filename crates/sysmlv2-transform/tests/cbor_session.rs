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
    // JSON carries no unit structure: that path names the unit
    // document-N (the document's ids ride as explicit ids).
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
    // The codec's own message is reachable as the cause, so a host that
    // walks the error chain sees what the payload got wrong.
    let cause = std::error::Error::source(&err).expect("the codec error is the cause");
    assert!(cause.to_string().contains("payload"), "{cause}");
}

#[test]
fn a_codec_error_converts_into_a_session_error() {
    // The conversion is what lets the session's own payload paths use
    // `?` over the codec's result.
    let codec = sysmlv2_cbor::from_compact_cbor_units(&[0xFF, 0x00]).expect_err("garbage bytes");
    let message = codec.to_string();
    let err = SessionError::from(codec);
    assert!(matches!(err, SessionError::Cbor(_)));
    assert!(err.to_string().ends_with(&message), "{err}");
}

#[test]
fn a_read_failure_carries_its_cause() {
    let Err(err) = Session::open(&[std::path::PathBuf::from("no/such/directory/model.sysml")])
    else {
        panic!("a missing file must not open a session");
    };
    assert!(matches!(err, SessionError::Io(_)));
    assert!(std::error::Error::source(&err).is_some(), "{err}");
}

#[test]
fn blank_unit_names_are_refused_when_the_session_is_built() {
    // The binary payloads key every unit by its name, so a blank one
    // is refused up front instead of failing inside the emitter.
    for name in ["", " ", "\t\n"] {
        let Err(err) = Session::from_sources(vec![(name.into(), "package P;".into())]) else {
            panic!("a unit named {name:?} must not open a session");
        };
        assert!(
            matches!(err, SessionError::InvalidUnitName(ref n) if n == name),
            "{err:?}"
        );
        assert!(err.to_string().contains("blank"), "{err}");
    }
    let s = Session::from_sources(vec![("named.sysml".into(), "package P;".into())])
        .expect("a named unit opens");
    assert!(!s.to_compact_cbor().is_empty());
}

#[test]
fn blank_unit_names_are_refused_by_add_unit() {
    let mut s =
        Session::from_sources(vec![("t.sysml".into(), "package P;".into())]).expect("parses");
    for name in ["", "  "] {
        let mut edit = s.edit();
        edit.add_unit(name);
        let err = edit.commit().expect_err("a blank unit name is refused");
        assert!(
            matches!(err, sysmlv2_transform::TransformError::InvalidName(ref n) if n == name),
            "{err:?}"
        );
    }
    assert_eq!(s.units().count(), 1);
}
