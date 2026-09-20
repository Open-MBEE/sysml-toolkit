//! The semantic-identity refusal names each broken site in
//! human-readable terms: the spelled reference text, unit:line:col, the
//! raw byte span, and the expected target's qualified name.

use sysmlv2_transform::{Session, SessionError, TransformError};

#[test]
fn refusal_names_broken_sites() {
    let src = "package Defs {
    part def Wheel;
}
package Other {
}
package Rig {
    private import Defs::Wheel;
    part def Vehicle {
        part front : Wheel;
    }
}
";
    let mut s = Session::from_sources(vec![("t.sysml".into(), src.into())]).expect("parses");
    let wheel = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let other = s.resolved().resolve_qualified("Other").unwrap();
    let mut edit = s.edit();
    edit.move_member(wheel, other, None);
    let err = edit.check().expect_err("move strands the import and use");
    assert!(
        matches!(err, TransformError::SemanticIdentity { .. }),
        "{err}"
    );
    let msg = err.to_string();
    // The spelled reference text, the unit name with line:col, the raw
    // byte span, and the moved target's new qualified name all appear.
    assert!(msg.contains("`Wheel`"), "{msg}");
    assert!(msg.contains("t.sysml:"), "{msg}");
    assert!(msg.contains("bytes "), "{msg}");
    assert!(msg.contains("Other::Wheel"), "{msg}");
    println!("{msg}");
}

#[test]
fn a_parse_failure_with_no_diagnostics_still_prints() {
    // The diagnostic lists are public fields, so a host can hand back an
    // error it built itself (a relay across a process boundary, say).
    // An empty list must read as a missing detail, not end in a fault.
    let session = SessionError::Parse {
        unit: "t.sysml".into(),
        diagnostics: Vec::new(),
    };
    let msg = session.to_string();
    assert!(msg.starts_with("t.sysml does not parse: "), "{msg}");
    assert!(msg.contains("no diagnostic"), "{msg}");

    let reparse = TransformError::ReparseFailed {
        unit: "t.sysml".into(),
        diagnostics: Vec::new(),
    };
    let msg = reparse.to_string();
    assert!(msg.starts_with("edited t.sysml does not parse: "), "{msg}");
    assert!(msg.contains("no diagnostic"), "{msg}");
}
