//! The semantic-identity refusal names each broken site in
//! human-readable terms: the spelled reference text, unit:line:col, the
//! raw byte span, and the expected target's qualified name.

use sysmlv2_transform::{Session, TransformError};

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
