//! Inserting a member at a slot among its owner's members: the new
//! member lands on the line after its predecessor (a comment ending
//! that line stays with the predecessor, one leading the next member
//! stays with that member), slot 0 goes before the first member, and a
//! unit's root namespace as the owner writes at the unit's top level.

use sysmlv2_transform::Session;

fn session(src: &str) -> Session {
    Session::from_sources(vec![("t.sysml".into(), src.into())]).expect("parses")
}

fn text(s: &Session) -> String {
    s.units().next().unwrap().2.to_string()
}

/// Commit one `insert_member_at` into the element named `owner` (or,
/// for `None`, the root namespace of the unit) and return the text.
fn insert_at(src: &str, owner: Option<&str>, member: &str, index: Option<usize>) -> String {
    let mut s = session(src);
    let owner = match owner {
        Some(qn) => s.resolved().resolve_qualified(qn).unwrap(),
        None => {
            let top = s.resolved().resolve_qualified("P").unwrap();
            s.resolved().owner(top).unwrap()
        }
    };
    let mut edit = s.edit();
    edit.insert_member_at(owner, member, index);
    edit.commit().expect("commit");
    text(&s)
}

const BODY: &str = "package P {
    part a; // about a
    // leads b
    part b;
    part c;
    // trailing note
}
";

#[test]
fn slot_lands_after_the_predecessor_line() {
    assert_eq!(
        insert_at(BODY, Some("P"), "part x;", Some(1)),
        "package P {
    part a; // about a
    part x;
    // leads b
    part b;
    part c;
    // trailing note
}
"
    );
}

#[test]
fn slot_zero_and_past_the_end() {
    assert_eq!(
        insert_at(BODY, Some("P"), "part x;", Some(0)),
        "package P {
    part x;
    part a; // about a
    // leads b
    part b;
    part c;
    // trailing note
}
"
    );
    // Past the end: after the last member, before the body's trailing note.
    let past = "package P {
    part a; // about a
    // leads b
    part b;
    part c;
    part x;
    // trailing note
}
";
    assert_eq!(insert_at(BODY, Some("P"), "part x;", Some(3)), past);
    assert_eq!(insert_at(BODY, Some("P"), "part x;", Some(99)), past);
    // No index: appended before the closing brace, as before.
    assert_eq!(
        insert_at(BODY, Some("P"), "part x;", None),
        "package P {
    part a; // about a
    // leads b
    part b;
    part c;
    // trailing note
    part x;
}
"
    );
}

#[test]
fn a_block_comment_closing_the_line_stays_with_the_predecessor() {
    let src = "package P {\n    part a; /* about a */\n    part b;\n}\n";
    assert_eq!(
        insert_at(src, Some("P"), "part x;", Some(1)),
        "package P {\n    part a; /* about a */\n    part x;\n    part b;\n}\n"
    );
}

#[test]
fn multi_line_members_are_reindented_at_the_slot() {
    let src = "package P {
    part def A {
        part a;
        part b;
    }
}
";
    assert_eq!(
        insert_at(src, Some("P::A"), "part x {\n    attribute m;\n}", Some(1)),
        "package P {
    part def A {
        part a;
        part x {
            attribute m;
        }
        part b;
    }
}
"
    );
}

#[test]
fn shared_lines_break_after_the_predecessor() {
    // The next member shares the line: the copy breaks it after `a`.
    let src = "package P {\n    part def A { part a; part b; }\n}\n";
    assert_eq!(
        insert_at(src, Some("P::A"), "part x;", Some(1)),
        "package P {\n    part def A { part a;\n        part x; part b; }\n}\n"
    );
    // Slot 0 when the first member shares the opening brace's line: the
    // line breaks after the brace.
    assert_eq!(
        insert_at(src, Some("P::A"), "part x;", Some(0)),
        "package P {\n    part def A {\n        part x; part a; part b; }\n}\n"
    );
    // The last member shares the line with the closing brace: appended
    // as an index-less insert would.
    let src = "package P {\n    part def A { part a; }\n}\n";
    assert_eq!(
        insert_at(src, Some("P::A"), "part x;", Some(1)),
        insert_at(src, Some("P::A"), "part x;", None)
    );
}

#[test]
fn an_index_into_an_empty_or_bodiless_owner_appends() {
    let src = "package P {\n    part def A;\n    part def B {\n    }\n}\n";
    assert_eq!(
        insert_at(src, Some("P::A"), "part x;", Some(0)),
        insert_at(src, Some("P::A"), "part x;", None)
    );
    assert_eq!(
        insert_at(src, Some("P::B"), "part x;", Some(2)),
        insert_at(src, Some("P::B"), "part x;", None)
    );
}

#[test]
fn the_root_namespace_inserts_at_the_top_level() {
    let src = "package P {\n    part def A;\n}\n\npackage Q;\n";
    assert_eq!(
        insert_at(src, None, "package R {\n    part def B;\n}", Some(1)),
        "package P {\n    part def A;\n}\npackage R {\n    part def B;\n}\n\npackage Q;\n"
    );
    assert_eq!(
        insert_at(src, None, "package R;", None),
        "package P {\n    part def A;\n}\n\npackage Q;\npackage R;\n"
    );
    // A unit whose text does not end its last line still gets one.
    assert_eq!(
        insert_at("package P;", None, "package R;", Some(1)),
        "package P;\npackage R;\n"
    );
}

#[test]
fn several_slots_in_one_batch() {
    let mut s = session("package P {\n    part a;\n    part b;\n}\n");
    let p = s.resolved().resolve_qualified("P").unwrap();
    let mut edit = s.edit();
    edit.insert_member_at(p, "part a2;", Some(1));
    edit.insert_member_at(p, "part b2;", Some(2));
    edit.insert_member_at(p, "part b3;", Some(2));
    edit.commit().expect("commit");
    assert_eq!(
        text(&s),
        "package P {\n    part a;\n    part a2;\n    part b;\n    part b2;\n    part b3;\n}\n"
    );
    for qn in ["P::a2", "P::b2", "P::b3"] {
        assert!(s.resolved().resolve_qualified(qn).is_some(), "{qn}");
    }
}

#[test]
fn a_slot_insert_is_verified_like_any_insert() {
    const SRC: &str = "package P {\n    part a;\n    part b;\n}\n";
    // Unparsable member text is refused at plan time.
    let mut s = session(SRC);
    let p = s.resolved().resolve_qualified("P").unwrap();
    let mut edit = s.edit();
    edit.insert_member_at(p, "part ;;;", Some(1));
    assert!(edit.commit().is_err());
    assert_eq!(text(&s), SRC);
    // A name the inserted text cannot resolve is reported, as for an append.
    let findings = |index| {
        let mut s = session(SRC);
        let p = s.resolved().resolve_qualified("P").unwrap();
        let mut edit = s.edit();
        edit.insert_member_at(p, "part x : Missing;", index);
        edit.commit().expect("commit").findings
    };
    let at_slot = findings(Some(1));
    assert!(
        at_slot.iter().any(|f| f.contains("unresolved")),
        "{at_slot:?}"
    );
    assert_eq!(at_slot, findings(None));
}
