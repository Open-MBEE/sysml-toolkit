//! Edits that take a member's whole line take it over either line
//! ending: text written with CRLF must not keep the blank line the
//! removed member stood on.

use sysmlv2_transform::Session;

fn session(src: &str) -> Session {
    Session::from_sources(vec![("t.sysml".into(), src.into())]).expect("parses")
}

fn text(s: &Session) -> String {
    s.units().next().expect("one unit").2.to_string()
}

#[test]
fn removing_a_member_from_crlf_text_leaves_no_blank_line() {
    let mut s = session("package P {\r\n    part def A;\r\n    part def B;\r\n}\r\n");
    let a = s
        .resolved()
        .resolve_qualified("P::A")
        .expect("`P::A` resolves");
    let mut edit = s.edit();
    edit.remove(a);
    edit.commit().expect("removes");
    assert_eq!(text(&s), "package P {\r\n    part def B;\r\n}\r\n");
}

#[test]
fn removing_a_member_from_lf_text_leaves_no_blank_line() {
    let mut s = session("package P {\n    part def A;\n    part def B;\n}\n");
    let a = s
        .resolved()
        .resolve_qualified("P::A")
        .expect("`P::A` resolves");
    let mut edit = s.edit();
    edit.remove(a);
    edit.commit().expect("removes");
    assert_eq!(text(&s), "package P {\n    part def B;\n}\n");
}

#[test]
fn moving_a_member_out_of_crlf_text_leaves_no_blank_line() {
    let mut s =
        session("package P {\r\n    part def A;\r\n}\r\npackage Q {\r\n    part def B;\r\n}\r\n");
    let a = s
        .resolved()
        .resolve_qualified("P::A")
        .expect("`P::A` resolves");
    let q = s.resolved().resolve_qualified("Q").expect("`Q` resolves");
    let mut edit = s.edit();
    edit.move_member(a, q, None);
    edit.commit().expect("moves");
    let out = text(&s);
    assert!(
        !out.contains("{\r\n\r\n") && !out.contains("{\n\n"),
        "the vacated line is gone: {out:?}"
    );
    assert!(out.contains("part def A;"), "{out:?}");
}

#[test]
fn a_member_sharing_its_line_keeps_the_line() {
    // Nothing widens here: the line belongs to the sibling too, so only
    // the member's own text goes — on either line ending.
    for src in [
        "package P {\r\n    part def A; part def B;\r\n}\r\n",
        "package P {\n    part def A; part def B;\n}\n",
    ] {
        let mut s = session(src);
        let b = s
            .resolved()
            .resolve_qualified("P::B")
            .expect("`P::B` resolves");
        let mut edit = s.edit();
        edit.remove(b);
        edit.commit().expect("removes");
        assert_eq!(text(&s), src.replace("part def B;", ""));
    }
}

#[test]
fn a_member_with_no_line_break_after_it_keeps_its_indentation() {
    // The last line has no break to take along, so only the member and
    // the blanks after it go.
    let mut s = session("package P {\n    part def A;\n}\npart def B;   ");
    let b = s.resolved().resolve_qualified("B").expect("`B` resolves");
    let mut edit = s.edit();
    edit.remove(b);
    edit.commit().expect("removes");
    assert_eq!(text(&s), "package P {\n    part def A;\n}\n");
}
