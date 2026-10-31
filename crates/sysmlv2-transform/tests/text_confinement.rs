//! Text an edit writes stays where it is written: member text whose
//! braces close more than they open would end its owner's body early
//! and declare what follows outside it, a `{` it leaves open would take
//! the owner's closing brace, a replacement ending in a `//` note would
//! swallow the rest of the member's line, and a type spelling that is
//! more than one type name would reach past its `: T` clause.

use sysmlv2_transform::{EditBuilder, ElementRef, Session, TransformError};

const SRC: &str = "package P {
    part def A {
        attribute a = 1;
        part b : A; part c; part d;
    }
    port def Q;
    part def B {
        port p : Q;
    }
}
";

fn session() -> Session {
    Session::from_sources(vec![("t.sysml".into(), SRC.into())]).expect("parses")
}

fn text(s: &Session) -> String {
    s.units().next().unwrap().2.to_string()
}

/// Commit the batch `plan` builds against [`SRC`], handed the elements
/// `names` resolve to; the session afterwards and the outcome.
fn run(
    names: &[&str],
    plan: impl Fn(&[ElementRef], &mut EditBuilder<'_>),
) -> (Session, Result<(), TransformError>) {
    let mut s = session();
    let elements: Vec<ElementRef> = names
        .iter()
        .map(|n| s.resolved().resolve_qualified(n).unwrap())
        .collect();
    let mut edit = s.edit();
    plan(&elements, &mut edit);
    let outcome = edit.commit().map(|_| ());
    (s, outcome)
}

/// The refusal of the batch, checked to leave the text as it was.
fn refused(names: &[&str], plan: impl Fn(&[ElementRef], &mut EditBuilder<'_>)) -> TransformError {
    let (s, outcome) = run(names, plan);
    assert_eq!(text(&s), SRC);
    outcome.expect_err("refused")
}

/// The text after committing the batch.
fn committed(names: &[&str], plan: impl Fn(&[ElementRef], &mut EditBuilder<'_>)) -> String {
    let (s, outcome) = run(names, plan);
    outcome.expect("commit");
    text(&s)
}

fn invalid_member(err: TransformError) -> String {
    match err {
        TransformError::InvalidMember { message, .. } => message,
        other => panic!("expected an invalid-member refusal, got {other}"),
    }
}

#[test]
fn member_text_closing_its_owners_body_is_refused() {
    const CLOSES: &str = "a `}` closes a body the text did not open";
    let insert = refused(&["P::A"], |el, e| {
        e.insert_member(el[0], "} part def X {");
    });
    assert_eq!(invalid_member(insert), CLOSES);
    let at_slot = refused(&["P::A"], |el, e| {
        e.insert_member_at(el[0], "part x; } part def X { part y;", Some(0));
    });
    assert_eq!(invalid_member(at_slot), CLOSES);
    let top = refused(&[], |_, e| {
        e.insert_top_level("t.sysml", "} part def X {");
    });
    assert_eq!(invalid_member(top), CLOSES);
    // A replacement shaped so: refused, where it used to panic.
    for text in [
        "part b : A; } part def X {",
        "part b : A; } part def X { part y;",
    ] {
        let replace = refused(&["P::A::b"], |el, e| {
            e.replace_member(el[0], text);
        });
        assert_eq!(invalid_member(replace), CLOSES, "{text}");
    }
}

#[test]
fn member_text_leaving_a_brace_open_is_refused() {
    let err = refused(&["P::A"], |el, e| {
        e.insert_member(el[0], "part x {");
    });
    assert_eq!(invalid_member(err), "a `{` is left without its `}`");
}

#[test]
fn braces_in_names_strings_and_comments_do_not_count() {
    let out = committed(&["P::A"], |el, e| {
        e.insert_member(el[0], "part 'x}' { doc /* } { */ }");
    });
    assert!(
        out.contains("        part 'x}' { doc /* } { */ }\n    }\n    port def Q;"),
        "{out}"
    );
}

#[test]
fn a_replacement_ending_in_a_line_note_keeps_the_rest_of_its_line() {
    let out = committed(&["P::A::b"], |el, e| {
        e.replace_member(el[0], "part b2 : A; // note");
    });
    assert_eq!(
        out,
        SRC.replace(
            "        part b : A; part c; part d;\n",
            "        part b2 : A; // note\n        part c; part d;\n"
        )
    );
    let mut s = Session::from_sources(vec![("t.sysml".into(), out)]).unwrap();
    assert!(s.resolved().resolve_qualified("P::A::c").is_some());
    assert!(s.resolved().resolve_qualified("P::A::d").is_some());
    // Alone on its line, the member's line ends with the note.
    assert_eq!(
        committed(&["P::A::a"], |el, e| {
            e.replace_member(el[0], "attribute a = 2; // note");
        }),
        SRC.replace("attribute a = 1;\n", "attribute a = 2; // note\n")
    );
}

#[test]
fn a_type_spelling_is_one_type_name() {
    for ty in [
        "A; } part def X { part z : A",
        "A; part q",
        "A = 5",
        "A, B",
        "A [2]",
        "A // note",
    ] {
        match refused(&["P::A::b"], |el, e| {
            e.set_feature_type(el[0], ty);
        }) {
            TransformError::InvalidType { text, .. } => assert_eq!(text, ty),
            other => panic!("{ty}: {other}"),
        }
    }
    assert_eq!(
        committed(&["P::A::b"], |el, e| {
            e.set_feature_type(el[0], "P::A");
        }),
        SRC.replace("part b : A;", "part b : P::A;")
    );
    assert_eq!(
        committed(&["P::B::p"], |el, e| {
            e.set_feature_type(el[0], "~Q");
        }),
        SRC.replace("port p : Q;", "port p : ~Q;")
    );
}
