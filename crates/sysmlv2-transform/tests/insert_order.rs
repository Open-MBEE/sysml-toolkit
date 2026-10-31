//! Where the grammar and the well-formedness rules put an inserted or
//! moved member, and what they refuse: a calculation, constraint or case
//! body ends with its result expression, so a member goes before it; a
//! subject must be its owner's first input, so it goes before the first
//! parameter and other inputs go after it; and an owner may own at most
//! one subject, objective, subaction of each kind, rendering and return
//! parameter, so a second one is refused.

use sysmlv2_transform::{Session, TransformError};

fn session(src: &str) -> Session {
    Session::from_sources(vec![("t.sysml".into(), src.into())]).expect("parses")
}

fn text(s: &Session) -> String {
    s.units().next().unwrap().2.to_string()
}

/// Commit one `insert_member_at` into `owner` and return the text.
fn insert(src: &str, owner: &str, member: &str, index: Option<usize>) -> String {
    let mut s = session(src);
    let owner = s.resolved().resolve_qualified(owner).unwrap();
    let mut edit = s.edit();
    edit.insert_member_at(owner, member, index);
    edit.commit().expect("commit");
    text(&s)
}

/// The refusal one `insert_member` into `owner` meets; the session's
/// text is checked to be untouched, and the dry run to agree.
fn refused(src: &str, owner: &str, member: &str) -> TransformError {
    let mut s = session(src);
    let owner = s.resolved().resolve_qualified(owner).unwrap();
    let mut edit = s.edit();
    edit.insert_member(owner, member);
    let dry = edit.check().expect_err("the dry run refuses").to_string();
    let mut edit = s.edit();
    edit.insert_member(owner, member);
    let err = edit.commit().expect_err("refused");
    assert_eq!(err.to_string(), dry);
    assert_eq!(text(&s), src);
    err
}

/// The context findings naming the subject-position rule.
fn subject_position_findings(src: &str) -> Vec<String> {
    session(src)
        .check_findings()
        .into_iter()
        .map(|f| f.message)
        .filter(|m| m.contains("SubjectParameterPosition"))
        .collect()
}

const PROBE: &str = "package BodyMembers {
	private import ScalarValues::*;
	part def Vehicle { attribute mass : Real; }
	requirement def R { in attribute limit : Real; }
	constraint def UnderLimit { in attribute m : Real; in attribute limit : Real; m <= limit }
	calc def Total { in attribute a : Real; in attribute b : Real; return attribute sum : Real; a + b }
}
";

#[test]
fn an_append_lands_before_a_calculation_result() {
    let out = insert(PROBE, "BodyMembers::Total", "in attribute c : Real;", None);
    assert_eq!(
        out,
        PROBE.replace(
            "return attribute sum : Real; a + b }",
            "return attribute sum : Real;\n\t\tin attribute c : Real; a + b }"
        )
    );
    // Past the end is the same slot.
    assert_eq!(
        insert(
            PROBE,
            "BodyMembers::Total",
            "in attribute c : Real;",
            Some(9)
        ),
        out
    );
    let mut s = session(&out);
    let c = s.resolved().resolve_qualified("BodyMembers::Total::c");
    assert!(c.is_some());
}

#[test]
fn an_append_lands_before_a_constraint_result() {
    assert_eq!(
        insert(
            PROBE,
            "BodyMembers::UnderLimit",
            "in attribute c : Real;",
            None
        ),
        PROBE.replace(
            "in attribute limit : Real; m <= limit }",
            "in attribute limit : Real;\n\t\tin attribute c : Real; m <= limit }"
        )
    );
}

#[test]
fn a_result_on_lines_of_its_own_keeps_its_leading_comment() {
    let src = "package P {
    calc def Total {
        in attribute a;
        return attribute sum;
        // the sum
        a + 1
    }
}
";
    let expected = "package P {
    calc def Total {
        in attribute a;
        return attribute sum;
        in attribute b;
        // the sum
        a + 1
    }
}
";
    assert_eq!(insert(src, "P::Total", "in attribute b;", None), expected);
    // Several in one batch keep their order, all before the result.
    let mut s = session(src);
    let total = s.resolved().resolve_qualified("P::Total").unwrap();
    let mut edit = s.edit();
    edit.insert_member(total, "in attribute b;");
    edit.insert_member(total, "in attribute c;");
    edit.commit().expect("commit");
    assert_eq!(
        text(&s),
        expected.replace(
            "in attribute b;\n",
            "in attribute b;\n        in attribute c;\n"
        )
    );
}

#[test]
fn a_body_holding_only_its_result_breaks_after_the_brace() {
    assert_eq!(
        insert(
            "package P {\n    calc def One { 1 }\n}\n",
            "P::One",
            "in attribute x;",
            None
        ),
        "package P {\n    calc def One {\n        in attribute x; 1 }\n}\n"
    );
}

#[test]
fn case_and_usage_bodies_end_with_their_result_too() {
    let src = "package P {
    analysis def A {
        subject v;
        objective o;
        v
    }
    calc c {
        in x;
        x
    }
}
";
    assert_eq!(
        insert(src, "P::A", "in attribute k;", None),
        src.replace("objective o;\n", "objective o;\n        in attribute k;\n")
    );
    assert_eq!(
        insert(src, "P::c", "in y;", None),
        src.replace("in x;\n", "in x;\n        in y;\n")
    );
}

#[test]
fn a_subject_lands_before_the_first_parameter() {
    let out = insert(PROBE, "BodyMembers::R", "subject v : Vehicle;", None);
    assert_eq!(
        out,
        PROBE.replace(
            "requirement def R { in attribute limit : Real; }",
            "requirement def R {\n\t\tsubject v : Vehicle; in attribute limit : Real; }"
        )
    );
    assert_eq!(subject_position_findings(&out), Vec::<String>::new());
    // The layout an append used to write breaks the rule.
    assert_eq!(
        subject_position_findings(&PROBE.replace(
            "requirement def R { in attribute limit : Real; }",
            "requirement def R { in attribute limit : Real; subject v : Vehicle; }"
        ))
        .len(),
        1
    );
    // An index past the first parameter is held to it.
    assert_eq!(
        insert(PROBE, "BodyMembers::R", "subject v : Vehicle;", Some(1)),
        out
    );
}

#[test]
fn a_subject_goes_before_actors_and_outputs_but_after_other_members() {
    let src = "package P {
    use case def U {
        doc /* a use case */
        objective o;
        actor a;
        out result;
    }
    requirement def Q {
        attribute note;
        out attribute level;
    }
}
";
    let out = insert(src, "P::U", "subject s;", None);
    assert_eq!(
        out,
        src.replace("objective o;\n", "objective o;\n        subject s;\n")
    );
    assert_eq!(subject_position_findings(&out), Vec::<String>::new());
    assert_eq!(
        insert(src, "P::Q", "subject s;", None),
        src.replace("attribute note;\n", "attribute note;\n        subject s;\n")
    );
}

#[test]
fn an_input_goes_no_earlier_than_past_the_subject() {
    let src = "package P {
    requirement def R {
        subject v;
        require constraint { true }
    }
}
";
    let out = insert(src, "P::R", "in attribute k;", Some(0));
    assert_eq!(
        out,
        src.replace("subject v;\n", "subject v;\n        in attribute k;\n")
    );
    assert_eq!(subject_position_findings(&out), Vec::<String>::new());
    // Other members take the slot asked for.
    assert_eq!(
        insert(src, "P::R", "attribute note;", Some(0)),
        src.replace(
            "        subject v;\n",
            "        attribute note;\n        subject v;\n"
        )
    );
}

#[test]
fn a_second_sole_member_is_refused() {
    let src = "package P {
    requirement def R {
        subject v;
    }
    case def C {
        subject v;
        objective o;
    }
    state def S {
        entry action e1;
    }
    view def V {
        render asTreeDiagram;
    }
    calc def F {
        return attribute r;
        1
    }
}
";
    let cases = [
        ("P::R", "subject w;", "subject"),
        ("P::C", "subject w;", "subject"),
        ("P::C", "objective o2;", "objective"),
        ("P::S", "entry action e2;", "`entry` action"),
        ("P::V", "render asElementTable;", "rendering"),
        ("P::F", "return attribute r2;", "return parameter"),
    ];
    for (owner, member, kind) in cases {
        match refused(src, owner, member) {
            TransformError::DuplicateMember {
                owner: o,
                member: m,
                count,
            } => {
                assert_eq!(
                    (o.as_str(), m.as_str(), count),
                    (owner, kind, 2),
                    "{member}"
                );
            }
            other => panic!("{member}: {other}"),
        }
    }
    assert_eq!(
        refused(src, "P::R", "subject w;").to_string(),
        "edit refused: `P::R` would own 2 subjects; it may own at most one"
    );
    // Two at once, into an owner without one.
    assert!(matches!(
        refused(src, "P::S", "do action d1; do action d2;"),
        TransformError::DuplicateMember { count: 2, .. }
    ));
    // The first of a kind, and another kind, are welcome.
    let out = insert(src, "P::S", "do action d;", None);
    assert!(
        out.contains("entry action e1;\n        do action d;\n"),
        "{out}"
    );
    let out = insert(src, "P::S", "exit action x;", None);
    assert!(out.contains("exit action x;"), "{out}");
}

#[test]
fn a_batch_may_swap_a_sole_member() {
    let src = "package P {\n    requirement def R {\n        subject v;\n        in x;\n    }\n}\n";
    let expected =
        "package P {\n    requirement def R {\n        subject w;\n        in x;\n    }\n}\n";
    // Remove first or insert first: judged on the committed model.
    for remove_first in [true, false] {
        let mut s = session(src);
        let r = s.resolved().resolve_qualified("P::R").unwrap();
        let v = s.resolved().resolve_qualified("P::R::v").unwrap();
        let mut edit = s.edit();
        if remove_first {
            edit.remove(v);
            edit.insert_member(r, "subject w;");
        } else {
            edit.insert_member(r, "subject w;");
            edit.remove(v);
        }
        edit.commit().expect("commit");
        assert_eq!(text(&s), expected);
    }
}

#[test]
fn an_owner_already_holding_two_is_refused_only_more() {
    let src = "package P {\n    state def S {\n        entry action a;\n        entry action b;\n    }\n}\n";
    assert!(insert(src, "P::S", "do action d;", None).contains("do action d;"));
    assert!(matches!(
        refused(src, "P::S", "entry action c;"),
        TransformError::DuplicateMember { count: 3, .. }
    ));
}

#[test]
fn a_move_obeys_the_same_order_and_limits() {
    let src = "package P {
    part def Vehicle;
    calc def Total {
        in attribute a;
        a
    }
    requirement def R {
        in attribute limit;
    }
    requirement def Q {
        subject v : Vehicle;
    }
    requirement def T {
        subject w : Vehicle;
    }
    attribute b;
}
";
    let moved = |what: &str, to: &str| {
        let mut s = session(src);
        let e = s.resolved().resolve_qualified(what).unwrap();
        let to = s.resolved().resolve_qualified(to).unwrap();
        let mut edit = s.edit();
        edit.move_member(e, to, None);
        edit.commit().map(|_| text(&s))
    };
    // Into a calculation: before its result.
    assert_eq!(
        moved("P::b", "P::Total").expect("commit"),
        src.replace("    attribute b;\n", "").replace(
            "in attribute a;\n",
            "in attribute a;\n        attribute b;\n"
        )
    );
    // A subject into a requirement without one: first.
    assert_eq!(
        moved("P::Q::v", "P::R").expect("commit"),
        src.replace("        subject v : Vehicle;\n", "").replace(
            "        in attribute limit;\n",
            "        subject v : Vehicle;\n        in attribute limit;\n"
        )
    );
    // A subject into a requirement that has one: refused.
    assert!(matches!(
        moved("P::Q::v", "P::T"),
        Err(TransformError::DuplicateMember { count: 2, .. })
    ));
}
