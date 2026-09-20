//! Edits whose subject is a library element are refused with
//! `TransformError::NotDeclared` before any text is read: library units
//! are resolution targets only, never edited, and a host that hands the
//! engine any handle it holds (a rename with the cursor on a library
//! type, say) gets a refusal instead of a fault. Every operation kind
//! is driven through the public edit API, as a dry run and as a commit,
//! and the user text must survive both untouched.

use sysmlv2_transform::eligibility::{ExtractRefusal, InlineRefusal};
use sysmlv2_transform::{EditBuilder, ElementRef, Library, Session, TransformError};

const LIB: &str = "package Lib {
    part def LibDef {
        attribute mass = 1;
    }
    part libPart : LibDef;
}
";

const USER: &str = "package P {
    part def A :> Lib::LibDef;
    part p : Lib::LibDef;
}
";

fn session() -> Session {
    Session::from_sources_with_library(
        vec![("user.sysml".into(), USER.into())],
        Some(Library::sources(vec![("lib.sysml".into(), LIB.into())])),
    )
    .expect("parses")
}

fn elem(s: &mut Session, qn: &str) -> ElementRef {
    s.resolved()
        .resolve_qualified(qn)
        .unwrap_or_else(|| panic!("`{qn}` resolves"))
}

fn user_text(s: &Session) -> String {
    s.units().next().expect("one user unit").2.to_string()
}

/// Plans the batch twice — as a dry run and as a commit — and requires
/// the same refusal from both, with the user text untouched.
fn refused(s: &mut Session, plan: impl Fn(&mut EditBuilder<'_>)) -> TransformError {
    let before = user_text(s);
    let mut dry = s.edit();
    plan(&mut dry);
    let dry_err = dry.check().expect_err("the dry run refuses");
    let mut edit = s.edit();
    plan(&mut edit);
    let err = edit.commit().expect_err("the commit refuses");
    assert_eq!(dry_err.to_string(), err.to_string());
    assert_eq!(user_text(s), before, "the session is untouched");
    err
}

fn assert_not_declared(err: &TransformError, subject: ElementRef) {
    assert!(
        matches!(err, TransformError::NotDeclared(e) if *e == subject),
        "expected NotDeclared({subject:?}), got {err:?}"
    );
}

#[test]
fn rename_of_a_library_element_is_refused() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    assert!(s.resolved().is_library_element(def));
    let err = refused(&mut s, |e| {
        e.rename(def, "Renamed");
    });
    assert_not_declared(&err, def);
}

#[test]
fn set_feature_value_on_a_library_element_is_refused() {
    let mut s = session();
    let mass = elem(&mut s, "Lib::LibDef::mass");
    let err = refused(&mut s, |e| {
        e.set_feature_value(mass, "2");
    });
    assert_not_declared(&err, mass);
}

#[test]
fn set_feature_type_on_a_library_element_is_refused() {
    let mut s = session();
    let mass = elem(&mut s, "Lib::LibDef::mass");
    let err = refused(&mut s, |e| {
        e.set_feature_type(mass, "P::A");
    });
    assert_not_declared(&err, mass);
}

#[test]
fn insert_member_into_a_library_element_is_refused() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    let err = refused(&mut s, |e| {
        e.insert_member(def, "attribute added;");
    });
    assert_not_declared(&err, def);
}

#[test]
fn remove_of_a_library_element_is_refused() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    let err = refused(&mut s, |e| {
        e.remove(def);
    });
    assert_not_declared(&err, def);
}

#[test]
fn replace_member_of_a_library_element_is_refused() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    let err = refused(&mut s, |e| {
        e.replace_member(def, "part def LibDef;");
    });
    assert_not_declared(&err, def);
}

#[test]
fn retarget_of_a_site_owned_by_a_library_element_is_refused() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    let a = elem(&mut s, "P::A");
    // Sites are recorded in user units only, so a library site is one a
    // host re-homed: the user site's record placed on the library
    // element, in the library unit.
    let mut site = s
        .resolved()
        .references_to(def)
        .into_iter()
        .next()
        .expect("`Lib::LibDef` is referenced");
    site.owner = def;
    site.unit = 0;
    assert!(s.source(site.unit).is_none(), "unit 0 is the library unit");
    let err = refused(&mut s, |e| {
        e.retarget(site.clone(), a);
    });
    assert_not_declared(&err, def);
}

#[test]
fn retarget_of_a_site_in_a_library_unit_is_refused() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    let a = elem(&mut s, "P::A");
    // The owner is a user element, so only the site's unit says the
    // rewrite would land in library text — the refusal must still come
    // before the splice is planned.
    let mut site = s
        .resolved()
        .references_to(def)
        .into_iter()
        .next()
        .expect("`Lib::LibDef` is referenced");
    let owner = site.owner;
    assert!(!s.resolved().is_library_element(owner));
    site.unit = 0;
    assert!(s.source(site.unit).is_none(), "unit 0 is the library unit");
    let err = refused(&mut s, |e| {
        e.retarget(site.clone(), a);
    });
    assert_not_declared(&err, owner);
}

#[test]
fn move_of_a_library_element_is_refused() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    let p = elem(&mut s, "P");
    let err = refused(&mut s, |e| {
        e.move_member(def, p, None);
    });
    assert_not_declared(&err, def);
}

#[test]
fn move_into_a_library_element_is_refused() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    let a = elem(&mut s, "P::A");
    let err = refused(&mut s, |e| {
        e.move_member(a, def, None);
    });
    assert_not_declared(&err, def);
}

#[test]
fn hoist_of_a_library_element_is_refused() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    let err = refused(&mut s, |e| {
        e.add_unit("side.sysml");
        e.hoist_to_unit(def, "side.sysml", None);
    });
    assert_not_declared(&err, def);
}

#[test]
fn extract_of_a_library_usage_is_refused_by_eligibility() {
    let mut s = session();
    let usage = elem(&mut s, "Lib::libPart");
    let err = refused(&mut s, |e| {
        e.extract_definition(usage, None);
    });
    assert!(
        matches!(
            err,
            TransformError::ExtractIneligible {
                reason: ExtractRefusal::NotAUserElement
            }
        ),
        "{err:?}"
    );
}

#[test]
fn inline_of_a_library_definition_is_refused_by_eligibility() {
    let mut s = session();
    let def = elem(&mut s, "Lib::LibDef");
    let err = refused(&mut s, |e| {
        e.inline_definition(def);
    });
    assert!(
        matches!(
            err,
            TransformError::InlineIneligible {
                reason: InlineRefusal::NotAUserElement
            }
        ),
        "{err:?}"
    );
}

#[test]
fn user_edits_beside_the_library_still_commit() {
    let mut s = session();
    let a = elem(&mut s, "P::A");
    let mut edit = s.edit();
    edit.rename(a, "B");
    edit.commit().expect("a user element renames");
    assert_eq!(
        user_text(&s),
        "package P {
    part def B :> Lib::LibDef;
    part p : Lib::LibDef;
}
"
    );
}
