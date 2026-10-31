//! The three ways an unnamed member is findable by an implied name, in one
//! model: a role membership's library name (`subj`, `obj`, `result`), the
//! end names of a connector's type by position (`left`, `right`), and the
//! library binary ends by position (`source`, `earlierOccurrence`,
//! `sameThing`). Each mechanism is gated on its own elsewhere; this seam
//! pins that they compose in one resolution and that the qualified names
//! they give resolve back to the members. The JSON lift of the same model
//! is `roundtrip::implied_names_lift_as_the_emitter_finds_them`.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ResolvedModel, model_resolution_report},
    model::Model,
};

/// The seam model: a requirement and a verification case with unnamed
/// subjects and an objective, a calculation with an unnamed return, a
/// connection typed by a user connection definition with named ends whose
/// own ends are unnamed, and a succession and a binding with bare ends.
pub const SEAM: &str = "package P {
    part def V { attribute mass; }
    part def W { attribute w; }
    connection def Link { end left : V; end right : W; }
    requirement def R { subject : V; require constraint { subj.mass > 0 } }
    verification def VD { subject : V; objective { verify requirement r; } }
    calc def C { in x; return : V; }
    part s {
        part v : V;
        part w : W;
        connection ln : Link connect v to w;
        action x;
        action y;
        succession sc first x then y;
        binding bd bind v.mass = w.w;
        ref r1 :> ln.left.mass;
        ref r2 :> ln.right.w;
        ref r3 :> ln.source;
        ref r4 :> sc.earlierOccurrence;
        ref r5 :> bd.sameThing;
    }
    part q {
        ref y = VD::obj::r;
        ref z = C::result;
        ref sj = R::subj;
    }
}";

/// Every qualified name an implied name gives, with the member it names
/// read as the owner's member of that metaclass at that position.
const NAMES: &[&str] = &[
    "P::R::subj",
    "P::VD::subj",
    "P::VD::obj",
    "P::VD::obj::r",
    "P::C::result",
    "P::s::ln::left",
    "P::s::ln::right",
    "P::s::sc::earlierOccurrence",
    "P::s::sc::laterOccurrence",
    "P::s::bd::thisThing",
    "P::s::bd::sameThing",
];

fn checked(source: &str) -> ResolvedModel {
    let mut model = Model::new();
    model.add_source("seams.sysml", source);
    assert!(!model.has_errors(), "{:?}", model.units()[0].diagnostics);
    let report = model_resolution_report(&model);
    assert!(report.unresolved.is_empty(), "{:?}", report.unresolved);
    assert!(report.ambiguous.is_empty(), "{:?}", report.ambiguous);
    ResolvedModel::build(&model)
}

#[test]
fn implied_role_end_and_typed_end_names_resolve_in_one_model() {
    let mut r = checked(SEAM);
    for name in NAMES {
        let e = r.resolve_semantic_qualified(name).expect(name);
        assert_eq!(r.element_qualified_name(e).as_deref(), Some(*name));
    }
    // The connection's ends are its own, found by the type's end names and
    // by the binary positional names alike.
    let ln = r.resolve_qualified("P::s::ln").unwrap();
    let left = r.resolve_qualified("P::s::ln::left").unwrap();
    assert_eq!(r.owner(left), Some(ln));
    assert_eq!(r.resolve_qualified("P::s::ln::source"), Some(left));
    assert_eq!(
        r.resolve_qualified("P::s::ln::target"),
        r.resolve_qualified("P::s::ln::right")
    );
    assert_ne!(Some(left), r.resolve_qualified("P::Link::left"));
    // A chain through the end reaches the connected part's members.
    assert_eq!(
        r.resolve_qualified("P::s::ln::left::mass"),
        r.resolve_qualified("P::V::mass")
    );
    // The role members are the owners' own, not the library features they
    // stand in for.
    for (owner, member) in [("P::R", "subj"), ("P::VD", "obj"), ("P::C", "result")] {
        let o = r.resolve_qualified(owner).unwrap();
        let m = r.resolve_qualified(&format!("{owner}::{member}")).unwrap();
        assert_eq!(r.owner(m), Some(o), "{owner}::{member}");
    }
    // The written references reach the members through those names.
    for name in [
        "P::V::mass",
        "P::s::ln::right",
        "P::s::ln::left",
        "P::s::sc::earlierOccurrence",
        "P::s::bd::sameThing",
        "P::VD::obj::r",
        "P::C::result",
        "P::R::subj",
    ] {
        let e = r.resolve_qualified(name).unwrap();
        assert!(!r.references_to(e).is_empty(), "{name}");
    }
}

/// The connection definition specializes a library type first and a user
/// type with named ends second: the user type's end names find the
/// definition's own unnamed ends, and a usage's typed by it.
pub const MULTI_GENERAL: &str = "package P {
    part def A { attribute m; }
    part a : A;
    part b : A;
    connection def U { end ue1 : A; end ue2 : A; }
    connection def X :> Connections::Connection, U { end : A; end : A; }
    connection x : X connect a to b;
    ref r1 :> X::ue1;
    ref r2 :> X::ue2;
    ref r3 :> x.ue2.m;
}";

#[test]
fn typed_end_names_come_from_any_general_with_the_library() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source("seams.sysml", MULTI_GENERAL);
    assert!(!model.has_errors(), "{:?}", model.units()[0].diagnostics);
    let mut r = ResolvedModel::build(&model);
    // The library carries unresolved references of its own; the model's
    // must all resolve.
    let unresolved: Vec<String> = r
        .unresolved_references()
        .into_iter()
        .filter(|u| {
            r.element_qualified_name(u.owner)
                .is_some_and(|q| q == "P" || q.starts_with("P::"))
        })
        .map(|u| u.spelling)
        .collect();
    assert!(unresolved.is_empty(), "{unresolved:?}");
    for (owner, ends) in [("P::X", ["ue1", "ue2"]), ("P::x", ["ue1", "ue2"])] {
        let o = r.resolve_qualified(owner).unwrap();
        for end in ends {
            let name = format!("{owner}::{end}");
            let e = r.resolve_semantic_qualified(&name).expect(&name);
            assert_eq!(r.owner(e), Some(o), "{name}");
            assert_eq!(r.element_qualified_name(e), Some(name.clone()));
        }
    }
    assert_eq!(
        r.resolve_qualified("P::x::source"),
        r.resolve_qualified("P::x::ue1")
    );
    for name in ["P::X::ue1", "P::X::ue2", "P::A::m"] {
        let e = r.resolve_qualified(name).unwrap();
        assert!(!r.references_to(e).is_empty(), "{name}");
    }
}
