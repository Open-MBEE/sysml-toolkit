//! Minimal-qualification respelling: `Session::minimize_qualifications`
//! rewrites every reference with the shortest spelling that still resolves
//! to the same element, verified by reparse.

use sysmlv2_transform::Session;

fn session(src: &str) -> Session {
    Session::from_sources(vec![("m.sysml".into(), src.into())]).expect("clean parse")
}

#[test]
fn qualified_references_shorten_through_imports() {
    let mut s = session(
        "package Lib {\n\
         \x20   part def Wheel;\n\
         }\n\
         package Car {\n\
         \x20   private import Lib::*;\n\
         \x20   part w : Lib::Wheel;\n\
         }\n",
    );
    let report = s.minimize_qualifications().expect("minimize");
    assert_eq!(report.reverted, 0, "no candidate should fail verification");
    assert!(report.respelled >= 1, "{report:?}");
    let text = s.source(0).unwrap();
    assert!(
        text.contains("part w : Wheel;"),
        "imported target should respell bare:\n{text}"
    );
}

#[test]
fn global_rooted_references_shorten() {
    // The `$::`-rooted spelling the JSON lift prints.
    let mut s = session(
        "package Lib {\n\
         \x20   part def Wheel;\n\
         }\n\
         package Car {\n\
         \x20   private import Lib::*;\n\
         \x20   part w : $::Lib::Wheel;\n\
         }\n",
    );
    let report = s.minimize_qualifications().expect("minimize");
    assert!(report.respelled >= 1, "{report:?}");
    let text = s.source(0).unwrap();
    assert!(
        text.contains("part w : Wheel;"),
        "the $::-rooted typing should respell bare:\n{text}"
    );
}

#[test]
fn import_targets_shorten() {
    // The lift prints import targets `$::`-rooted; the pass respells
    // them like any other site, gated by the reparse verification.
    let mut s = session(
        "package Lib {\n\
         \x20   part def Wheel;\n\
         }\n\
         package Car {\n\
         \x20   private import $::Lib::*;\n\
         \x20   part w : $::Lib::Wheel;\n\
         }\n",
    );
    let report = s.minimize_qualifications().expect("minimize");
    assert_eq!(report.reverted, 0, "{report:?}");
    let text = s.source(0).unwrap();
    assert!(
        text.contains("private import Lib::*;"),
        "the import target should drop the root marker:\n{text}"
    );
    assert!(text.contains("part w : Wheel;"), "{text}");
}

#[test]
fn shadowed_import_targets_keep_their_qualification() {
    // `import B::*` inside A would find A::B, not P::B — the target
    // must keep a disambiguating spelling.
    let mut s = session(
        "package P {\n\
         \x20   part def B {\n\
         \x20       part def Inner;\n\
         \x20   }\n\
         \x20   part def A {\n\
         \x20       part def B;\n\
         \x20       private import $::P::B::*;\n\
         \x20       part i : $::P::B::Inner;\n\
         \x20   }\n\
         }\n",
    );
    s.minimize_qualifications().expect("minimize");
    let text = s.source(0).unwrap();
    assert!(
        text.contains("private import P::B::*;"),
        "shadowed import target keeps the qualifying prefix:\n{text}"
    );
}

#[test]
fn shadowed_names_keep_their_qualification() {
    // A bare `B` at the site resolves to the *sibling* `B`, so the
    // reference must keep (only) the disambiguating prefix.
    let mut s = session(
        "package P {\n\
         \x20   part def A {\n\
         \x20       part def B;\n\
         \x20   }\n\
         \x20   part def B;\n\
         \x20   part x : A::B;\n\
         \x20   part y : B;\n\
         }\n",
    );
    s.minimize_qualifications().expect("minimize");
    let text = s.source(0).unwrap();
    assert!(
        text.contains("part x : A::B;"),
        "shadowed target must stay qualified:\n{text}"
    );
    assert!(text.contains("part y : B;"), "{text}");
}

#[test]
fn minimize_is_idempotent_and_ids_stable() {
    let src = "package Lib {\n\
               \x20   part def Wheel;\n\
               }\n\
               package Car {\n\
               \x20   private import Lib::*;\n\
               \x20   part w : Lib::Wheel;\n\
               }\n";
    let mut s = session(src);
    let before = s.to_compact_json();
    s.minimize_qualifications().expect("first pass");
    let after_first = s.source(0).unwrap().to_string();
    // Respelling references moves no declaration: identical interchange.
    assert_eq!(
        before,
        s.to_compact_json(),
        "minimize must not change the emitted JSON"
    );
    let report = s.minimize_qualifications().expect("second pass");
    assert_eq!(report.respelled, 0, "second pass finds nothing: {report:?}");
    assert_eq!(after_first, s.source(0).unwrap());
}

/// The corpus gate: every corpus file's lifted form minimizes
/// cleanly — the pass succeeds, the emitted interchange JSON is
/// byte-identical (ids and semantics untouched), and the `$::`-rooted
/// spellings the lift prints are (ratcheted) eliminated.
#[test]
fn corpus_lift_minimize_gate() {
    // Unoptimized lifter frames run to 128 KB per nesting level, and the
    // deepest corpus model sits within bytes of the default test-thread
    // stack. Give the gate its own generous stack so unrelated struct
    // growth cannot trip it.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(corpus_lift_minimize_gate_body)
        .unwrap()
        .join()
        .unwrap();
}

fn corpus_lift_minimize_gate_body() {
    let files = sysmlv2_testkit::user_files();
    assert!(files.len() > 100, "expected the corpus checkout");
    let (mut minimized, mut respelled, mut reverted) = (0usize, 0usize, 0usize);
    let (mut globals_before, mut globals_after) = (0usize, 0usize);
    for path in files {
        let original = std::fs::read_to_string(&path).unwrap();
        let name = path
            .file_name()
            .map(|n| n.to_string_lossy().into_owned())
            .unwrap_or_default();
        let Ok(s) = Session::from_sources(vec![(name.clone(), original)]) else {
            continue; // files that don't parse are out of scope
        };
        let json = s.to_compact_json();
        // The lifted form — the `$::`-rooted printing minimize targets.
        let mut lifted = Session::from_interchange_json(&json)
            .unwrap_or_else(|e| panic!("{name}: lift failed: {e:?}"));
        // The invariant is against the *lifted* session's own emission:
        // the lift renames the unit (root-namespace convention), which
        // moves ids — minimize itself must move nothing.
        let pre_json = lifted.to_compact_json();
        let before: usize = lifted
            .units()
            .map(|(_, _, text)| text.matches("$::").count())
            .sum();
        let report = lifted
            .minimize_qualifications()
            .unwrap_or_else(|e| panic!("{name}: minimize failed: {e:?}"));
        let after: usize = lifted
            .units()
            .map(|(_, _, text)| text.matches("$::").count())
            .sum();
        assert_eq!(
            lifted.to_compact_json(),
            pre_json,
            "{name}: minimize changed the emitted interchange JSON"
        );
        minimized += 1;
        respelled += report.respelled;
        reverted += report.reverted;
        globals_before += before;
        globals_after += after;
    }
    eprintln!(
        "minimize corpus: {minimized} files, {respelled} sites respelled \
         ({reverted} reverted by verification), $:: spellings {globals_before} -> {globals_after}"
    );
    assert!(minimized > 200, "corpus coverage collapsed: {minimized}");
    // The ratchet, measured at introduction (251 files, 5913 global
    // spellings lifted, 4651 sites respelled; re-baselined to 5923/1023
    // when chain-written specialization targets began contributing
    // inherited members — more references resolve, so more lifted sites
    // print `$::`-rooted): what stays qualified is imports (their
    // resolution rules differ), chains continuing into a further global
    // link (anchoring), and genuinely shadowed or usage-scoped names
    // plain resolution cannot reach. May only move down.
    assert!(
        globals_after <= 1023,
        "$:: spellings after minimize grew: {globals_after} (was {globals_before} pre-pass)"
    );
}

/// `minimal_spelling` answers the shortest suffix that resolves from
/// the context declaration's scope — no rewriting involved.
#[test]
fn minimal_spelling_prefers_shortest_resolvable_suffix() {
    let mut s = session(
        "package P {\n\
         \x20   part holder {\n\
         \x20       attribute grade : Grade;\n\
         \x20   }\n\
         \x20   enum def Grade {\n\
         \x20       low;\n\
         \x20       high;\n\
         \x20   }\n\
         }\n",
    );
    let ctx = s
        .resolved()
        .resolve_qualified("P::holder::grade")
        .expect("attribute");
    let lit = s
        .resolved()
        .resolve_qualified("P::Grade::high")
        .expect("literal");
    // Literals need their enum's name; the enum itself spells bare.
    assert_eq!(s.minimal_spelling(ctx, lit).as_deref(), Some("Grade::high"));
    let ty = s.resolved().resolve_qualified("P::Grade").expect("enum");
    assert_eq!(s.minimal_spelling(ctx, ty).as_deref(), Some("Grade"));
}

/// A member import (`import Pkg::Member;`) is respelled by *unrooting* the
/// lift's `$::`, never by re-deriving the path from the target element's
/// qualified name. Two properties fall out, and both matter:
///
/// - the root goes, so the text matches what an author would write;
/// - the final segment is preserved verbatim, so an `alias` import keeps
///   naming the alias Membership. An element can have several memberships,
///   and the element's own qualified name spells only one of them — the
///   re-derived path would silently re-point the import, which is a model
///   change wearing a respelling's clothes.
#[test]
fn member_imports_unroot_without_changing_which_membership_they_name() {
    for (label, src, want) in [
        (
            "plain member import",
            "package Lib {\n\
             \x20   part def Widget;\n\
             }\n\
             package P {\n\
             \x20   private import Lib::Widget;\n\
             \x20   part a : Widget;\n\
             }\n",
            "private import Lib::Widget;",
        ),
        (
            "aliased member import",
            "package Defs {\n\
             \x20   part def Vehicle;\n\
             \x20   alias Car for Vehicle;\n\
             }\n\
             package Uses {\n\
             \x20   private import Defs::Car;\n\
             \x20   part v : Car;\n\
             }\n",
            "private import Defs::Car;",
        ),
    ] {
        // Through the lift, which is what introduces the `$::` root.
        let json = session(src).to_compact_json();
        let mut lifted =
            Session::from_interchange_json(&json).unwrap_or_else(|e| panic!("{label}: {e:?}"));
        let before = lifted.to_compact_json();
        lifted.minimize_qualifications().expect("minimize");
        let text = lifted.source(0).unwrap();

        assert!(
            text.contains(want),
            "{label}: expected `{want}`, got:\n{text}"
        );
        assert!(
            !text.contains("$::"),
            "{label}: the global root should be gone:\n{text}"
        );
        // The decisive one: respelling must not move the model.
        assert_eq!(
            lifted.to_compact_json(),
            before,
            "{label}: minimize changed the emitted interchange JSON"
        );
    }
}

/// The member-import rule is *shortest resolvable suffix of at least two
/// segments*, which is more than unrooting: the leading segment may resolve
/// by lexical scoping or through a sibling import of the same namespace
/// (the reference implementation consults both). On authored text that is
/// usually the spelling the author wrote. A written path of one segment
/// keeps its single candidate, so a root-level member import unroots too.
#[test]
fn member_imports_shorten_to_the_shortest_resolvable_suffix() {
    for (label, src, want) in [
        (
            "leading segment is a sibling package of an enclosing namespace",
            "package A {\n\
             \x20   package B {\n\
             \x20       part def C;\n\
             \x20   }\n\
             \x20   package P {\n\
             \x20       private import A::B::C;\n\
             \x20       part x : C;\n\
             \x20   }\n\
             }\n",
            "private import B::C;",
        ),
        (
            "leading segment is visible through a sibling import",
            "package A {\n\
             \x20   package B {\n\
             \x20       part def C;\n\
             \x20   }\n\
             }\n\
             package P {\n\
             \x20   private import A::*;\n\
             \x20   private import A::B::C;\n\
             \x20   part x : C;\n\
             }\n",
            "private import B::C;",
        ),
        (
            "one-segment written path",
            "package Lib {\n\
             \x20   part def Widget;\n\
             }\n\
             package P {\n\
             \x20   private import Lib;\n\
             \x20   part a : Lib::Widget;\n\
             }\n",
            "private import Lib;",
        ),
    ] {
        let json = session(src).to_compact_json();
        let mut lifted =
            Session::from_interchange_json(&json).unwrap_or_else(|e| panic!("{label}: {e:?}"));
        let before = lifted.to_compact_json();
        lifted.minimize_qualifications().expect("minimize");
        let text = lifted.source(0).unwrap();

        assert!(
            text.contains(want),
            "{label}: expected `{want}`, got:\n{text}"
        );
        assert!(
            !text.contains("$::"),
            "{label}: the global root should be gone:\n{text}"
        );
        assert_eq!(
            lifted.to_compact_json(),
            before,
            "{label}: minimize changed the emitted interchange JSON"
        );
    }
}

/// The floor and the fallbacks: a member import never collapses to its
/// last segment alone, keeps its full written path when no shorter suffix
/// resolves from the site, and keeps the `$::` root when even the full
/// path would resolve to something else there.
#[test]
fn member_imports_keep_their_qualification_when_a_shorter_suffix_does_not_resolve() {
    for (label, src, want, forbidden) in [
        (
            "nested target: the full written path, unrooted",
            "package Outer {\n\
             \x20   package Lib {\n\
             \x20       part def Widget;\n\
             \x20   }\n\
             }\n\
             package P {\n\
             \x20   private import Outer::Lib::Widget;\n\
             \x20   part a : Widget;\n\
             }\n",
            "private import Outer::Lib::Widget;",
            "import Lib::Widget;",
        ),
        (
            "never the last segment alone",
            "package Lib {\n\
             \x20   part def Widget;\n\
             }\n\
             package P {\n\
             \x20   private import Lib::Widget;\n\
             \x20   part a : Widget;\n\
             }\n",
            "private import Lib::Widget;",
            "import Widget;",
        ),
        (
            "shadowed leading segment: the root stays",
            "package Outer {\n\
             \x20   package Lib {\n\
             \x20       part def Widget;\n\
             \x20   }\n\
             }\n\
             package P {\n\
             \x20   part def Outer;\n\
             \x20   private import $::Outer::Lib::Widget;\n\
             \x20   part a : Widget;\n\
             }\n",
            "private import $::Outer::Lib::Widget;",
            "import Outer::Lib::Widget;",
        ),
    ] {
        let json = session(src).to_compact_json();
        let mut lifted =
            Session::from_interchange_json(&json).unwrap_or_else(|e| panic!("{label}: {e:?}"));
        let before = lifted.to_compact_json();
        lifted.minimize_qualifications().expect("minimize");
        let text = lifted.source(0).unwrap();

        assert!(
            text.contains(want),
            "{label}: expected `{want}`, got:\n{text}"
        );
        assert!(
            !text.contains(forbidden),
            "{label}: must not respell to `{forbidden}`:\n{text}"
        );
        assert_eq!(
            lifted.to_compact_json(),
            before,
            "{label}: minimize changed the emitted interchange JSON"
        );
    }
}
