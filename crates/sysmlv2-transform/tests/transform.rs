//! Transformation engine: splice minimality (bytes outside the edit
//! are untouched — notes and formatting survive), inverse-edit identity,
//! semantic-identity rejection, and every EditBuilder operation. The
//! corpus gate drives engine renames A→B→A over the non-library corpus
//! and requires byte identity.

use std::path::PathBuf;
use sysmlv2_transform::{Session, TransformError};

const DEMO: &str = "package Defs {
    // the wheel family
    part def Wheel;
    part def SpareWheel :> Wheel; // note kept
}
package Rig {
    private import Defs::Wheel;
    part def Vehicle {
        part front : Wheel;
        part spare : Defs::SpareWheel;
        attribute count = 2;
    }
    part v : Vehicle;
}
";

fn session(src: &str) -> Session {
    Session::from_sources(vec![("t.sysml".into(), src.into())]).expect("parses")
}

fn text(s: &Session) -> String {
    s.units().next().unwrap().2.to_string()
}

#[test]
fn rename_is_splice_minimal_and_note_preserving() {
    let mut s = session(DEMO);
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut edit = s.edit();
    edit.rename(e, "RoadWheel");
    edit.commit().expect("commit");

    // Byte-exact expectation: only the four `Wheel` spellings changed —
    // both notes, all blank structure, every other byte identical.
    assert_eq!(
        text(&s),
        "package Defs {
    // the wheel family
    part def RoadWheel;
    part def SpareWheel :> RoadWheel; // note kept
}
package Rig {
    private import Defs::RoadWheel;
    part def Vehicle {
        part front : RoadWheel;
        part spare : Defs::SpareWheel;
        attribute count = 2;
    }
    part v : Vehicle;
}
"
    );
    // The renamed model still resolves cleanly and can be queried.
    assert_eq!(s.resolved().unresolved_count(), 0);
    assert!(s.resolved().resolve_qualified("Defs::RoadWheel").is_some());
}

#[test]
fn inverse_rename_is_byte_identical() {
    let mut s = session(DEMO);
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut edit = s.edit();
    edit.rename(e, "Zz9Tmp");
    edit.commit().expect("forward");
    let e = s.resolved().resolve_qualified("Defs::Zz9Tmp").unwrap();
    let mut edit = s.edit();
    edit.rename(e, "Wheel");
    edit.commit().expect("back");
    assert_eq!(text(&s), DEMO);
}

#[test]
fn rename_to_restricted_name_quotes() {
    let mut s = session(DEMO);
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut edit = s.edit();
    edit.rename(e, "in");
    edit.commit().expect("commit");
    assert!(text(&s).contains("part def 'in';"), "{}", text(&s));
    assert!(text(&s).contains("part front : 'in';"), "{}", text(&s));
    // And back, from the quoted spelling.
    let e = s.resolved().resolve_qualified("Defs::'in'").unwrap();
    let mut edit = s.edit();
    edit.rename(e, "Wheel");
    edit.commit().expect("back");
    assert_eq!(text(&s), DEMO);
}

#[test]
fn rename_leaves_alias_spellings_alone() {
    let src = "package P {
    part def Wheel;
    alias W for Wheel;
    part a : Wheel;
    part b : W;
}
";
    let mut s = session(src);
    let e = s.resolved().resolve_qualified("P::Wheel").unwrap();
    let mut edit = s.edit();
    edit.rename(e, "RoadWheel");
    edit.commit().expect("commit");
    let out = text(&s);
    // The alias declaration retargets (it spells `Wheel`), the
    // alias-written use does not.
    assert!(out.contains("alias W for RoadWheel;"), "{out}");
    assert!(out.contains("part b : W;"), "{out}");
    assert!(out.contains("part a : RoadWheel;"), "{out}");
}

#[test]
fn rename_rejects_shadow_capture() {
    let src = "package P {
    part def T;
    package Q {
        part def U;
        part x : T;
    }
}
";
    let mut s = session(src);
    let e = s.resolved().resolve_qualified("P::Q::U").unwrap();
    let mut edit = s.edit();
    edit.rename(e, "T");
    let err = edit.commit().expect_err("must reject capture");
    assert!(
        matches!(err, TransformError::SemanticIdentity { .. }),
        "{err}"
    );
    // Rolled back: source and model unchanged.
    assert_eq!(text(&s), src);
    assert!(s.resolved().resolve_qualified("P::Q::U").is_some());
}

#[test]
fn set_feature_value_replaces_and_adds() {
    let src = "package P {
    part def V {
        attribute mass = 10; // keep me
        attribute empty;
    }
}
";
    let mut s = session(src);
    let mass = s.resolved().resolve_qualified("P::V::mass").unwrap();
    let empty = s.resolved().resolve_qualified("P::V::empty").unwrap();
    let mut edit = s.edit();
    edit.set_feature_value(mass, "20 + 1");
    edit.set_feature_value(empty, "3");
    edit.commit().expect("commit");
    let out = text(&s);
    assert!(out.contains("attribute mass = 20 + 1; // keep me"), "{out}");
    assert!(out.contains("attribute empty = 3;"), "{out}");
    let mass = s.resolved().resolve_qualified("P::V::mass").unwrap();
    assert_eq!(s.resolved().evaluate(mass).unwrap().to_string(), "21");

    // A malformed expression is rejected at plan time.
    let mut edit = s.edit();
    edit.set_feature_value(mass, "1 +");
    assert!(matches!(
        edit.commit(),
        Err(TransformError::InvalidExpression { .. })
    ));
}

#[test]
fn set_feature_value_adds_to_typed_declaration() {
    // The typing reference is the last token before the `;`, exactly
    // where the ` = expr` splice inserts — its span must not stretch
    // over the inserted text in the identity check.
    let src = "package P {
    attribute def A;
    part def V {
        attribute watts : A;
        attribute rated : A = 5;
        attribute empty;
    }
}
";
    let mut s = session(src);
    let watts = s.resolved().resolve_qualified("P::V::watts").unwrap();
    let rated = s.resolved().resolve_qualified("P::V::rated").unwrap();
    let empty = s.resolved().resolve_qualified("P::V::empty").unwrap();
    let mut edit = s.edit();
    edit.set_feature_value(watts, "60"); // add to a typed value-less feature
    edit.set_feature_value(rated, "7"); // replace on a typed feature
    edit.set_feature_value(empty, "3"); // add to an untyped feature
    edit.commit().expect("commit");
    let out = text(&s);
    assert!(out.contains("attribute watts : A = 60;"), "{out}");
    assert!(out.contains("attribute rated : A = 7;"), "{out}");
    assert!(out.contains("attribute empty = 3;"), "{out}");
    // The typing survived: watts still resolves and stays typed by A.
    let watts = s.resolved().resolve_qualified("P::V::watts").unwrap();
    let a = s.resolved().resolve_qualified("P::A").unwrap();
    assert!(s.resolved().typings(watts).contains(&a));
    assert_eq!(s.resolved().evaluate(watts).unwrap().to_string(), "60");
}

#[test]
fn check_dry_runs_the_full_pipeline_without_committing() {
    let src = "package P {
    part def T;
    part def Q {
        part def U;
        part u : U;
    }
}
";
    let mut s = session(src);

    // A batch that would commit: check reports the exact splices and
    // findings, but the session is untouched.
    let q = s.resolved().resolve_qualified("P::Q").unwrap();
    let mut edit = s.edit();
    edit.insert_member(q, "part t2 : T;");
    let report = edit.check().expect("would commit");
    assert!(!report.splices.is_empty());
    assert_eq!(text(&s), src);
    assert!(s.resolved().resolve_qualified("P::Q::t2").is_none());

    // Element handles minted before the check stay valid (no rebuild).
    assert!(s.resolved().member_extent(q).is_some());

    // The same batch really commits afterwards, producing what check
    // predicted.
    let mut edit = s.edit();
    edit.insert_member(q, "part t2 : T;");
    let committed = edit.commit().expect("commit");
    assert_eq!(committed.splices.len(), report.splices.len());
    assert_eq!(committed.splices[0].text, report.splices[0].text);
    assert!(s.resolved().resolve_qualified("P::Q::t2").is_some());

    // A batch that would refuse: check returns the exact refusal —
    // renaming U to T would capture `u : U`'s reference — session
    // untouched.
    let u = s.resolved().resolve_qualified("P::Q::U").unwrap();
    let before = text(&s);
    let mut edit = s.edit();
    edit.rename(u, "T");
    let err = edit.check().expect_err("would refuse");
    assert!(
        matches!(err, TransformError::SemanticIdentity { .. }),
        "{err}"
    );
    assert_eq!(text(&s), before);
    assert!(s.resolved().resolve_qualified("P::Q::U").is_some());
}

#[test]
fn set_feature_type_replaces_and_adds_in_place() {
    let src = "package P {
    attribute def A;
    attribute def B;
    part def V {
        attribute x : A = 3; // keep me
        attribute y : A {
            doc /* keep this body */
        }
        attribute bare;
        attribute empty = 5;
    }
    part def W :> V {
        attribute :>> empty = 7;
    }
}
";
    let mut s = session(src);
    let r = s.resolved();
    let x = r.resolve_qualified("P::V::x").unwrap();
    let y = r.resolve_qualified("P::V::y").unwrap();
    let bare = r.resolve_qualified("P::V::bare").unwrap();
    let empty = r.resolve_qualified("P::V::empty").unwrap();
    let redef = r.resolve_qualified("P::W::empty").unwrap();
    let mut edit = s.edit();
    edit.set_feature_type(x, "B"); // change in place
    edit.set_feature_type(y, "B"); // body preserved
    edit.set_feature_type(bare, "A"); // add where none exists
    edit.set_feature_type(empty, "B"); // add before an existing value
    edit.set_feature_type(redef, "A"); // unnamed redefining feature
    edit.commit().expect("commit");
    let out = text(&s);
    assert!(out.contains("attribute x : B = 3; // keep me"), "{out}");
    assert!(
        out.contains("attribute y : B {\n            doc /* keep this body */\n        }"),
        "{out}"
    );
    assert!(out.contains("attribute bare : A;"), "{out}");
    assert!(out.contains("attribute empty : B = 5;"), "{out}");
    assert!(out.contains("attribute :>> empty : A = 7;"), "{out}");
    // Declaration order untouched; typings resolve to the new targets.
    let a = s.resolved().resolve_qualified("P::A").unwrap();
    let b = s.resolved().resolve_qualified("P::B").unwrap();
    let x = s.resolved().resolve_qualified("P::V::x").unwrap();
    let bare = s.resolved().resolve_qualified("P::V::bare").unwrap();
    assert!(s.resolved().typings(x).contains(&b));
    assert!(s.resolved().typings(bare).contains(&a));

    // A dangling spelling commits with a finding, like inserted text.
    let empty = s.resolved().resolve_qualified("P::V::empty").unwrap();
    let mut edit = s.edit();
    edit.set_feature_type(empty, "Nowhere");
    let report = edit.commit().expect("commit");
    assert!(
        report.findings.iter().any(|f| f.contains("unresolved")),
        "{:?}",
        report.findings
    );

    // A malformed spelling is rejected at plan time.
    let x = s.resolved().resolve_qualified("P::V::x").unwrap();
    let mut edit = s.edit();
    edit.set_feature_type(x, "not a type;");
    assert!(matches!(
        edit.commit(),
        Err(TransformError::InvalidType { .. })
    ));
}

#[test]
fn insert_member_braced_semicolon_and_top_level() {
    let src = "package P {
    part def V {
        part a;
    }
    part def W;
}
";
    let mut s = session(src);
    let v = s.resolved().resolve_qualified("P::V").unwrap();
    let w = s.resolved().resolve_qualified("P::W").unwrap();
    let mut edit = s.edit();
    edit.insert_member(v, "part b;");
    edit.insert_member(w, "part c;");
    edit.insert_top_level("t.sysml", "package Q {\n    part def X;\n}");
    edit.commit().expect("commit");
    assert_eq!(
        text(&s),
        "package P {
    part def V {
        part a;
        part b;
    }
    part def W {
        part c;
    }
}
package Q {
    part def X;
}
"
    );
    assert!(s.resolved().resolve_qualified("P::V::b").is_some());
    assert!(s.resolved().resolve_qualified("P::W::c").is_some());
    assert!(s.resolved().resolve_qualified("Q::X").is_some());

    // Invalid member text is rejected at plan time.
    let v = s.resolved().resolve_qualified("P::V").unwrap();
    let mut edit = s.edit();
    edit.insert_member(v, "part ;;;");
    assert!(matches!(
        edit.commit(),
        Err(TransformError::InvalidMember { .. })
    ));
}

#[test]
fn remove_cleans_the_line_and_guards_references() {
    let mut s = session(DEMO);
    // `front : Wheel` is referenced by nothing — removable.
    let front = s
        .resolved()
        .resolve_qualified("Rig::Vehicle::front")
        .unwrap();
    let mut edit = s.edit();
    edit.remove(front);
    edit.commit().expect("commit");
    let out = text(&s);
    assert!(!out.contains("front"), "{out}");
    assert!(
        out.contains("        part spare : Defs::SpareWheel;"),
        "{out}"
    );
    // No stray blank line where the member was.
    assert!(!out.contains("{\n\n"), "{out}");

    // `Wheel` is referenced from outside — removal must fail, listing
    // the stranded sites, and roll back.
    let before = text(&s);
    let wheel = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut edit = s.edit();
    edit.remove(wheel);
    match edit.commit() {
        Err(TransformError::RemovalBreaksReferences { sites, .. }) => {
            assert!(!sites.is_empty());
        }
        other => panic!("expected RemovalBreaksReferences, got {other:?}"),
    }
    assert_eq!(text(&s), before);
}

#[test]
fn remove_subtree_with_internal_references_is_fine() {
    let src = "package P {
    part def V {
        part a;
        part b :> a;
    }
    part def W;
}
";
    let mut s = session(src);
    // `a` is referenced only from inside V — removing all of V is legal.
    let v = s.resolved().resolve_qualified("P::V").unwrap();
    let mut edit = s.edit();
    edit.remove(v);
    edit.commit().expect("commit");
    assert_eq!(text(&s), "package P {\n    part def W;\n}\n");
}

#[test]
fn refused_remove_rolls_back_to_the_previous_commit() {
    // Two-commit sequence: a successful insert, then a remove that
    // passes planning (nothing references the removed member) but
    // trips commit-time semantic identity — the filtered import's
    // visibility hinges on the removed metadata member, so an
    // untouched typing site stops resolving. The refusal must leave
    // the session exactly at the post-insert state, and the session
    // must stay usable for further edits.
    let src = "package Lib {
    metadata def Marked;
    part def E1 {
        metadata m : Marked;
    }
    part def E2;
}
package P {
    private import Lib::*[@Marked];
    part def Holder;
    part e : E1;
}
";
    let mut s = session(src);

    // Commit 1: insert a member (grows Holder's `;` into a body).
    let holder = s.resolved().resolve_qualified("P::Holder").unwrap();
    let mut edit = s.edit();
    edit.insert_member(holder, "attribute X : Real;");
    edit.commit().expect("insert commits");
    let after_insert = text(&s);
    assert!(
        after_insert.contains("attribute X : Real;"),
        "{after_insert}"
    );

    // Commit 2 (refused): removing the metadata member hides E1 from
    // the filtered import — `part e : E1` no longer resolves.
    let meta = s.resolved().resolve_qualified("Lib::E1::m").unwrap();
    let mut edit = s.edit();
    edit.remove(meta);
    match edit.commit() {
        Err(TransformError::SemanticIdentity { broken }) => {
            assert!(!broken.is_empty());
        }
        other => panic!("expected SemanticIdentity refusal, got {other:?}"),
    }

    // The refusal rolls back to the post-insert state — the earlier
    // commit survives byte for byte.
    assert_eq!(text(&s), after_insert);

    // And the session still takes edits.
    let e2 = s.resolved().resolve_qualified("Lib::E2").unwrap();
    let mut edit = s.edit();
    edit.remove(e2);
    edit.commit().expect("post-refusal commit");
    let out = text(&s);
    assert!(!out.contains("part def E2"), "{out}");
    assert!(out.contains("attribute X : Real;"), "{out}");
}

#[test]
fn retarget_respells_one_site() {
    let mut s = session(DEMO);
    let front = s
        .resolved()
        .resolve_qualified("Rig::Vehicle::front")
        .unwrap();
    let spare_def = s.resolved().resolve_qualified("Defs::SpareWheel").unwrap();
    let wheel = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let site = s
        .resolved()
        .references_to(wheel)
        .into_iter()
        .find(|site| site.kind == "type")
        .expect("front's typing site");
    let mut edit = s.edit();
    edit.retarget(site, spare_def);
    edit.commit().expect("commit");
    let out = text(&s);
    assert!(out.contains("part front : Defs::SpareWheel;"), "{out}");
    let front_ty = s.resolved().typings(front);
    assert_eq!(front_ty, vec![spare_def]);
}

#[test]
fn id_map_tracks_renamed_paths() {
    let mut s = session(DEMO);
    let e = s.resolved().resolve_qualified("Rig::Vehicle").unwrap();
    let old_id = s.resolved().element_id(e);
    let mut edit = s.edit();
    edit.rename(e, "Car");
    let report = edit.commit().expect("commit");
    let renamed = s.resolved().resolve_qualified("Rig::Car").unwrap();
    let new_id = s.resolved().element_id(renamed);
    assert_ne!(old_id, new_id);
    assert!(
        report.id_map.contains(&(old_id, new_id)),
        "{:?}",
        report.id_map
    );
    // Untouched elements keep their ids and stay out of the map.
    let wheel = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let wheel_id = s.resolved().element_id(wheel);
    assert!(report.id_map.iter().all(|&(old, _)| old != wheel_id));
}

#[test]
fn batch_edits_compose() {
    let mut s = session(DEMO);
    let wheel = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let count = s
        .resolved()
        .resolve_qualified("Rig::Vehicle::count")
        .unwrap();
    let vehicle = s.resolved().resolve_qualified("Rig::Vehicle").unwrap();
    let mut edit = s.edit();
    edit.rename(wheel, "RoadWheel");
    edit.set_feature_value(count, "4");
    edit.insert_member(vehicle, "part rear : RoadWheel;");
    edit.commit().expect("commit");
    let out = text(&s);
    assert!(out.contains("part front : RoadWheel;"), "{out}");
    assert!(out.contains("attribute count = 4;"), "{out}");
    assert!(out.contains("part rear : RoadWheel;"), "{out}");
    assert_eq!(s.resolved().unresolved_count(), 0);
}

/// One batch may rename an element AND things inside it — the
/// verification expectations for the inner renames' rewritten
/// references must follow the ancestor's rename instead of refusing
/// on the shifted qualified name.
#[test]
fn batch_renames_element_and_its_parameters() {
    let src = "package P {
    calc def old_calc {
        in mu_x;
        in r_y;
        return z = mu_x * 2 + (r_y + mu_x);
    }
}
";
    let mut s = session(src);
    let def = s.resolved().resolve_qualified("P::old_calc").unwrap();
    let mu = s.resolved().resolve_qualified("P::old_calc::mu_x").unwrap();
    let r = s.resolved().resolve_qualified("P::old_calc::r_y").unwrap();
    let mut edit = s.edit();
    edit.rename(def, "NewCalc");
    edit.rename(mu, "muX");
    edit.rename(r, "rY");
    edit.commit().expect("legal batch must commit");
    let out = text(&s);
    assert!(out.contains("calc def NewCalc {"), "{out}");
    assert!(out.contains("in muX;"), "{out}");
    assert!(out.contains("return z = muX * 2 + (rY + muX);"), "{out}");
    assert_eq!(s.resolved().unresolved_count(), 0);
    assert!(s.resolved().resolve_qualified("P::NewCalc::muX").is_some());
}

/// Deeper chains map recursively: every ancestor level renamed in the
/// same batch, referenced through a fully qualified spelling.
#[test]
fn batch_renames_nested_chain() {
    let src = "package old_pkg {
    part def old_def {
        part def old_leaf;
    }
}
package Q {
    part y : old_pkg::old_def::old_leaf;
}
";
    let mut s = session(src);
    let p = s.resolved().resolve_qualified("old_pkg").unwrap();
    let d = s.resolved().resolve_qualified("old_pkg::old_def").unwrap();
    let l = s
        .resolved()
        .resolve_qualified("old_pkg::old_def::old_leaf")
        .unwrap();
    let mut edit = s.edit();
    edit.rename(p, "NewPkg");
    edit.rename(d, "NewDef");
    edit.rename(l, "NewLeaf");
    edit.commit().expect("legal batch must commit");
    let out = text(&s);
    assert!(out.contains("part y : NewPkg::NewDef::NewLeaf;"), "{out}");
    assert_eq!(s.resolved().unresolved_count(), 0);
}

/// A batch may chain names (A→B while B→C): the expectation for A's
/// rewritten references spells the final segment `B`, which must NOT
/// be re-mapped through B's own rename.
#[test]
fn batch_chain_renames_do_not_cross_map() {
    let src = "package P {
    part def A;
    part def B;
    part a : A;
    part b : B;
}
";
    let mut s = session(src);
    let a = s.resolved().resolve_qualified("P::A").unwrap();
    let b = s.resolved().resolve_qualified("P::B").unwrap();
    let mut edit = s.edit();
    edit.rename(a, "B");
    edit.rename(b, "C");
    edit.commit().expect("legal batch must commit");
    let out = text(&s);
    assert!(out.contains("part def B;"), "{out}");
    assert!(out.contains("part def C;"), "{out}");
    assert!(out.contains("part a : B;"), "{out}");
    assert!(out.contains("part b : C;"), "{out}");
    assert_eq!(s.resolved().unresolved_count(), 0);
}

/// The same batch shape over the external-validation submodule: a
/// calculation definition renamed to the definition convention AND its
/// parameters to the usage convention, in one commit (skips when the
/// submodule is not initialized).
#[test]
fn external_model_batch_renames_calc_def_and_parameters() {
    let Some(files) = sysmlv2_testkit::apollo_files() else {
        eprintln!("skipping: apollo-11-sysml-v2 submodule not initialized");
        return;
    };
    let sources: Vec<(String, String)> = files
        .iter()
        .map(|f| {
            (
                f.file_name().unwrap().to_string_lossy().into_owned(),
                std::fs::read_to_string(f).unwrap(),
            )
        })
        .collect();
    let mut s = Session::from_sources(sources).expect("parses");
    let qn = |s: &mut Session, q: &str| s.resolved().resolve_qualified(q);
    let def = qn(&mut s, "CalculationsPackage::calculateTliDeltaV").unwrap();
    let mu = qn(&mut s, "CalculationsPackage::calculateTliDeltaV::mu_Earth").unwrap();
    let rl = qn(&mut s, "CalculationsPackage::calculateTliDeltaV::r_leo").unwrap();
    let ra = qn(
        &mut s,
        "CalculationsPackage::calculateTliDeltaV::r_apoapsis",
    )
    .unwrap();
    let mut edit = s.edit();
    edit.rename(def, "CalculateTliDeltaV");
    edit.rename(mu, "muEarth");
    edit.rename(rl, "rLeo");
    edit.rename(ra, "rApoapsis");
    edit.commit().expect("legal batch must commit");
    let calc_unit = s
        .units()
        .find(|(_, name, _)| name.ends_with("CalculationsPackage.sysml"))
        .map(|(_, _, text)| text.to_string())
        .unwrap();
    assert!(
        calc_unit.contains("calc def CalculateTliDeltaV {"),
        "{calc_unit}"
    );
    assert!(
        calc_unit.contains(
            "return deltaV :> ISQ::speed = (muEarth * (2/rLeo - 2/(rLeo + rApoapsis)))^(1/2) - (muEarth / rLeo)^(1/2);"
        ),
        "{calc_unit}"
    );
}

#[test]
fn open_from_disk() {
    let dir = std::env::temp_dir().join(format!("sysmlv2-transform-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join("m.sysml");
    std::fs::write(&path, "package P { part def V; part v : V; }").unwrap();
    let mut s = Session::open(&[PathBuf::from(&path)]).expect("opens");
    let v = s.resolved().resolve_qualified("P::V").unwrap();
    let mut edit = s.edit();
    edit.rename(v, "W");
    edit.commit().expect("commit");
    assert!(s.units().next().unwrap().2.contains("part v : W;"));
    std::fs::remove_dir_all(&dir).ok();
}

/// Corpus gate: engine-driven inverse rename (A→B→A) over every
/// non-library corpus file must be byte-identical. The engine may
/// legitimately *refuse* a rename (semantic identity — e.g. shadow
/// capture); refusals roll back and are skipped, everything else must
/// round-trip exactly.
#[test]
fn corpus_inverse_rename_gate() {
    let files = sysmlv2_testkit::user_files();
    assert!(files.len() > 100, "expected the corpus checkout");
    let mut successes = 0usize;
    let mut refusals = 0usize;
    for path in files {
        let original = std::fs::read_to_string(&path).unwrap();
        let name = path.display().to_string();
        let Ok(mut s) = Session::from_sources(vec![(name.clone(), original.clone())]) else {
            continue; // files that don't parse are out of scope
        };

        // Most-referenced element with a declaration: the hardest case.
        let sites = s.resolved().reference_sites().to_vec();
        let mut counts: std::collections::HashMap<_, usize> = std::collections::HashMap::new();
        for site in &sites {
            *counts.entry(site.target).or_default() += 1;
        }
        let mut ranked: Vec<_> = counts.into_iter().collect();
        ranked.sort_by_key(|&(e, n)| (std::cmp::Reverse(n), e));
        let candidate = ranked.iter().map(|&(e, _)| e).find(|&e| {
            s.resolved().declaration_site(e).is_some() && s.resolved().element_name(e).is_some()
        });
        let Some(e) = candidate else { continue };
        let old_name = s.resolved().element_name(e).unwrap().to_string();
        let old_qn = s.resolved().element_qualified_name(e);
        let Some(old_qn) = old_qn else { continue };
        let new_qn = match old_qn.rfind("::") {
            Some(i) => format!("{}Zz9InverseGate", &old_qn[..i + 2]),
            None => "Zz9InverseGate".to_string(),
        };

        let mut edit = s.edit();
        edit.rename(e, "Zz9InverseGate");
        match edit.commit() {
            Ok(_) => {}
            Err(TransformError::SemanticIdentity { .. }) => {
                assert_eq!(text(&s), original, "refusal must roll back [{name}]");
                refusals += 1;
                continue;
            }
            Err(other) => panic!("forward rename failed [{name}]: {other}"),
        }
        let renamed = s.resolved().resolve_qualified(&new_qn).unwrap_or_else(|| {
            panic!(
                "renamed element resolves [{name}]: {old_qn} -> {new_qn} ({})",
                s.resolved().element_type(e)
            )
        });
        let mut edit = s.edit();
        edit.rename(renamed, &old_name);
        edit.commit()
            .unwrap_or_else(|e| panic!("inverse rename failed [{name}]: {e}"));
        assert_eq!(
            text(&s),
            original,
            "inverse rename must be byte-identical [{name}]"
        );
        successes += 1;
    }
    eprintln!("corpus inverse-rename: {successes} round-tripped, {refusals} refused");
    assert!(
        successes >= 80,
        "gate went vacuous: only {successes} inverse renames succeeded"
    );
}

// ---------------------------------------------------------------------------
// check_sources: the CLI `check` pipeline as a library call
// ---------------------------------------------------------------------------

#[test]
fn check_sources_reports_parse_errors_with_positions() {
    let findings = sysmlv2_transform::check_sources(
        &[(
            "bad.sysml".into(),
            "package Bad {\n  part p : ;\n}\n".into(),
        )],
        None,
    )
    .expect("check runs");
    assert!(!findings.is_empty(), "expected parse findings");
    let f = &findings[0];
    assert_eq!(f.severity, sysmlv2_transform::Severity::Error);
    assert_eq!(f.unit, "bad.sysml");
    assert_eq!(f.line, 2, "position should point at the broken typing");
    assert!(f.col > 0);
}

#[test]
fn check_sources_is_quiet_on_clean_sources_without_library() {
    let findings = sysmlv2_transform::check_sources(
        &[(
            "ok.sysml".into(),
            "package Ok { part def A; part a : A; }\n".into(),
        )],
        None,
    )
    .expect("check runs");
    assert!(findings.is_empty(), "unexpected findings: {findings:?}");
}

#[test]
fn check_sources_reports_unresolved_references_with_library() {
    let lib = sysmlv2_testkit::library_dir();
    let findings = sysmlv2_transform::check_sources(
        &[(
            "dangling.sysml".into(),
            "package Dangling {\n  part p : DoesNotExist;\n}\n".into(),
        )],
        Some(&lib),
    )
    .expect("check runs");
    let unresolved: Vec<_> = findings
        .iter()
        .filter(|f| f.message.contains("unresolved reference"))
        .collect();
    assert_eq!(unresolved.len(), 1, "findings: {findings:?}");
    let f = unresolved[0];
    assert_eq!(f.severity, sysmlv2_transform::Severity::Warning);
    assert_eq!((f.line, f.unit.as_str()), (2, "dangling.sysml"));
}

#[test]
fn check_sources_accepts_library_typed_sources() {
    let lib = sysmlv2_testkit::library_dir();
    let findings = sysmlv2_transform::check_sources(
        &[(
            "typed.sysml".into(),
            "package Typed {\n  attribute mass : ScalarValues::Real;\n}\n".into(),
        )],
        Some(&lib),
    )
    .expect("check runs");
    assert!(findings.is_empty(), "unexpected findings: {findings:?}");
}

#[test]
fn check_sources_parses_kerml_units_by_name() {
    let findings = sysmlv2_transform::check_sources(
        &[("k.kerml".into(), "package K { classifier A; }\n".into())],
        None,
    )
    .expect("check runs");
    assert!(findings.is_empty(), "unexpected findings: {findings:?}");
}

#[test]
fn commit_reports_replayable_splices() {
    let mut s = session(DEMO);
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut edit = s.edit();
    edit.rename(e, "RoadWheel");
    let report = edit.commit().expect("commit");

    // Four spellings of `Wheel` move (declaration, `:>` bound, import,
    // typing); `SpareWheel` spellings are different tokens and stay.
    assert_eq!(report.splices.len(), 4, "splices: {:?}", report.splices);
    assert!(report.splices.iter().all(|sp| sp.unit == "t.sysml"));
    assert!(report.splices.iter().all(|sp| sp.text == "RoadWheel"));

    // The report's contract: splices are in pre-commit coordinates,
    // ordered and non-overlapping — replaying them over the previous
    // source must reproduce the session's post-commit text exactly.
    let mut replayed = String::new();
    let mut cursor = 0usize;
    for sp in &report.splices {
        replayed.push_str(&DEMO[cursor..sp.start as usize]);
        replayed.push_str(&sp.text);
        cursor = sp.end as usize;
    }
    replayed.push_str(&DEMO[cursor..]);
    assert_eq!(replayed, text(&s));
}

#[test]
fn commit_reports_splices_across_ops_and_units() {
    let mut s = Session::from_sources(vec![
        ("a.sysml".into(), "package A {\n    part def X;\n}\n".into()),
        (
            "b.sysml".into(),
            "package B {\n    private import A::X;\n    part x : X;\n}\n".into(),
        ),
    ])
    .expect("parses");
    let x = s.resolved().resolve_qualified("A::X").unwrap();
    let b = s.resolved().resolve_qualified("B").unwrap();
    let mut edit = s.edit();
    edit.rename(x, "Y");
    edit.insert_member(b, "part y : Y;");
    let report = edit.commit().expect("commit");

    let units: std::collections::BTreeSet<&str> =
        report.splices.iter().map(|sp| sp.unit.as_str()).collect();
    assert_eq!(
        units.into_iter().collect::<Vec<_>>(),
        vec!["a.sysml", "b.sysml"]
    );
    // Replay per unit against the pre-commit sources.
    let pre = [
        ("a.sysml", "package A {\n    part def X;\n}\n"),
        (
            "b.sysml",
            "package B {\n    private import A::X;\n    part x : X;\n}\n",
        ),
    ];
    for (idx, (name, old)) in pre.iter().enumerate() {
        let mut replayed = String::new();
        let mut cursor = 0usize;
        for sp in report.splices.iter().filter(|sp| sp.unit == *name) {
            replayed.push_str(&old[cursor..sp.start as usize]);
            replayed.push_str(&sp.text);
            cursor = sp.end as usize;
        }
        replayed.push_str(&old[cursor..]);
        let now = s.units().nth(idx).unwrap().2.to_string();
        assert_eq!(replayed, now, "unit {name}");
    }
}

#[test]
fn move_member_reorders_within_owner() {
    let mut s = session(DEMO);
    let spare = s
        .resolved()
        .resolve_qualified("Rig::Vehicle::spare")
        .unwrap();
    let vehicle = s.resolved().resolve_qualified("Rig::Vehicle").unwrap();
    let mut edit = s.edit();
    edit.move_member(spare, vehicle, Some(0));
    let report = edit.commit().expect("commit");

    // `spare` now precedes `front`; everything else is untouched.
    let t = text(&s);
    let spare_at = t.find("part spare : Defs::SpareWheel;").unwrap();
    let front_at = t.find("part front : Wheel;").unwrap();
    assert!(spare_at < front_at, "order not swapped:\n{t}");
    // Named members chain past their membership's ordinal (IDS.md,
    // id scheme 1), so reordering named siblings moves **no**
    // ids at all — selections in UIs survive the reorder unmapped.
    // (Positional members would still remap; `Vehicle`'s parts are
    // all named.)
    assert!(report.id_map.is_empty(), "{:?}", report.id_map);
    // Splices replay (the report contract holds for moves too).
    let mut replayed = String::new();
    let mut cursor = 0usize;
    for sp in &report.splices {
        replayed.push_str(&DEMO[cursor..sp.start as usize]);
        replayed.push_str(&sp.text);
        cursor = sp.end as usize;
    }
    replayed.push_str(&DEMO[cursor..]);
    assert_eq!(replayed, t);
}

#[test]
fn move_member_reparents_and_remaps_ids() {
    let mut s = Session::from_sources(vec![(
        "t.sysml".into(),
        "package A {\n    part def Unused;\n}\npackage B {\n    part def Keep;\n}\n".into(),
    )])
    .expect("parses");
    let unused = s.resolved().resolve_qualified("A::Unused").unwrap();
    let b = s.resolved().resolve_qualified("B").unwrap();
    let mut edit = s.edit();
    edit.move_member(unused, b, None);
    let report = edit.commit().expect("commit");

    let t = text(&s);
    assert_eq!(
        t,
        "package A {\n}\npackage B {\n    part def Keep;\n    part def Unused;\n}\n"
    );
    // The ownership path changed: the moved element's id moved with it.
    assert!(!report.id_map.is_empty());
    assert!(s.resolved().resolve_qualified("B::Unused").is_some());
    assert!(s.resolved().resolve_qualified("A::Unused").is_none());
}

#[test]
fn move_member_rejects_breaking_outside_references() {
    let mut s = session(DEMO);
    let wheel = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let vehicle = s.resolved().resolve_qualified("Rig::Vehicle").unwrap();
    let mut edit = s.edit();
    edit.move_member(wheel, vehicle, None);
    // `import Defs::Wheel` (and `SpareWheel :> Wheel`) would strand.
    let err = edit.commit().expect_err("must roll back");
    assert!(
        matches!(err, TransformError::SemanticIdentity { .. }),
        "{err}"
    );
    assert_eq!(text(&s), DEMO, "rolled back byte-identically");
}

#[test]
fn move_member_verifies_references_inside_moved_text() {
    const SRC: &str = "package A {\n    part def T;\n    part box;\n    part p : T;\n}\npackage B {\n    part def X;\n}\n";
    // Moving `p` inside `box` keeps `T` visible (outer scope): commits.
    let mut s = Session::from_sources(vec![("t.sysml".into(), SRC.into())]).expect("parses");
    let p = s.resolved().resolve_qualified("A::p").unwrap();
    let bx = s.resolved().resolve_qualified("A::box").unwrap();
    let mut edit = s.edit();
    edit.move_member(p, bx, None);
    edit.commit().expect("in-scope move commits");
    assert!(text(&s).contains("part box {\n        part p : T;\n    }"));

    // Moving `p` into `B` strands its `: T` typing: rolls back.
    let mut s = Session::from_sources(vec![("t.sysml".into(), SRC.into())]).expect("parses");
    let p = s.resolved().resolve_qualified("A::p").unwrap();
    let b = s.resolved().resolve_qualified("B").unwrap();
    let mut edit = s.edit();
    edit.move_member(p, b, None);
    let err = edit.commit().expect_err("must roll back");
    assert!(
        matches!(err, TransformError::SemanticIdentity { .. }),
        "{err}"
    );
    assert_eq!(text(&s), SRC);
}

#[test]
fn move_member_rejects_own_subtree() {
    let mut s = session(DEMO);
    let vehicle = s.resolved().resolve_qualified("Rig::Vehicle").unwrap();
    let front = s
        .resolved()
        .resolve_qualified("Rig::Vehicle::front")
        .unwrap();
    let mut edit = s.edit();
    edit.move_member(vehicle, front, None);
    let err = edit.commit().expect_err("must reject");
    assert!(
        matches!(err, TransformError::MoveIntoOwnSubtree(_)),
        "{err}"
    );
    assert_eq!(text(&s), DEMO);
}

#[test]
fn insert_member_matches_tab_indentation() {
    // A tab-indented unit nests inserted members with tabs, not the
    // canonical four spaces — mixed indentation reads as damage.
    let src = "package P {\n\tpart def V {\n\t\tpart a;\n\t}\n\tpart def W;\n}\n";
    let mut s = session(src);
    let v = s.resolved().resolve_qualified("P::V").unwrap();
    let w = s.resolved().resolve_qualified("P::W").unwrap();
    let mut edit = s.edit();
    edit.insert_member(v, "part b;");
    edit.insert_member(w, "part c;");
    edit.commit().expect("commit");
    assert_eq!(
        text(&s),
        "package P {\n\tpart def V {\n\t\tpart a;\n\t\tpart b;\n\t}\n\tpart def W {\n\t\tpart c;\n\t}\n}\n"
    );
}

#[test]
fn add_unit_creates_an_empty_unit_for_later_batches() {
    let mut s = session(DEMO);
    // Collision and empty names refuse without touching the session.
    let existing = s.units().next().map(|(_, n, _)| n.to_string()).unwrap();
    let mut refused = s.edit();
    refused.add_unit(&existing);
    assert!(matches!(
        refused.commit(),
        Err(TransformError::UnitExists(_))
    ));
    let mut refused = s.edit();
    refused.add_unit("");
    assert!(matches!(
        refused.commit(),
        Err(TransformError::InvalidName(_))
    ));
    assert_eq!(text(&s), DEMO);

    // Born empty; a following batch inserts into it (ops plan against
    // the pre-commit state, so same-batch insertion is out of scope).
    let mut edit = s.edit();
    edit.add_unit("side.sysml");
    let report = edit.commit().expect("add unit commits");
    assert!(
        report.splices.iter().any(|sp| sp.unit == "side.sysml"
            && sp.start == 0
            && sp.end == 0
            && sp.text.is_empty())
    );
    assert_eq!(
        s.units()
            .find(|(_, n, _)| *n == "side.sysml")
            .map(|(_, _, t)| t.to_string()),
        Some(String::new())
    );
    let mut edit = s.edit();
    edit.insert_top_level("side.sysml", "package Side {\n}");
    edit.commit().expect("insert into born unit commits");
    assert_eq!(
        s.units()
            .find(|(_, n, _)| *n == "side.sysml")
            .map(|(_, _, t)| t.to_string()),
        Some("package Side {\n}\n".to_string())
    );
    // A duplicate creation now refuses against the committed state.
    let mut refused = s.edit();
    refused.add_unit("side.sysml");
    assert!(matches!(
        refused.commit(),
        Err(TransformError::UnitExists(_))
    ));
}

#[test]
fn insert_member_reindents_continuation_lines() {
    // A multi-line member arrives in top-level form (its own internal
    // unit — tabs here); every line lands at the destination depth in
    // the unit's indent style: internal tab levels become the file's
    // four spaces, and the closing brace sits at member depth instead
    // of column zero.
    let src = "package P {\n    part def V {\n        part a;\n    }\n}\n";
    let mut s = session(src);
    let v = s.resolved().resolve_qualified("P::V").unwrap();
    let mut edit = s.edit();
    edit.insert_member(
        v,
        "part def B {\n\tdoc /* two\n\tlines */\n\tpart inner {\n\t\tpart deep;\n\t}\n}",
    );
    edit.commit().expect("commit");
    assert_eq!(
        text(&s),
        "package P {\n    part def V {\n        part a;\n        part def B {\n            doc /* two\n            lines */\n            part inner {\n                part deep;\n            }\n        }\n    }\n}\n",
        "{}",
        text(&s)
    );
}

// ---------------------------------------------------------------- replace

/// The identity-preserving update: where remove+insert refuses a member
/// that outside references target, replace_member swaps the declaration
/// and judges validity on the post-edit model.
#[test]
fn replace_member_survives_outside_references() {
    let mut s = session(DEMO);
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    // remove+insert refuses: Rig::Vehicle::front references Wheel.
    let mut refused = s.edit();
    refused.remove(e);
    assert!(matches!(
        refused.commit(),
        Err(TransformError::RemovalBreaksReferences { .. })
    ));
    // replace_member with the same name: references untouched, body grows.
    // The replacement arrives in top-level form (tab-nested); it is
    // re-spelled at the member's own depth in the unit's indent style.
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut edit = s.edit();
    edit.replace_member(e, "part def Wheel {\n\tattribute radius = 5;\n}");
    let report = edit.commit().expect("replace commits");
    assert!(
        text(&s).contains("part def Wheel {\n        attribute radius = 5;\n    }"),
        "{}",
        text(&s)
    );
    assert!(text(&s).contains("part front : Wheel;"), "{}", text(&s));
    // Splice minimality: the note above the family survives.
    assert!(text(&s).contains("// the wheel family"));
    drop(report);
}

/// A declared-name change respells outside references (rename machinery)
/// and records the correspondence; alias spellings stay as written.
#[test]
fn replace_member_renames_respell_references() {
    let mut s = session(DEMO);
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut edit = s.edit();
    edit.replace_member(e, "part def RoadWheel;");
    edit.commit().expect("replace commits");
    let t = text(&s);
    assert!(t.contains("part def RoadWheel;"), "{t}");
    assert!(t.contains("part front : RoadWheel;"), "{t}");
    assert!(t.contains("private import Defs::RoadWheel;"), "{t}");
    assert!(t.contains(":> RoadWheel;"), "{t}");
    assert!(!t.contains("part def Wheel"), "{t}");
    // And the replaced element resolves under its new qualified name.
    assert!(s.resolved().resolve_qualified("Defs::RoadWheel").is_some());
}

/// Replacement text must be exactly one parseable member.
#[test]
fn replace_member_shape_refusals() {
    let mut s = session(DEMO);
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut two = s.edit();
    two.replace_member(e, "part def A;\npart def B;");
    assert!(matches!(
        two.commit(),
        Err(TransformError::InvalidMember { .. })
    ));
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut broken = s.edit();
    broken.replace_member(e, "part def {");
    assert!(matches!(
        broken.commit(),
        Err(TransformError::InvalidMember { .. })
    ));
    // Refusals roll back: the model is untouched.
    assert!(text(&s).contains("part def Wheel;"));
}

/// Renaming onto a sibling that would capture references refuses at
/// post-state verification, not silently.
#[test]
fn replace_member_refuses_reference_capture() {
    let mut s = session(DEMO);
    let e = s.resolved().resolve_qualified("Defs::Wheel").unwrap();
    let mut edit = s.edit();
    // front/spare would now resolve through the renamed element, but
    // `:> Wheel` inside SpareWheel names a vanished element.
    edit.replace_member(e, "part def SpareWheel;");
    assert!(edit.commit().is_err());
    assert!(text(&s).contains("part def Wheel;"), "rolled back");
}

/// A batch removing both a member and the annotation that references it
/// commits in one edit: the annotation's reference site leaves with its
/// own removal and must not veto the member's.
#[test]
fn remove_batch_tolerates_sibling_consumed_references() {
    let src = "package P {
    part def Wheel;
    metadata def Note { attribute body; }
    metadata n : Note about Wheel { body = \"x\"; }
}
";
    let mut s = session(src);
    let member = s.resolved().resolve_qualified("P::Wheel").unwrap();
    let record = s.resolved().resolve_qualified("P::n").unwrap();
    let mut edit = s.edit();
    // Record first, then member — the materializer's order.
    edit.remove(record);
    edit.remove(member);
    edit.commit().expect("one batch commits");
    let t = text(&s);
    assert!(!t.contains("Wheel"), "{t}");
    assert!(!t.contains("about"), "{t}");
    // Reverse order still refuses: the member's removal is planned
    // before the record's span is consumed.
    let mut s2 = session(src);
    let member = s2.resolved().resolve_qualified("P::Wheel").unwrap();
    let record = s2.resolved().resolve_qualified("P::n").unwrap();
    let mut edit = s2.edit();
    edit.remove(member);
    edit.remove(record);
    assert!(edit.commit().is_err(), "member-first still refuses");
}

/// An explicit replacement of an annotation record owns its `about`
/// spelling. A later replacement that renames the annotated member must
/// not add an overlapping automatic reference-respelling splice.
#[test]
fn replace_batch_tolerates_sibling_consumed_references() {
    let src = "package P {
    part def Alpha;
    metadata def Note { attribute body; }
    metadata n : Note about Alpha { body = \"old\"; }
}
";
    let mut s = session(src);
    let member = s.resolved().resolve_qualified("P::Alpha").unwrap();
    let record = s.resolved().resolve_qualified("P::n").unwrap();
    let mut edit = s.edit();
    // Record first, then member — the materializer's order.
    edit.replace_member(record, "metadata n : Note about Beta { body = \"new\"; }");
    edit.replace_member(member, "part def Beta;");
    edit.commit().expect("one batch commits");
    let t = text(&s);
    assert!(t.contains("part def Beta;"), "{t}");
    assert!(t.contains("about Beta"), "{t}");
    assert!(t.contains("body = \"new\""), "{t}");
}
