//! A session started from the outcomes a previous session settled on
//! answers as a session built cold does, after every kind of edit a host
//! makes between builds, and the outcomes outlive the session that
//! produced them.
use std::path::{Path, PathBuf};
use sysmlv2_wasm::{PreparedLibrary, Session, SettledOutcomes};

type Units = Vec<(String, String)>;

fn owned(units: &[(&str, &str)]) -> Units {
    units
        .iter()
        .map(|(name, text)| (name.to_string(), text.to_string()))
        .collect()
}

fn sources(units: &[(String, String)]) -> String {
    serde_json::to_string(
        &units
            .iter()
            .map(|(name, text)| serde_json::json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
    )
    .unwrap()
}

/// What a session answers: its compact and full interchange documents,
/// its findings, warnings, units and unresolved count.
fn answers(session: &mut Session) -> String {
    [
        session.to_compact_json(),
        session.to_full_json(true),
        session.check(),
        session.warnings(),
        session.units(),
        session.unresolved_count().to_string(),
    ]
    .join("\n")
}

/// The edits a host makes between builds, each over `units`: a comment
/// appended to a unit, a unit emptied, a declaration inserted at the top
/// of a unit (every reference after it shifts), a unit dropped, a unit
/// added, and the units in reverse order.
fn edits(units: &[(String, String)]) -> Vec<(String, Units)> {
    let mut out = Vec::new();
    for (i, (name, _)) in units.iter().enumerate() {
        let mut commented = units.to_vec();
        commented[i].1.push_str("\n// edited\n");
        out.push((format!("{name} commented"), commented));
        let mut emptied = units.to_vec();
        emptied[i].1 = "package Edited;".to_string();
        out.push((format!("{name} emptied"), emptied));
        let mut shifted = units.to_vec();
        let inserted = if name.ends_with(".kerml") {
            "package Inserted { class Fresh; }\n"
        } else {
            "package Inserted { part def Fresh; }\n"
        };
        shifted[i].1.insert_str(0, inserted);
        out.push((format!("{name} shifted"), shifted));
        let mut dropped = units.to_vec();
        dropped.remove(i);
        out.push((format!("{name} dropped"), dropped));
    }
    let mut added = units.to_vec();
    added.push((
        "added.sysml".to_string(),
        "package Added { part def Extra; part extra : Extra; }".to_string(),
    ));
    out.push(("a unit added".to_string(), added));
    let mut reversed = units.to_vec();
    reversed.reverse();
    out.push(("units reversed".to_string(), reversed));
    out
}

/// `units` with `from` respelled `to` in `unit`: a rename that unresolves
/// the references other units make to the renamed element.
fn renamed(units: &[(String, String)], unit: &str, from: &str, to: &str) -> (String, Units) {
    let mut renamed = units.to_vec();
    let (_, text) = renamed
        .iter_mut()
        .find(|(name, _)| name == unit)
        .expect("the renamed unit exists");
    assert!(text.contains(from), "{unit} spells {from}");
    *text = text.replace(from, to);
    (format!("{unit}: {from} renamed to {to}"), renamed)
}

/// A cold build on `library` keeps its outcomes; a build started from
/// them answers as the cold one over the same units and over every edit
/// in `edited_sets`, as does a build started from a seeded build's
/// outcomes, and a build of the original units started from an edited
/// build's.
fn seeded_answers_as_cold(
    library: &PreparedLibrary,
    units: &Units,
    edited_sets: Vec<(String, Units)>,
) {
    let mut cold = Session::from_sources_with_prepared_library(&sources(units), library).unwrap();
    let before = answers(&mut cold);
    let settled: SettledOutcomes = cold
        .settled_outcomes()
        .expect("a cold build on the prepared library settles");
    assert_eq!(settled.unit_count(), units.len());
    // the outcomes outlive the session that produced them
    drop(cold);
    let mut same = Session::from_sources_settled(&sources(units), library, &settled).unwrap();
    assert_eq!(answers(&mut same), before, "the same units again");
    let same_settled = same
        .settled_outcomes()
        .expect("a seeded build on the prepared library settles");
    assert_eq!(same_settled.unit_count(), units.len());

    for (label, edited) in edited_sets {
        let mut cold =
            Session::from_sources_with_prepared_library(&sources(&edited), library).unwrap();
        let expected = answers(&mut cold);
        // from the unedited build's outcomes
        let mut seeded =
            Session::from_sources_settled(&sources(&edited), library, &settled).unwrap();
        assert_eq!(answers(&mut seeded), expected, "{label}");
        // from a seeded build's own outcomes
        let mut chained =
            Session::from_sources_settled(&sources(&edited), library, &same_settled).unwrap();
        assert_eq!(answers(&mut chained), expected, "{label}, chained");
        // and back to the original units from the edited build's, when it kept any
        if let Some(edited_settled) = seeded.settled_outcomes() {
            let mut back =
                Session::from_sources_settled(&sources(units), library, &edited_settled).unwrap();
            assert_eq!(answers(&mut back), before, "{label}, back");
        }
    }
}

#[test]
fn a_seeded_session_answers_as_a_cold_one_on_a_small_library() {
    let library = PreparedLibrary::new(
        &sources(&owned(&[(
            "lib.kerml",
            "package L { class A { feature x; } class B :> A { feature :>> x; } alias C for B; }",
        )])),
        None,
    )
    .unwrap();
    let units = owned(&[
        (
            "u1.kerml",
            "package U { private import L::*; feature a : C; feature x chains a.x; }",
        ),
        (
            "u2.kerml",
            "package V { private import U::*; feature b :> a; feature y chains b.x; }",
        ),
        (
            "u3.sysml",
            "package W { private import V::*; part def P; part p : P { attribute z = y; } }",
        ),
    ]);
    let mut edited_sets = edits(&units);
    edited_sets.push(renamed(&units, "u1.kerml", "feature a :", "feature aa :"));
    seeded_answers_as_cold(&library, &units, edited_sets);
}

#[test]
fn outcomes_are_kept_only_by_a_build_on_a_prepared_library() {
    let library = sources(&owned(&[(
        "lib.kerml",
        "package L { class A { feature x; } class B :> A { feature :>> x; } }",
    )]));
    let units = sources(&owned(&[(
        "u.kerml",
        "package U { private import L::*; feature a : B; feature x chains a.x; }",
    )]));
    // no library: nothing to start a next build on
    assert!(
        Session::from_sources(&units)
            .unwrap()
            .settled_outcomes()
            .is_none()
    );
    // the library resolved together with the units: a joint build keeps none
    assert!(
        Session::from_sources_with_library(&units, Some(library.clone()), None)
            .unwrap()
            .settled_outcomes()
            .is_none()
    );
    let prepared = PreparedLibrary::new(&library, None).unwrap();
    let mut session = Session::from_sources_with_prepared_library(&units, &prepared).unwrap();
    let settled = session
        .settled_outcomes()
        .expect("kept on a prepared library");
    assert_eq!(settled.unit_count(), 1);
    // a rebuild keeps the latest build's outcomes
    session
        .edit(r#"[{"op":"rename","target":"U::a","newName":"b"}]"#)
        .unwrap();
    let after = session.settled_outcomes().expect("kept across an edit");
    assert_eq!(after.unit_count(), 1);
}

/// The units under `dir`, by path.
fn units_under(dir: &Path) -> Units {
    let mut files = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).unwrap().flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("sysml" | "kerml")
            ) {
                files.push(path);
            }
        }
    }
    files.sort();
    files
        .into_iter()
        .map(|p| {
            let name = p.strip_prefix(dir).unwrap().display().to_string();
            (name, std::fs::read_to_string(&p).unwrap())
        })
        .collect()
}

/// The standard library's directory: `SYSMLV2_LIBRARY`, as the package
/// build reads it, else the corpus checkout; `None` when neither exists.
fn standard_library_dir() -> Option<PathBuf> {
    let dir = match std::env::var_os("SYSMLV2_LIBRARY") {
        Some(dir) => PathBuf::from(dir),
        None => Path::new(env!("CARGO_MANIFEST_DIR"))
            .ancestors()
            .nth(2)
            .expect("crates/sysmlv2-wasm sits two levels below the root")
            .join("spec-refs/SysML-v2-Release/sysml.library"),
    };
    if dir.join("Kernel Libraries").is_dir() {
        Some(dir)
    } else {
        eprintln!("standard library not found at {}; skipping", dir.display());
        None
    }
}

#[test]
fn a_seeded_session_answers_as_a_cold_one_on_the_standard_library() {
    let Some(dir) = standard_library_dir() else {
        return;
    };
    let mut library = units_under(&dir);
    library.extend(sysmlv2_model::ambient::units());
    let library = PreparedLibrary::new(&sources(&library), None).unwrap();
    let units = owned(&[
        (
            "defs.sysml",
            "package VehicleDefs {
                private import ISQ::*;
                part def Vehicle { attribute mass : MassValue; part engine : Engine; part wheels : Wheel[4]; }
                part def Engine { attribute power : PowerValue; port fuelIn : FuelPort; }
                part def Wheel { attribute diameter : LengthValue; }
                port def FuelPort { in item fuel : Fuel; }
                item def Fuel;
                calc def KineticEnergy { in m : MassValue; in v : SpeedValue; return : EnergyValue = 0.5 * m * v ** 2; }
            }",
        ),
        (
            "usage.sysml",
            "package VehicleUsage {
                private import VehicleDefs::*;
                private import ISQ::*;
                private import SI::*;
                part car : Vehicle {
                    attribute :>> mass = 1500 [kg];
                    part :>> engine { attribute :>> power = 150000 [W]; }
                    part :>> wheels { attribute :>> diameter = 0.6 [m]; }
                }
                part tank { port fuelOut : ~FuelPort; }
                connect tank.fuelOut to car.engine.fuelIn;
                attribute ke : EnergyValue = KineticEnergy(car.mass, 30 [m/s]);
            }",
        ),
        (
            "views.sysml",
            "package VehicleViews {
                private import VehicleUsage::*;
                private import Views::*;
                view def PartTree;
                view carTree : PartTree { expose car::**; render asTreeDiagram; }
            }",
        ),
    ]);
    // a sample of the matrix: a build on the standard library costs seconds unoptimized
    let mut edited_sets: Vec<(String, Units)> = edits(&units)
        .into_iter()
        .filter(|(label, _)| {
            label == "usage.sysml commented"
                || label == "defs.sysml shifted"
                || label == "views.sysml dropped"
        })
        .collect();
    assert_eq!(edited_sets.len(), 3);
    edited_sets.push(renamed(&units, "usage.sysml", "part car :", "part truck :"));
    seeded_answers_as_cold(&library, &units, edited_sets);
}
