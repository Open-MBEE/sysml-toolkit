//! The reads a host makes of a session between its compact emissions —
//! checks, diagrams, verification, lint, navigation, and derived and
//! checked property reads of every element — leave the rows the session's
//! build made as they were, so the session goes on emitting off them: a
//! read that wrote one would cost every later emission a second build of
//! the model, and the memory that build takes.
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use sysmlv2_wasm::{Element, PreparedLibrary, Session};

fn sources(units: &[(String, String)]) -> String {
    serde_json::to_string(
        &units
            .iter()
            .map(|(name, text)| serde_json::json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
    )
    .unwrap()
}

fn owned(units: &[(&str, &str)]) -> Vec<(String, String)> {
    units
        .iter()
        .map(|(name, text)| (name.to_string(), text.to_string()))
        .collect()
}

/// The session's user elements, from its roots down through members.
fn user_elements(session: &mut Session) -> Vec<Element> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    let mut stack = session.roots();
    while let Some(e) = stack.pop() {
        if session.is_library_element(&e).unwrap() || !seen.insert(session.element_id(&e).unwrap())
        {
            continue;
        }
        stack.extend(session.members(&e).unwrap_or_default());
        out.push(e);
    }
    out
}

/// Every read a host makes of a session between emissions, results
/// ignored: a read may well refuse an element or a name.
fn read_everything(session: &mut Session) {
    let _ = session.check();
    for view in ["tree", "interconnection", "state", "action"] {
        let _ = session.to_graph(Some(format!(r#"{{"view":"{view}"}}"#)));
        let _ = session.to_plantuml(Some(format!(r#"{{"view":"{view}"}}"#)));
    }
    let _ = session.verify(None);
    let _ = session.lint(None);
    let _ = session.to_full_json(true, None).unwrap();
    let _ = session.to_full_json_strict();
    let _ = session.units();
    let _ = session.unresolved_count();
    let names = Session::computed_names();
    for policy in ["passthrough", "closure", "closure-implied"] {
        session.set_closure_policy(policy).unwrap();
        let elements = user_elements(session);
        assert!(elements.len() > 20, "the walk reaches the user elements");
        for e in elements {
            let qualified = session.qualified_name(&e).unwrap();
            let _ = session.metaclass(&e);
            let _ = session.owner(&e);
            let _ = session.features(&e);
            let _ = session.typings(&e);
            let _ = session.evaluate(&e);
            let _ = session.declaration_site(&e);
            let _ = session.value_source(&e);
            for name in &names {
                let _ = session.derived(&e, name);
                let _ = session.derived_elements(&e, name);
                let _ = session.property(&e, name);
            }
            if let Some(qualified) = qualified {
                let _ = session.query(&qualified);
                let _ = session.references(&qualified);
            }
        }
    }
    session.set_closure_policy("passthrough").unwrap();
}

/// The session's compact and elided CBOR are the whole compact array's
/// encodings, carrying its unit table; `names` names the elided targets.
fn assert_cbor_is_the_arrays(session: &Session, names: &HashMap<String, String>, what: &str) {
    let json: serde_json::Value = serde_json::from_str(&session.to_compact_json()).unwrap();
    let units: Vec<(usize, String)> = serde_json::from_str(&session.unit_table()).unwrap();
    assert_eq!(
        session.to_compact_cbor(),
        sysmlv2_cbor::to_compact_cbor_with_units(&json, &units).unwrap(),
        "{what}: compact CBOR"
    );
    assert_eq!(
        session.to_compact_cbor_elided().unwrap(),
        sysmlv2_cbor::to_compact_cbor_elided_with_units(
            &json,
            &|id| names.get(id).cloned(),
            &units
        )
        .unwrap(),
        "{what}: elided CBOR"
    );
}

/// The library's element names by id, as a build of the units over the
/// library's sources tables them.
fn library_names(
    library_units: &[(String, String)],
    units: &[(String, String)],
) -> HashMap<String, String> {
    let library =
        sysmlv2_transform::Library::prepared_sources(library_units.to_vec(), None).unwrap();
    let session =
        sysmlv2_transform::Session::from_sources_with_library(units.to_vec(), Some(library))
            .unwrap();
    sysmlv2_model::json::library_name_map(session.model())
        .into_iter()
        .filter_map(|(id, segments)| segments.last().cloned().map(|name| (id, name)))
        .collect()
}

/// After every read, the session emits off its build's rows, and emits
/// what a session that read nothing emits.
fn assert_reads_keep_the_built_rows(units: &[(String, String)], library: &PreparedLibrary) {
    let mut session =
        Session::from_sources_with_prepared_library(&sources(units), library).unwrap();
    assert!(
        session.emits_built_rows(),
        "a fresh session emits off its rows"
    );
    read_everything(&mut session);
    assert!(
        session.emits_built_rows(),
        "a read wrote a row the build made"
    );
    let untouched = Session::from_sources_with_prepared_library(&sources(units), library).unwrap();
    assert_eq!(session.to_compact_json(), untouched.to_compact_json());
    assert_eq!(session.state_digest(), untouched.state_digest());
}

#[test]
fn reads_keep_the_built_rows_on_a_small_library() {
    let library_units = owned(&[(
        "lib.sysml",
        "standard library package Lib { metadata def Mark; \
         part def Base { attribute mass; part wheel[4]; port p; } \
         port def P; }",
    )]);
    let library = PreparedLibrary::new(&sources(&library_units), None).unwrap();
    let units = owned(&[
        (
            "u.sysml",
            "package U { private import Lib::*; \
             part def Car :> Base { attribute :>> mass = 2; part :>> wheel; } \
             part car : Car { attribute :>> mass = 1; part a; part b; connect a to b; } \
             state def S { entry; then idle; state idle; state on; \
               transition first idle then on; } \
             action def Go { action a1; action a2; first a1 then a2; } \
             constraint def C { attribute x; x > 0 } \
             @Mark about Base; }",
        ),
        ("v.sysml", "package V { part truck : U::Car; }"),
    ]);
    assert_reads_keep_the_built_rows(&units, &library);
    let session = Session::from_sources_with_prepared_library(&sources(&units), &library).unwrap();
    assert!(session.emits_built_rows());
    assert_cbor_is_the_arrays(
        &session,
        &library_names(&library_units, &units),
        "on a small library",
    );
    let empty = Session::from_sources_with_prepared_library("[]", &library).unwrap();
    assert_cbor_is_the_arrays(&empty, &HashMap::new(), "no units");
}

fn units_under(dir: &Path) -> Vec<(String, String)> {
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
fn reads_keep_the_built_rows_on_the_standard_library() {
    let Some(dir) = standard_library_dir() else {
        return;
    };
    let mut library_units = units_under(&dir);
    library_units.extend(sysmlv2_model::ambient::units());
    let library = PreparedLibrary::new(&sources(&library_units), None).unwrap();
    let units = owned(&[
        (
            "craft.sysml",
            "package Craft {
                private import ScalarValues::*;
                private import ISQ::*;
                private import SI::*;
                port def CommandPort;
                part def Battery { attribute capacity : Real = 5200.0; attribute mass : MassValue = 0.24 [kg]; }
                part def Rotor { attribute mass : MassValue = 0.05 [kg]; }
                part def Controller { port cmd : CommandPort; }
                part def Esc { port input : ~CommandPort; }
                constraint def MassBudget { in total : MassValue; total <= 2 [kg] }
                part craft {
                    part battery : Battery;
                    part rotors : Rotor[4];
                    part fc : Controller;
                    part esc : Esc;
                    connect fc.cmd to esc.input;
                    attribute total : MassValue = battery.mass + 4 * rotors.mass;
                    constraint budget : MassBudget { in total = craft.total; }
                }
            }",
        ),
        (
            "mission.sysml",
            "package Mission {
                private import Craft::*;
                item def TakeoffCmd;
                item def LandCmd;
                part def Autopilot {
                    state def Modes {
                        entry; then idle;
                        state idle;
                        transition first idle accept TakeoffCmd then flying;
                        state flying;
                        transition first flying accept LandCmd then idle;
                    }
                    exhibit state modes : Modes;
                }
                action def Survey {
                    action takeoff; action scan; action land;
                    first takeoff then scan;
                    first scan then land;
                }
                part surveyCraft { part battery : Battery; part autopilot : Autopilot; }
            }",
        ),
    ]);
    assert_reads_keep_the_built_rows(&units, &library);
    let session = Session::from_sources_with_prepared_library(&sources(&units), &library).unwrap();
    assert!(session.emits_built_rows());
    let names = library_names(&library_units, &units);
    assert_cbor_is_the_arrays(&session, &names, "on the standard library");
    // The 28-unit model beside the standard library's checkout.
    let root = dir
        .parent()
        .and_then(Path::parent)
        .map(|refs| refs.join("apollo-11-sysml-v2"))
        .filter(|root| root.is_dir());
    if let Some(root) = root {
        let model = units_under(&root);
        let session =
            Session::from_sources_with_prepared_library(&sources(&model), &library).unwrap();
        assert!(session.emits_built_rows());
        assert_cbor_is_the_arrays(
            &session,
            &library_names(&library_units, &model),
            "a 28-unit model",
        );
    }
}
