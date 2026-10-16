//! A session emits its compact forms — the element array and unit
//! structure, compact CBOR, id-elided CBOR and the state digest — off the
//! rows its own build made, and they are byte for byte what a fresh build
//! of its model emits: on a prepared library and without one, cold and
//! started from settled outcomes, and after the session has been checked
//! and exported in full. Decoding names elided targets through the same
//! tables, read off the session's rows too. Where the rows are read one
//! element at a time, the JSON text, the compact and elided CBOR and the
//! digest are what the whole array writes.

use std::collections::HashMap;
use std::path::{Path, PathBuf};
use sysmlv2_model::json::{library_name_map, model_to_compact_json_with_units};
use sysmlv2_model::model::GraphFormat;
use sysmlv2_transform::{Library, Session};

/// The compact forms of a session.
#[derive(Debug, PartialEq)]
struct Emitted {
    json: serde_json::Value,
    units: Vec<(usize, String)>,
    cbor: Vec<u8>,
    elided: Vec<u8>,
    digest: uuid::Uuid,
}

/// The session's compact forms as it emits them.
fn emitted(session: &Session) -> Emitted {
    Emitted {
        json: session.to_compact_json(),
        units: session.unit_structure(),
        cbor: session.to_compact_cbor(),
        elided: session.to_compact_cbor_elided().unwrap(),
        digest: session.state_digest(),
    }
}

/// The library name table a fresh build of the session's model makes, by
/// last segment.
fn rebuilt_names(session: &Session) -> HashMap<String, String> {
    library_name_map(session.model())
        .into_iter()
        .filter_map(|(id, segments)| segments.last().cloned().map(|name| (id, name)))
        .collect()
}

/// The compact forms a fresh build of the session's model emits, encoded
/// as the session encodes them (no explicit ids, the stock graph format),
/// with the whole library name table naming the elided targets.
fn rebuilt(session: &Session) -> Emitted {
    let (json, units) = model_to_compact_json_with_units(session.model());
    let names = rebuilt_names(session);
    Emitted {
        cbor: sysmlv2_cbor::to_compact_cbor_with_units(&json, &units).unwrap(),
        elided: sysmlv2_cbor::to_compact_cbor_elided_with_units(
            &json,
            &|id| names.get(id).cloned(),
            &units,
        )
        .unwrap(),
        digest: sysmlv2_cbor::state_digest(&json).unwrap(),
        json,
        units,
    }
}

/// The session emits what a fresh build emits, read off its own rows.
fn assert_emits_as_rebuilt(session: &mut Session, what: &str) {
    assert!(
        session
            .resolved_ref()
            .built_compact_json_with_units()
            .is_some(),
        "{what}: the build's rows are read"
    );
    let expected = rebuilt(session);
    assert_eq!(emitted(session), expected, "{what}");
    let names = rebuilt_names(session);
    assert_eq!(
        session.decode_cbor(&expected.elided).unwrap(),
        sysmlv2_cbor::from_cbor_with(&expected.elided, &|id| names.get(id).cloned()).unwrap(),
        "{what}: decoded"
    );
    // and still after the session has been checked and exported in full
    let _ = session.check_findings();
    let _ = session.to_full_json();
    assert!(
        session
            .resolved_ref()
            .built_compact_json_with_units()
            .is_some(),
        "{what}: the build's rows are read after a check"
    );
    assert_eq!(emitted(session), expected, "{what}, checked");
}

/// The session's elided delta from `base`, as a fresh build of its model
/// encodes it with the whole library name table.
fn assert_elided_delta_as_rebuilt(session: &Session, base: &serde_json::Value, what: &str) {
    let (target, units) = model_to_compact_json_with_units(session.model());
    let names = rebuilt_names(session);
    let expected = sysmlv2_cbor::delta_compact_cbor_elided(
        base,
        &target,
        &sysmlv2_cbor::DeltaOptions::new()
            .with_graph_format(GraphFormat::LegacyV2)
            .with_units(units),
        &|id| names.get(id).cloned(),
    )
    .unwrap();
    assert_eq!(
        session.delta_cbor_elided_from(base).unwrap(),
        expected,
        "{what}: elided delta"
    );
}

/// The session's compact JSON text, compact and elided CBOR and state
/// digest are what its whole compact array writes, encodes and digests.
/// Where `streams`, the array is its build's rows read one element at a
/// time, and the digest of those elements taken in turn is the whole
/// array's: the session writes, encodes and digests them so; otherwise it
/// takes the whole array.
fn assert_streams_as_whole(session: &Session, streams: bool, what: &str) {
    let whole = session.to_compact_json();
    let digest = sysmlv2_cbor::state_digest(&whole).unwrap();
    assert_eq!(
        session.to_compact_json_string(),
        whole.to_string(),
        "{what}: JSON text"
    );
    assert_eq!(session.state_digest(), digest, "{what}: digest");
    let units = session.unit_structure();
    let format = session.model().graph_format();
    let cbor = match (format, session.has_explicit_ids()) {
        (GraphFormat::CanonicalV3, true) => {
            sysmlv2_cbor::to_compact_cbor_explicit_with_format(&whole, &units, format)
        }
        (GraphFormat::CanonicalV3, false) => {
            sysmlv2_cbor::to_compact_cbor_with_format(&whole, &units, format)
        }
        (_, true) => sysmlv2_cbor::to_compact_cbor_with_units_explicit(&whole, &units),
        (_, false) => sysmlv2_cbor::to_compact_cbor_with_units(&whole, &units),
    }
    .unwrap();
    assert_eq!(session.to_compact_cbor(), cbor, "{what}: compact CBOR");
    if session.has_explicit_ids() {
        assert!(session.to_compact_cbor_elided().is_err(), "{what}: elided");
    } else {
        let names = rebuilt_names(session);
        let resolver = |id: &str| names.get(id).cloned();
        let elided = if format == GraphFormat::CanonicalV3 {
            sysmlv2_cbor::to_compact_cbor_elided_with_format(&whole, &resolver, &units, format)
        } else {
            sysmlv2_cbor::to_compact_cbor_elided_with_units(&whole, &resolver, &units)
        }
        .unwrap();
        assert_eq!(
            session.to_compact_cbor_elided().unwrap(),
            elided,
            "{what}: elided CBOR"
        );
    }
    assert_eq!(
        session.streams_compact_rows(),
        streams,
        "{what}: read one element at a time"
    );
    if streams {
        let rows = session.resolved_ref().built_compact_rows().unwrap();
        assert_eq!(
            serde_json::Value::Array(rows.elements().collect()),
            whole,
            "{what}: elements"
        );
        assert_eq!(
            sysmlv2_cbor::state_digest_streamed(rows.len(), |i| rows.element(i)).unwrap(),
            digest,
            "{what}: digest of the elements in turn"
        );
    }
}

const LIBRARY: &str = "standard library package Lib { metadata def Mark; \
     part def Base { attribute mass; part wheel[4]; } }";
const USER: &str = "package U { private import Lib::*; \
     part def Car :> Base { attribute :>> mass; part :>> wheel; } \
     part car : Car { attribute :>> mass = 1; } \
     @Mark about Base; }";
const OTHER: &str = "package V { part truck : U::Car { attribute :>> mass = 2; } }";

fn units() -> Vec<(String, String)> {
    vec![
        ("u.sysml".to_owned(), USER.to_owned()),
        ("v.sysml".to_owned(), OTHER.to_owned()),
    ]
}

#[test]
fn a_session_emits_its_compact_forms_as_a_fresh_build_does() {
    let library =
        Library::prepared_sources(vec![("lib.sysml".into(), LIBRARY.into())], None).unwrap();
    let mut cold = Session::from_sources_with_library(units(), Some(library.clone())).unwrap();
    assert_emits_as_rebuilt(&mut cold, "on the prepared library");
    let settled = cold.settled_outcomes();
    let mut edited = units();
    edited[1].1 = "package V { part truck : U::Car; part van : U::Car; }".into();
    let mut seeded = Session::from_sources_settled(edited, Some(library.clone()), settled).unwrap();
    assert_emits_as_rebuilt(&mut seeded, "started from settled outcomes");
    assert_elided_delta_as_rebuilt(&seeded, &cold.to_compact_json(), "edited");
    let mut sources = vec![("lib.sysml".to_owned(), LIBRARY.to_owned())];
    sources.extend(units());
    let mut alone = Session::from_sources(sources).unwrap();
    assert_emits_as_rebuilt(&mut alone, "without a library");
}

/// Every string in `value` that `spellings` respells, respelled.
fn respell(value: &mut serde_json::Value, spellings: &HashMap<String, String>) {
    match value {
        serde_json::Value::String(s) => {
            if let Some(respelled) = spellings.get(s.as_str()) {
                s.clone_from(respelled);
            }
        }
        serde_json::Value::Array(items) => items.iter_mut().for_each(|v| respell(v, spellings)),
        serde_json::Value::Object(entries) => {
            entries.values_mut().for_each(|v| respell(v, spellings));
        }
        _ => {}
    }
}

#[test]
fn a_session_writes_and_digests_its_compact_array_one_element_at_a_time() {
    let library =
        Library::prepared_sources(vec![("lib.sysml".into(), LIBRARY.into())], None).unwrap();
    let session = Session::from_sources_with_library(units(), Some(library.clone())).unwrap();
    assert_streams_as_whole(&session, true, "on the prepared library");
    let mut sources = vec![("lib.sysml".to_owned(), LIBRARY.to_owned())];
    sources.extend(units());
    let alone = Session::from_sources(sources).unwrap();
    assert_streams_as_whole(&alone, true, "without a library");
    let empty = Session::from_sources(vec![("empty.sysml".into(), String::new())]).unwrap();
    assert_streams_as_whole(&empty, true, "an empty unit");
    let none = Session::from_sources(Vec::new()).unwrap();
    assert_eq!(none.to_compact_json_string(), "[]");
    assert_eq!(none.state_digest(), sysmlv2_cbor::empty_base_digest());
    assert_streams_as_whole(&none, true, "no units");
    // Sessions opened from the compact forms: one decoded with its ids the
    // derivation's keeps its build's rows; a lift under other unit names
    // keeps the document's ids, and a load on a library rewrites rows.
    let decoded = Session::from_compact_cbor_with(&alone.to_compact_cbor(), None).unwrap();
    assert_streams_as_whole(&decoded, true, "decoded from compact CBOR");
    let lifted = Session::from_interchange_json_with(&alone.to_compact_json(), None).unwrap();
    assert!(lifted.has_explicit_ids());
    assert_streams_as_whole(&lifted, false, "lifted from compact JSON");
    let decoded =
        Session::from_compact_cbor_with(&session.to_compact_cbor(), Some(&library)).unwrap();
    assert_streams_as_whole(&decoded, false, "decoded from compact CBOR on the library");
    // A session over a document whose ids are not the derivation's keeps
    // them, overlaying them on the whole array.
    let mut document = session.to_compact_json();
    let foreign: HashMap<String, String> = document
        .as_array()
        .unwrap()
        .iter()
        .map(|element| {
            let id = element["@id"].as_str().unwrap();
            let given = uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, id.as_bytes());
            (id.to_owned(), given.to_string())
        })
        .collect();
    respell(&mut document, &foreign);
    let explicit = Session::from_interchange_json_with(&document, Some(&library)).unwrap();
    assert!(explicit.has_explicit_ids());
    assert_streams_as_whole(&explicit, false, "explicit ids");
    // The canonical graph format completes rows as it emits them.
    let library = Library::prepared_sources_with_format(
        vec![("lib.sysml".into(), LIBRARY.into())],
        None,
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    let canonical =
        Session::from_sources_with_graph_format(units(), Some(library), GraphFormat::CanonicalV3)
            .unwrap();
    assert_streams_as_whole(&canonical, false, "the canonical graph format");
}

#[test]
fn a_session_whose_emission_completes_rows_emits_as_a_fresh_build_does() {
    let library = Library::prepared_sources_with_format(
        vec![("lib.sysml".into(), LIBRARY.into())],
        None,
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    let session =
        Session::from_sources_with_graph_format(units(), Some(library), GraphFormat::CanonicalV3)
            .unwrap();
    assert!(!session.resolved_ref().emits_built_rows());
    let (json, units) = model_to_compact_json_with_units(session.model());
    let names = rebuilt_names(&session);
    assert_eq!(session.to_compact_json(), json);
    assert_eq!(session.unit_structure(), units);
    assert_eq!(
        session.to_compact_cbor_elided().unwrap(),
        sysmlv2_cbor::to_compact_cbor_elided_with_format(
            &json,
            &|id| names.get(id).cloned(),
            &units,
            GraphFormat::CanonicalV3,
        )
        .unwrap()
    );
}

/// Two types specializing members of each other found through aliases
/// that point across a pair of nested types: a reference cycle, which the
/// checks report, edited by dropping one of `A`'s bases.
const CYCLE: &str = "package P {
  part def M {
    part def Y { alias Z for M::Z; }
    part def Z { alias Y for M::Y; }
  }
  part def B :> A::Z;
  part def A :> B::Y, M::Y;
}
";
const CYCLE_EDITED: &str = "package P {
  part def M {
    part def Y { alias Z for M::Z; }
    part def Z { alias Y for M::Y; }
  }
  part def B :> A::Z;
  part def A :> B::Y;
}
";

/// A session over the cycle, started from the outcomes a session over its
/// unedited text settled on, emits what a cold session emits. (On the
/// standard library: a build on a small one resolves the cycle in one pass
/// and keeps no outcomes to start from.)
fn assert_cycle_seeded_emits_as_cold(library: &Library) {
    let unit = |text: &str| vec![("u.sysml".to_owned(), text.to_owned())];
    let previous = Session::from_sources_with_library(unit(CYCLE), Some(library.clone())).unwrap();
    let settled = previous
        .settled_outcomes()
        .expect("the build on the prepared library settles");
    let mut seeded =
        Session::from_sources_settled(unit(CYCLE_EDITED), Some(library.clone()), Some(settled))
            .unwrap();
    let mut cold =
        Session::from_sources_with_library(unit(CYCLE_EDITED), Some(library.clone())).unwrap();
    assert_emits_as_rebuilt(&mut seeded, "the cycle, seeded");
    assert_emits_as_rebuilt(&mut cold, "the cycle, cold");
    assert_eq!(
        emitted(&seeded),
        emitted(&cold),
        "the cycle, seeded and cold"
    );
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

#[test]
fn a_session_on_the_standard_library_emits_as_a_fresh_build_does() {
    let root = sysmlv2_testkit::workspace_root().join("spec-refs/SysML-v2-Release");
    let example: PathBuf = root.join("sysml/src/examples/Vehicle Example");
    if !example.exists() {
        eprintln!("corpus not initialized; skipping");
        return;
    }
    let mut library = units_under(&root.join("sysml.library"));
    library.extend(sysmlv2_model::ambient::units());
    let library = Library::prepared_sources(library, None).unwrap();
    let units = units_under(&example);
    let mut cold =
        Session::from_sources_with_library(units.clone(), Some(library.clone())).unwrap();
    assert_streams_as_whole(&cold, true, "the Vehicle example");
    assert_emits_as_rebuilt(&mut cold, "the Vehicle example");
    match sysmlv2_testkit::apollo_files() {
        Some(files) => {
            let root = sysmlv2_testkit::workspace_root().join("spec-refs/apollo-11-sysml-v2");
            let units = files
                .iter()
                .map(|f| {
                    let name = f.strip_prefix(&root).unwrap().display().to_string();
                    (name, std::fs::read_to_string(f).unwrap())
                })
                .collect();
            let session = Session::from_sources_with_library(units, Some(library.clone())).unwrap();
            assert_streams_as_whole(&session, true, "a 28-unit model");
        }
        None => eprintln!("the 28-unit model is not checked out; skipping it"),
    }
    let mut edited = units;
    edited[0].1.push_str("\n// edited\n");
    let mut seeded =
        Session::from_sources_settled(edited, Some(library.clone()), cold.settled_outcomes())
            .unwrap();
    assert_emits_as_rebuilt(&mut seeded, "the Vehicle example, edited and seeded");
    assert_elided_delta_as_rebuilt(&seeded, &cold.to_compact_json(), "the Vehicle example");
    assert_cycle_seeded_emits_as_cold(&library);
}
