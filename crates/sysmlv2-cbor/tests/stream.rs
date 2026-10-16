//! The snapshot encodings of a payload's elements taken in turn — each
//! read once, its record written and transcoded — are byte for byte the
//! whole array's: compact CBOR with and without a unit structure and the
//! id-elided form, over the golden corpus, a payload
//! referring outside itself, payloads whose backpointers stray from their
//! derivation, a payload of foreign ids, the empty payload and a 28-unit
//! model over the standard library. They refuse what the whole array's
//! refuse, and ids spelled otherwise than canonically.

use serde_json::{Value, json};
use std::collections::HashMap;
use sysmlv2_cbor::{ElementRecords, to_compact_cbor_elided_with_units, to_compact_cbor_with_units};
use sysmlv2_parser::json::{
    ResolvedModel, library_name_map, model_to_compact_json, model_to_compact_json_with_units,
};
use sysmlv2_parser::model::Model;

/// The payload's elements, each cloned out of it in turn.
fn records(payload: &Value) -> Result<ElementRecords, sysmlv2_cbor::Error> {
    let elements = payload.as_array().unwrap();
    ElementRecords::read(elements.len(), |i| elements[i].clone())
}

/// The streamed encodings equal the whole array's, with `units` and
/// with none, `names` naming the elided targets.
fn assert_streams_as_whole(
    payload: &Value,
    units: &[(usize, String)],
    names: &dyn Fn(&str) -> Option<String>,
    what: &str,
) {
    let records = records(payload).unwrap_or_else(|e| panic!("{what}: {e}"));
    for units in [units, &[]] {
        assert_eq!(
            records.to_compact_cbor(units).unwrap(),
            to_compact_cbor_with_units(payload, units).unwrap(),
            "{what}: compact CBOR with {} units",
            units.len()
        );
        assert_eq!(
            records.to_compact_cbor_elided(names, units).unwrap(),
            to_compact_cbor_elided_with_units(payload, names, units).unwrap(),
            "{what}: elided CBOR with {} units",
            units.len()
        );
    }
}

fn no_external(s: &str) -> Option<String> {
    panic!("unexpected external target {s}")
}

fn goldens() -> Vec<(String, Value)> {
    let dir = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../sysmlv2-parser/tests/goldens/expected");
    let mut out = Vec::new();
    for entry in std::fs::read_dir(dir).expect("goldens/expected exists") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("json") {
            continue;
        }
        let v = serde_json::from_str(&std::fs::read_to_string(&path).unwrap()).unwrap();
        out.push((path.file_name().unwrap().to_string_lossy().into_owned(), v));
    }
    assert!(out.len() >= 150, "corpus present");
    out
}

const UNIT: &str = "package P { part def A { attribute m; part w[2]; } \
     part def B :> A { attribute :>> m = 1; part :>> w; } part b : B; \
     action def Go { action a1; action a2; first a1 then a2; } }";

fn compact_of(units: &[(&str, &str)]) -> Value {
    let mut model = Model::new();
    for (name, text) in units {
        model.add_source((*name).to_owned(), text);
    }
    model_to_compact_json(&model)
}

/// Every string in `value` that `spellings` respells, respelled.
fn respell(value: &mut Value, spellings: &HashMap<String, String>) {
    match value {
        Value::String(s) => {
            if let Some(respelled) = spellings.get(s.as_str()) {
                s.clone_from(respelled);
            }
        }
        Value::Array(items) => items.iter_mut().for_each(|v| respell(v, spellings)),
        Value::Object(entries) => entries.values_mut().for_each(|v| respell(v, spellings)),
        _ => {}
    }
}

#[test]
fn the_encodings_of_the_elements_in_turn_are_the_whole_arrays() {
    let mut payloads = goldens();
    // With its last element gone, a model refers outside itself.
    let mut partial = compact_of(&[("m.sysml", UNIT)]);
    partial.as_array_mut().unwrap().pop();
    payloads.push(("a model missing an element".into(), partial));
    payloads.push(("the empty model".into(), Value::Array(Vec::new())));
    // Ids of another producer: none of them derives, so each rides the
    // exception map.
    let mut foreign = compact_of(&[("m.sysml", UNIT)]);
    let given: HashMap<String, String> = foreign
        .as_array()
        .unwrap()
        .iter()
        .map(|element| {
            let id = element["@id"].as_str().unwrap();
            let given = uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, id.as_bytes());
            (id.to_owned(), given.to_string())
        })
        .collect();
    respell(&mut foreign, &given);
    payloads.push(("foreign ids".into(), foreign));
    let two = compact_of(&[
        ("m.sysml", UNIT),
        ("n.sysml", "package Q { part q : P::B; }"),
    ]);
    payloads.push(("two units".into(), two));
    for (name, payload) in payloads {
        let n = payload.as_array().unwrap().len();
        let units: Vec<(usize, String)> = if n == 0 {
            Vec::new()
        } else {
            vec![(0, "a.sysml".to_owned()), (n - 1, "z.sysml".to_owned())]
                .into_iter()
                .take(if n > 1 { 2 } else { 1 })
                .collect()
        };
        let mut reversed = payload.clone();
        reversed.as_array_mut().unwrap().reverse();
        assert_streams_as_whole(&payload, &units, &|_| None, &name);
        assert_streams_as_whole(&reversed, &units, &|_| None, &format!("{name}, reversed"));
    }
}

/// Backpointers that do not spell their derivation are spelled on the
/// wire, absent keys ride the owner-exception section, and a record's
/// backpointers are left out only where they match.
#[test]
fn the_encodings_of_backpointers_that_stray_from_their_derivation_are_the_whole_arrays() {
    let payload = compact_of(&[("m.sysml", UNIT)]);
    let elements = payload.as_array().unwrap();
    let n = elements.len();
    assert!(n > 6);
    // An owned element (not a root) with each backpointer spelled
    // otherwise, and a relationship with its owner's key gone.
    let owned_at = (0..n)
        .find(|&i| elements[i]["owningRelationship"].is_object())
        .unwrap();
    let other = elements[(owned_at + 3) % n]["@id"].clone();
    let strays: Vec<(&str, Value)> = vec![
        ("null where an owner derives", Value::Null),
        (
            "another element where an owner derives",
            json!({ "@id": other }),
        ),
        ("a symbolic owner", json!({ "@ref": "Elsewhere::x" })),
        ("an owner spelled in capitals", {
            let id = elements[owned_at]["owningRelationship"]["@id"]
                .as_str()
                .unwrap()
                .to_uppercase();
            json!({ "@id": id })
        }),
    ];
    for (what, value) in strays {
        let mut strayed = payload.clone();
        strayed[owned_at]["owningRelationship"] = value;
        assert_streams_as_whole(&strayed, &[(0, "m.sysml".into())], &no_external, what);
    }
    let mut absent = payload.clone();
    for element in absent.as_array_mut().unwrap().iter_mut().skip(1).step_by(2) {
        element
            .as_object_mut()
            .unwrap()
            .remove("owningRelationship");
        element
            .as_object_mut()
            .unwrap()
            .remove("owningRelatedElement");
    }
    assert_streams_as_whole(
        &absent,
        &[(0, "m.sysml".into())],
        &no_external,
        "absent keys",
    );
    // A root given an owner that is not one of its elements.
    let mut root_owned = payload.clone();
    root_owned[0]["owningRelationship"] =
        json!({ "@id": uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, b"elsewhere").to_string() });
    assert_streams_as_whole(&root_owned, &[], &no_external, "a root owned elsewhere");
}

#[test]
fn the_encodings_of_the_elements_in_turn_refuse_what_the_whole_arrays_do_and_ids_spelled_otherwise()
{
    let model = compact_of(&[("m.sysml", UNIT)]);
    let mut unknown = model.clone();
    unknown[0]["@type"] = "NoSuchMetaclass".into();
    assert!(to_compact_cbor_with_units(&unknown, &[]).is_err());
    assert!(records(&unknown).is_err(), "an unknown metaclass");
    let mut twice = model.clone();
    let first = twice[0].clone();
    twice.as_array_mut().unwrap().push(first);
    assert!(to_compact_cbor_with_units(&twice, &[]).is_err());
    assert!(records(&twice).is_err(), "an element twice");
    let mut stray_key = model.clone();
    stray_key[1]["noSuchProperty"] = json!(1);
    assert!(to_compact_cbor_with_units(&stray_key, &[]).is_err());
    assert!(records(&stray_key).is_err(), "a key outside the tables");
    let id = model[0]["@id"].as_str().unwrap().to_owned();
    let capitals =
        serde_json::from_str::<Value>(&model.to_string().replace(&id, &id.to_uppercase())).unwrap();
    assert!(to_compact_cbor_with_units(&capitals, &[]).is_ok());
    assert!(records(&capitals).is_err(), "an id in capitals");
    // A unit table the whole array's encoder refuses is refused too.
    let records = records(&model).unwrap();
    for units in [
        vec![(model.as_array().unwrap().len(), "far.sysml".to_owned())],
        vec![(1, "b.sysml".to_owned()), (0, "a.sysml".to_owned())],
        vec![(0, String::new())],
    ] {
        assert!(to_compact_cbor_with_units(&model, &units).is_err());
        assert!(records.to_compact_cbor(&units).is_err(), "{units:?}");
        assert!(
            records
                .to_compact_cbor_elided(&no_external, &units)
                .is_err(),
            "{units:?}"
        );
    }
}

/// An unnamed performance names itself after the last feature of the
/// chain it references, a library action here, so the derivation asks the
/// library for that feature's name: streamed and whole agree whether the
/// library answers or not.
#[test]
fn the_encodings_of_a_performance_of_a_library_action_through_a_chain_are_the_whole_arrays() {
    let mut model = Model::new();
    model.add_library_source(
        "lib.sysml",
        "standard library package Lib { part def Base { action go; action stop; } }",
    );
    model.add_source(
        "u.sysml".to_owned(),
        "package U { private import Lib::*; part p : Base; \
         part r { perform p.go; perform p.stop; perform p.go; } }",
    );
    let (compact, units) = model_to_compact_json_with_units(&model);
    // The action itself, resolved: its membership carries the same
    // qualified name, so the name table alone cannot tell the two apart.
    let go = {
        let mut resolved = ResolvedModel::build(&model);
        let action = resolved
            .resolve_qualified("Lib::Base::go")
            .expect("the library action resolves");
        resolved.element_id(action).to_string()
    };
    let names: HashMap<String, String> = library_name_map(&model)
        .into_iter()
        .filter_map(|(id, segs)| segs.last().cloned().map(|n| (id.to_string(), n)))
        .collect();
    let chains = compact
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["@type"] == "FeatureChaining" && e["chainingFeature"]["@id"] == go)
        .count();
    assert_eq!(chains, 2, "two chains end in the library action");
    let asked = std::cell::RefCell::new(Vec::new());
    let naming = |s: &str| {
        asked.borrow_mut().push(s.to_owned());
        names.get(s).cloned()
    };
    assert_streams_as_whole(&compact, &units, &naming, "a performance, named");
    assert!(
        asked.borrow().contains(&go),
        "the library action is asked for its name"
    );
    let silent = |s: &str| {
        asked.borrow_mut().push(s.to_owned());
        None
    };
    asked.borrow_mut().clear();
    assert_streams_as_whole(&compact, &units, &silent, "a performance, unnamed");
    assert!(asked.borrow().contains(&go));
    // The library's answer moves the performances' ids: named, they derive
    // and ride no exception; unnamed, they are positional and still derive.
    let records = records(&compact).unwrap();
    assert_ne!(
        records.to_compact_cbor_elided(&naming, &units).unwrap(),
        records.to_compact_cbor_elided(&silent, &units).unwrap()
    );
}

#[test]
fn the_encodings_of_a_model_over_the_standard_library_in_turn_are_the_whole_arrays() {
    let Some(files) = sysmlv2_testkit::apollo_files() else {
        eprintln!("the 28-unit model is not checked out; skipping it");
        return;
    };
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for f in &files {
        let src = std::fs::read_to_string(f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let (compact, units) = model_to_compact_json_with_units(&model);
    let names: HashMap<String, String> = library_name_map(&model)
        .into_iter()
        .filter_map(|(id, segs)| segs.last().cloned().map(|n| (id.to_string(), n)))
        .collect();
    assert_eq!(units.len(), files.len());
    let records = records(&compact).unwrap();
    // Only the library's elements are referenced outside the payload,
    // and the elision asks about those alone.
    assert!(!records.externals().is_empty());
    assert!(
        records
            .externals()
            .iter()
            .all(|u| names.contains_key(&u.to_string()))
    );
    let asked = std::cell::RefCell::new(Vec::new());
    let resolver = |s: &str| {
        asked.borrow_mut().push(s.to_owned());
        names.get(s).cloned()
    };
    assert_streams_as_whole(&compact, &units, &resolver, "a 28-unit model");
    let externals: std::collections::HashSet<String> = records
        .externals()
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(!asked.borrow().is_empty());
    assert!(asked.borrow().iter().all(|s| externals.contains(s)));
}
