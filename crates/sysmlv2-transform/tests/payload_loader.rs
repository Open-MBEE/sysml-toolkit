//! The id-preserving payload loader (plan §33c): a document loaded into
//! a session keeps the ids it carried — this toolkit's own, a foreign
//! producer's, or ids of elements the textual notation cannot name.

use serde_json::Value;
use std::collections::HashMap;
use std::fs;
use sysmlv2_model::model::Model;
use sysmlv2_transform::{Library, Session, SessionError};
use uuid::Uuid;

fn canon(v: &Value) -> String {
    serde_json::to_string(v).unwrap()
}

fn by_id(v: &Value) -> HashMap<String, &Value> {
    v.as_array()
        .unwrap()
        .iter()
        .map(|e| (e["@id"].as_str().unwrap().to_string(), e))
        .collect()
}

/// Every id in the payload replaced by a fresh one, consistently across
/// references — a document from another producer.
fn foreignize(v: &Value) -> (Value, HashMap<String, String>) {
    let mut map: HashMap<String, String> = HashMap::new();
    for e in v.as_array().unwrap() {
        let id = e["@id"].as_str().unwrap().to_string();
        let fresh = Uuid::new_v5(&Uuid::NAMESPACE_OID, format!("foreign:{id}").as_bytes());
        map.insert(id, fresh.to_string());
    }
    fn rewrite(v: &Value, map: &HashMap<String, String>) -> Value {
        match v {
            Value::Object(o) => Value::Object(
                o.iter()
                    .map(|(k, x)| {
                        let x = if (k == "@id" || k == "elementId") && x.is_string() {
                            map.get(x.as_str().unwrap())
                                .map(|s| Value::String(s.clone()))
                                .unwrap_or_else(|| x.clone())
                        } else {
                            rewrite(x, map)
                        };
                        (k.clone(), x)
                    })
                    .collect(),
            ),
            Value::Array(a) => Value::Array(a.iter().map(|x| rewrite(x, map)).collect()),
            other => other.clone(),
        }
    }
    (rewrite(v, &map), map)
}

#[test]
fn toolkit_payload_reloads_with_identical_ids_and_no_explicit_ids() {
    let src = "package P {
        part def V { attribute mass; part w[2]; }
        part v : V { attribute :>> mass = 3; }
        alias M for V;
    }";
    let s = Session::from_sources(vec![("p.sysml".into(), src.into())]).unwrap();
    let compact = s.to_compact_json();
    // Same unit name, so the derivation reproduces every id and no
    // explicit id is needed; without the name the root id (salted by the
    // unit name) would differ and the whole document would ride explicit.
    let loaded =
        Session::from_interchange_json_named(&compact, None, &["p.sysml".to_string()]).unwrap();
    assert!(!loaded.has_explicit_ids(), "our own ids derive exactly");
    let unnamed = Session::from_interchange_json(&compact).unwrap();
    assert!(unnamed.has_explicit_ids());
    assert_eq!(canon(&unnamed.to_compact_json()), canon(&compact));
    assert_eq!(canon(&loaded.to_compact_json()), canon(&compact));
    assert_eq!(
        canon(&loaded.to_full_json_with(false)),
        canon(&s.to_full_json_with(false))
    );
}

#[test]
fn foreign_ids_are_preserved_and_flagged() {
    let src = "package P {
        part def V { attribute mass; }
        part v : V;
        connection c connect v to v;
    }";
    let s = Session::from_sources(vec![("p.sysml".into(), src.into())]).unwrap();
    let (foreign, map) = foreignize(&s.to_compact_json());
    let loaded = Session::from_interchange_json(&foreign).unwrap();
    assert!(loaded.has_explicit_ids());
    assert!(
        loaded.warnings().is_empty(),
        "no unmatched elements: {:?}",
        loaded.warnings()
    );
    // Every element comes back under the id it was given, references
    // included.
    assert_eq!(canon(&loaded.to_compact_json()), canon(&foreign));
    // The full form spells the same ids.
    let full = loaded.to_full_json_with(false);
    let ids = by_id(&full);
    for given in map.values() {
        assert!(
            ids.contains_key(given),
            "{given} missing from the full form"
        );
    }
    // The read API sees them too.
    let mut loaded = loaded;
    let v_id = foreign
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["declaredName"] == "v")
        .map(|e| e["@id"].as_str().unwrap().to_string())
        .expect("v");
    let v = loaded
        .resolved()
        .element_by_id(&v_id)
        .expect("v is addressable by its given id");
    assert_eq!(loaded.resolved().element_name(v), Some("v"));
    // Binary: the compact payload is flagged; elision is refused.
    let bytes = loaded.to_compact_cbor();
    let desc = sysmlv2_cbor::describe(&bytes).unwrap();
    assert_eq!(desc["explicitIds"], true);
    assert!(matches!(
        loaded.to_compact_cbor_elided(),
        Err(SessionError::ExplicitIds)
    ));
    // The flagged payload decodes to the same ids.
    let back = Session::from_compact_cbor(&bytes).unwrap();
    assert_eq!(canon(&back.to_compact_json()), canon(&foreign));
}

#[test]
fn explicit_ids_survive_an_edit_elsewhere() {
    let src = "package P {
        part def V { attribute mass; }
        part v : V;
    }";
    let s = Session::from_sources(vec![("p.sysml".into(), src.into())]).unwrap();
    let (foreign, _) = foreignize(&s.to_compact_json());
    let mut loaded = Session::from_interchange_json(&foreign).unwrap();
    let before = loaded.to_compact_json();
    // Append a new member: existing ids stay given, the new one derives.
    let p = loaded.resolved().resolve_qualified("P").unwrap();
    let mut edit = loaded.edit();
    edit.insert_member(p, "part w;");
    edit.commit().unwrap();
    let after = loaded.to_compact_json();
    let before_ids = by_id(&before);
    let after_ids = by_id(&after);
    for (id, el) in &before_ids {
        let kept = after_ids
            .get(id)
            .expect("given id survives an unrelated edit");
        assert_eq!(kept["@type"], el["@type"]);
    }
    assert!(loaded.has_explicit_ids());
    assert!(
        after_ids.values().any(|e| e["declaredName"] == "w"),
        "the new member is present"
    );
}

#[test]
fn a_deleted_element_does_not_bequeath_its_given_id() {
    let src = "package P {
        part def V { attribute mass; }
        part v : V;
    }";
    let s = Session::from_sources(vec![("p.sysml".into(), src.into())]).unwrap();
    let (foreign, _) = foreignize(&s.to_compact_json());
    let mut loaded = Session::from_interchange_json(&foreign).unwrap();
    let v_given = foreign
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["declaredName"] == "v")
        .map(|e| e["@id"].as_str().unwrap().to_string())
        .unwrap();
    // Delete v: its entry retires with it.
    let v = loaded.resolved().resolve_qualified("P::v").unwrap();
    let mut edit = loaded.edit();
    edit.remove(v);
    edit.commit().unwrap();
    assert!(!by_id(&loaded.to_compact_json()).contains_key(&v_given));
    // Recreate a `part v` in the same place: it derives the same key as
    // the deleted one, and must not inherit the deleted element's id.
    let p = loaded.resolved().resolve_qualified("P").unwrap();
    let mut edit = loaded.edit();
    edit.insert_member(p, "part v : V;");
    edit.commit().unwrap();
    let after = loaded.to_compact_json();
    let new_v = after
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["declaredName"] == "v")
        .map(|e| e["@id"].as_str().unwrap().to_string())
        .unwrap();
    assert_ne!(new_v, v_given, "a fresh element is not the deleted one");
    // The remaining entries (P, V, mass, their memberships, the root) are
    // still explicit.
    assert!(loaded.has_explicit_ids());
}

#[test]
fn reordered_relationships_never_swap_ids_across_metaclasses() {
    // A producer may list a feature's value before its typing; the lift
    // prints a fixed order, so positional pairing alone would cross the
    // two ids. Pairing is only trusted within a metaclass.
    let src = "package P {
        part def V;
        part v : V = null;
    }";
    let s = Session::from_sources(vec![("p.sysml".into(), src.into())]).unwrap();
    let (mut foreign, _) = foreignize(&s.to_compact_json());
    let v_index = foreign
        .as_array()
        .unwrap()
        .iter()
        .position(|e| e["declaredName"] == "v")
        .unwrap();
    let rels = foreign[v_index]["ownedRelationship"]
        .as_array()
        .unwrap()
        .clone();
    assert_eq!(rels.len(), 2, "typing and value");
    foreign[v_index]["ownedRelationship"] = Value::Array(rels.iter().rev().cloned().collect());
    let loaded = Session::from_interchange_json(&foreign).unwrap();
    let ids = by_id(&foreign);
    let emitted = loaded.to_compact_json();
    let out = by_id(&emitted);
    for (id, el) in &ids {
        if let Some(x) = out.get(id) {
            assert_eq!(x["@type"], el["@type"], "id {id} changed metaclass");
        }
    }
    assert!(
        loaded
            .warnings()
            .iter()
            .any(|w| w.contains("no structural counterpart")),
        "the two reordered relationships are reported, not swapped: {:?}",
        loaded.warnings()
    );
}

#[test]
fn a_document_in_another_element_order_still_preserves_its_ids() {
    let src = "package P {
        part def V { attribute mass; }
        part v : V;
    }";
    let s = Session::from_sources(vec![("p.sysml".into(), src.into())]).unwrap();
    let (foreign, _) = foreignize(&s.to_compact_json());
    let reversed = Value::Array(foreign.as_array().unwrap().iter().rev().cloned().collect());
    let loaded = Session::from_interchange_json(&reversed).unwrap();
    assert!(loaded.has_explicit_ids());
    assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
    let emitted = loaded.to_compact_json();
    let out = by_id(&emitted);
    for (id, el) in by_id(&foreign) {
        assert_eq!(out.get(&id).map(|x| canon(x)), Some(canon(el)), "{id}");
    }
}

#[test]
fn library_references_stay_ids_without_a_library() {
    // A library-typed payload converted without a library: the lift can
    // only spell the library id, and the emitted forms keep it as the id
    // (no dangling substitute, no recovery annotation).
    let root = sysmlv2_testkit::workspace_root().join("spec-refs/SysML-v2-Release");
    if !root.join("sysml.library").exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let s = Session::from_sources(vec![(
        "p.sysml".into(),
        "package P { part def V { attribute mass : ScalarValues::Real; } }".into(),
    )])
    .unwrap()
    .with_library(&root.join("sysml.library"))
    .unwrap();
    let compact = s.to_compact_json();
    let lib_type = compact
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["@type"] == "FeatureTyping")
        .map(|e| e["type"]["@id"].as_str().unwrap().to_string())
        .expect("the typing references a library id");
    let loaded = Session::from_interchange_json(&compact).unwrap();
    let typing_of = |v: &Value| -> Value {
        v.as_array()
            .unwrap()
            .iter()
            .find(|e| e["@type"] == "FeatureTyping")
            .map(|e| e["type"].clone())
            .unwrap()
    };
    assert_eq!(typing_of(&loaded.to_compact_json())["@id"], lib_type);
    let full = loaded.to_full_json_with(true);
    assert_eq!(typing_of(&full)["@id"], lib_type);
    assert!(
        !full
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "TextualRepresentation"),
        "no recovery annotation for an id-spelled reference"
    );
}

#[test]
fn references_to_unnamed_elements_are_bound_by_id() {
    // API-GAPS issue 13: a legal payload may reference an element with
    // no name; the text cannot spell it, but the loaded model must keep
    // the link.
    let src = "package P {
        part a; part b;
        connection c connect a to b;
    }";
    let s = Session::from_sources(vec![("p.sysml".into(), src.into())]).unwrap();
    let mut compact = s.to_compact_json();
    let mut stripped = 0;
    for e in compact.as_array_mut().unwrap() {
        let name = e["declaredName"].as_str().map(str::to_string);
        if matches!(name.as_deref(), Some("a") | Some("b")) {
            e.as_object_mut().unwrap().remove("declaredName");
            stripped += 1;
        }
    }
    assert_eq!(stripped, 2);
    let loaded = Session::from_interchange_json(&compact).unwrap();
    let out = loaded.to_compact_json();
    let text = canon(&out);
    assert!(
        !text.contains("@ref"),
        "no reference degrades to a spelling: {text}"
    );
    // The connector's ends still target the two unnamed parts.
    let ids = by_id(&compact);
    let unnamed: Vec<&str> = ids
        .iter()
        .filter(|(_, e)| e["@type"] == "PartUsage" && e.get("declaredName").is_none())
        .map(|(id, _)| id.as_str())
        .collect();
    assert_eq!(unnamed.len(), 2);
    let out_ids = by_id(&out);
    for id in &unnamed {
        assert!(out_ids.contains_key(*id), "unnamed part keeps its id");
    }
    let referenced: Vec<&str> = out
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["@type"] == "ReferenceSubsetting")
        .filter_map(|e| e["referencedFeature"]["@id"].as_str())
        .collect();
    for id in &unnamed {
        assert!(
            referenced.contains(id),
            "connector end references the unnamed part {id}: {referenced:?}"
        );
    }
    assert!(
        loaded
            .warnings()
            .iter()
            .all(|w| !w.contains("cannot name reference target")),
        "{:?}",
        loaded.warnings()
    );
}

/// The whole standard corpus loaded from its compact payload reproduces
/// the text route's compact and full forms element by element.
///
/// Excluded: files whose top-level package name is also declared by
/// another corpus file. The lift spells cross-scope references rooted at
/// the model root (`$::Name::…`), which is unambiguous within one
/// document but not in a model that holds two documents declaring the
/// same top-level name (API-GAPS issue 15); the text route resolves
/// those references lexically.
#[test]
fn corpus_payload_route_matches_the_text_route() {
    // A whole-corpus session rebuild needs more stack than a test thread
    // has, as the other corpus-scale session tests in this crate do.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(corpus_payload_route_body)
        .unwrap()
        .join()
        .unwrap();
}

fn corpus_payload_route_body() {
    let root = sysmlv2_testkit::workspace_root().join("spec-refs/SysML-v2-Release");
    if !root.join("sysml.library").exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let files = sysmlv2_testkit::user_files();
    if files.is_empty() {
        eprintln!("skipping: corpus model files not present");
        return;
    }
    // Top-level member names per file, read from the resolved model, to
    // drop the files whose top-level names another file declares too.
    let mut probe = Model::new();
    let mut probe_names = Vec::new();
    for path in &files {
        let src = fs::read_to_string(path).unwrap();
        let name = path
            .strip_prefix(&root)
            .unwrap_or(path)
            .to_string_lossy()
            .into_owned();
        probe.add_source(name.clone(), &src);
        probe_names.push(name);
    }
    let (probe_compact, probe_units) =
        sysmlv2_model::json::model_to_compact_json_with_units(&probe);
    let mut resolved = sysmlv2_model::json::ResolvedModel::build(&probe);
    let mut per_file: Vec<(std::path::PathBuf, Vec<String>)> = Vec::new();
    let mut declared: HashMap<String, usize> = HashMap::new();
    for (i, (root_index, unit)) in probe_units.iter().enumerate() {
        let root_id = probe_compact[*root_index]["@id"].as_str().unwrap();
        let root_el = resolved.element_by_id(root_id).expect("unit root");
        let names: Vec<String> = resolved
            .owned_members(root_el)
            .into_iter()
            .filter_map(|m| resolved.element_name(m).map(str::to_string))
            .collect();
        for n in &names {
            *declared.entry(n.clone()).or_default() += 1;
        }
        assert_eq!(&probe_names[i], unit);
        per_file.push((files[i].clone(), names));
    }
    let excluded: Vec<&std::path::PathBuf> = per_file
        .iter()
        .filter(|(_, names)| names.iter().any(|n| declared[n] > 1))
        .map(|(p, _)| p)
        .collect();
    assert_eq!(
        excluded.len(),
        8,
        "four top-level names are each declared by two corpus files: {excluded:?}"
    );
    let files: Vec<std::path::PathBuf> = files
        .iter()
        .filter(|p| !excluded.contains(p))
        .cloned()
        .collect();
    let lib = Library::dir(root.join("sysml.library"));
    let mut model = Model::new();
    model
        .load_library_dir(&root.join("sysml.library"))
        .expect("library loads");
    let mut names = Vec::new();
    for path in &files {
        let src = fs::read_to_string(path).unwrap();
        let name = path
            .strip_prefix(&root)
            .unwrap_or(path)
            .to_string_lossy()
            .into_owned();
        model.add_source(name.clone(), &src);
        names.push(name);
    }
    let compact = sysmlv2_model::json::model_to_compact_json(&model);
    let direct_full = sysmlv2_model::full::model_to_full_json_with(&model, false);
    let loaded = Session::from_interchange_json_named(&compact, Some(&lib), &names).unwrap();
    assert!(
        !loaded.has_explicit_ids(),
        "a toolkit payload loaded under its unit names derives every id"
    );
    assert!(
        loaded.warnings().is_empty(),
        "{} warnings, first: {:?}",
        loaded.warnings().len(),
        loaded.warnings().first()
    );
    let reloaded = loaded.to_compact_json();
    let (a, b) = (by_id(&compact), by_id(&reloaded));
    assert_eq!(a.len(), b.len(), "element count");
    // API-GAPS issue 16: one reference to a library return parameter is
    // spelled by the parameter's effective name and does not re-resolve.
    const KNOWN_UNRESOLVED: &str = "$::Requirements::RequirementConstraintCheck::result";
    let mut known = 0usize;
    let mut known_ids: Vec<String> = Vec::new();
    let mut differing = 0usize;
    let mut example = String::new();
    for (id, el) in &a {
        match b.get(id) {
            Some(x) if canon(x) == canon(el) => {}
            Some(x) if x["memberElement"]["@ref"] == KNOWN_UNRESOLVED => {
                known += 1;
                known_ids.push(id.clone());
            }
            other => {
                differing += 1;
                if example.is_empty() {
                    example = format!("{id}: {} vs {:?}", canon(el), other.map(|x| canon(x)));
                }
            }
        }
    }
    assert_eq!(known, 1, "exactly one known unresolvable spelling");
    assert_eq!(
        differing, 0,
        "compact round trip through the loader; e.g. {example}"
    );
    // And the full form emitted from the loaded session equals the
    // text route's, element by element.
    let loaded_full = loaded.to_full_json_with(false);
    let (a, b) = (by_id(&direct_full), by_id(&loaded_full));
    assert_eq!(a.len(), b.len(), "full-form element count");
    // The known unresolvable reference becomes a deterministic dangling
    // id in the full form; skip it and every element that carries that
    // id in a derived property.
    let dangling: Vec<String> = known_ids
        .iter()
        .filter_map(|id| b.get(id.as_str()))
        .filter_map(|x| x["memberElement"]["@id"].as_str().map(str::to_string))
        .collect();
    let mut differing = 0usize;
    for (id, el) in &a {
        if b.get(id).map(|x| canon(x)) != Some(canon(el)) {
            let text = canon(b[id]);
            if known_ids.contains(id) || dangling.iter().any(|d| text.contains(d)) {
                continue;
            }
            differing += 1;
            if differing == 1 {
                eprintln!("first full-form difference at {id}: {}", canon(b[id]));
            }
        }
    }
    assert_eq!(differing, 0, "full form through the loader");
}

#[test]
fn long_expressions_keep_their_value_through_json_and_cbor_sessions() {
    sysmlv2_syntax::parser::on_parsing_stack(
        "session-expression-roundtrip",
        |e| panic!("cannot reserve parsing stack: {e}"),
        || {
            let operators = sysmlv2_syntax::parser::MAX_EXPR_OPERATORS as usize;
            let source = format!("attribute sum = {};", vec!["1"; operators + 1].join(" + "));
            let session = Session::from_sources(vec![("sum.sysml".into(), source)]).unwrap();
            let compact = session.to_compact_json();
            let full = session.to_full_json();
            let bytes = session.to_compact_cbor();
            let binary = Session::from_compact_cbor(&bytes).unwrap();
            assert_eq!(binary.to_compact_json(), compact);
            for payload in [&compact, &full] {
                let loaded = Session::from_interchange_json(payload).unwrap();
                assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
                assert_eq!(loaded.to_compact_json(), compact);
            }

            // Add one operator below the deepest leaf: the valid input is
            // now just beyond the expression budget. Neither JSON nor
            // binary session loading may return the shorter sum.
            let mut too_deep = compact;
            let elements = too_deep.as_array_mut().unwrap();
            let leaf = elements
                .iter_mut()
                .find(|e| e["@type"] == "LiteralInteger")
                .unwrap();
            let leaf_id = leaf["@id"].clone();
            leaf["@type"] = "OperatorExpression".into();
            leaf["operator"] = "+".into();
            leaf.as_object_mut().unwrap().remove("value");
            let id = |s: &str| Uuid::new_v5(&Uuid::NAMESPACE_OID, s.as_bytes()).to_string();
            let rels = [id("extra-left-rel"), id("extra-right-rel")];
            leaf["ownedRelationship"] = serde_json::json!([{"@id": rels[0]}, {"@id": rels[1]}]);
            for (i, rel) in rels.iter().enumerate() {
                let value = id(&format!("extra-value-{i}"));
                elements.push(serde_json::json!({"@id": rel, "@type": "ParameterMembership",
                    "owningRelatedElement": {"@id": leaf_id}, "ownedRelatedElement": [{"@id": value}]}));
                elements.push(serde_json::json!({"@id": value, "@type": "LiteralInteger",
                    "owningRelationship": {"@id": rel}, "value": 1}));
            }
            let error = match Session::from_interchange_json(&too_deep) {
                Ok(_) => panic!("a truncated expression must not become a session"),
                Err(e) => e.to_string(),
            };
            assert!(error.contains("expression nesting deeper than"), "{error}");
            let bytes = sysmlv2_cbor::to_compact_cbor(&too_deep).unwrap();
            assert!(Session::from_compact_cbor(&bytes).is_err());
        },
    );
}
