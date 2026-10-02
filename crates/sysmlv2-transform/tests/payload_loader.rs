//! The id-preserving payload loader: a document loaded into
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
    // A legal payload may reference an element with
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
/// same top-level name; the text route resolves
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
    let mut differing = 0usize;
    let mut example = String::new();
    for (id, el) in &a {
        match b.get(id) {
            Some(x) if canon(x) == canon(el) => {}
            other => {
                differing += 1;
                if example.is_empty() {
                    example = format!("{id}: {} vs {:?}", canon(el), other.map(|x| canon(x)));
                }
            }
        }
    }
    assert_eq!(
        differing, 0,
        "compact round trip through the loader; e.g. {example}"
    );
    // And the full form emitted from the loaded session equals the
    // text route's, element by element.
    let loaded_full = loaded.to_full_json_with(false);
    let (a, b) = (by_id(&direct_full), by_id(&loaded_full));
    assert_eq!(a.len(), b.len(), "full-form element count");
    let mut differing = 0usize;
    for (id, el) in &a {
        if b.get(id).map(|x| canon(x)) != Some(canon(el)) {
            differing += 1;
            if differing == 1 {
                eprintln!("first full-form difference at {id}: {:?}", b.get(id));
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

#[test]
fn unnamed_type_references_restore_semantic_queries_and_survive_rebuild() {
    let source = "package P {
        part def Base { attribute mass = 7; }
        part def Child :> Base;
        part p : Base[1];
        attribute result = p.mass;
    }";
    let original = Session::from_sources(vec![("p.sysml".into(), source.into())]).unwrap();
    let (mut document, _) = foreignize(&original.to_compact_json());
    let base = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "Base")
        .unwrap();
    let base_id = base["@id"].as_str().unwrap().to_owned();
    base.as_object_mut().unwrap().remove("declaredName");
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    for iteration in 0..2 {
        let model = loaded.resolved();
        let base = model.element_by_id(&base_id).unwrap();
        let child = model.resolve_qualified("P::Child").unwrap();
        let p = model.resolve_qualified("P::p").unwrap();
        assert_eq!(model.typings(p), vec![base]);
        assert!(model.conforms(p, base));
        assert!(model.conforms(child, base));
        let mass = model.resolve_qualified("P::p::mass").unwrap();
        assert_eq!(model.resolve_qualified("P::Child::mass"), Some(mass));
        assert!(model.inherited_features(p, false).contains(&mass));
        assert!(matches!(
            model.evaluate_qualified("P::result"),
            Ok(sysmlv2_model::eval::Value::Integer(7))
        ));
        let sites = model.references_to(base);
        assert_eq!(sites.iter().filter(|s| s.kind == "type").count(), 1);
        assert_eq!(
            sites.iter().filter(|s| s.kind == "superclassifier").count(),
            1
        );
        assert!(
            sites.iter().all(|s| !s.plain),
            "identity references must not be respelled as names"
        );
        assert_eq!(model.unresolved_count(), 0);
        assert!(
            model.bind_id_spelled_references().is_empty(),
            "binding is idempotent"
        );
        if iteration == 0 {
            let p = loaded.resolved().resolve_qualified("P").unwrap();
            let mut edit = loaded.edit();
            edit.insert_member(p, "part unrelated;");
            edit.commit().unwrap();
        }
    }
}

#[test]
fn unresolved_external_type_keeps_identity_without_invented_semantics() {
    let source = "package P { part def Base; part p : Base; }";
    let original = Session::from_sources(vec![("p.sysml".into(), source.into())]).unwrap();
    let mut document = original.to_compact_json();
    let external = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"external-type").to_string();
    for element in document.as_array_mut().unwrap() {
        if element["@type"] == "FeatureTyping" {
            element["type"]["@id"] = Value::String(external.clone());
        }
    }
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    let model = loaded.resolved();
    let p = model.resolve_qualified("P::p").unwrap();
    assert!(model.typings(p).is_empty());
    assert!(model.element_by_id(&external).is_none());
    assert_eq!(
        model.unresolved_count(),
        0,
        "known external identities are not unresolved names"
    );
    assert!(
        loaded
            .warnings()
            .iter()
            .any(|w| w.contains("outside the document"))
    );
    let output = loaded.to_compact_json();
    let typing = output
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["@type"] == "FeatureTyping")
        .unwrap();
    assert_eq!(typing["type"]["@id"], external);
}

#[test]
fn uuid_spelling_in_text_remains_a_lexical_name() {
    let name = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"ordinary-name").to_string();
    let source = format!("package P {{ part def '{name}'; part p : '{name}'; }}");
    let mut session = Session::from_sources(vec![("p.sysml".into(), source)]).unwrap();
    let model = session.resolved();
    let p = model.resolve_qualified("P::p").unwrap();
    let typ = model.resolve_qualified(&format!("P::'{name}'")).unwrap();
    assert_eq!(model.typings(p), vec![typ]);
    assert_ne!(model.element_id(typ).to_string(), name);
}

#[test]
fn unnamed_redefinition_targets_restore_shadowing_and_default_evaluation() {
    let source = "package P {
        part def Base { attribute mass default = 7; }
        part def Child :> Base { attribute weight :>> mass; }
    }";
    let original = Session::from_sources(vec![("p.sysml".into(), source.into())]).unwrap();
    let (mut document, _) = foreignize(&original.to_compact_json());
    let mass = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "mass")
        .unwrap();
    let mass_id = mass["@id"].as_str().unwrap().to_owned();
    mass.as_object_mut().unwrap().remove("declaredName");
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    let model = loaded.resolved();
    let mass = model.element_by_id(&mass_id).unwrap();
    let child = model.resolve_qualified("P::Child").unwrap();
    let weight = model.resolve_qualified("P::Child::weight").unwrap();
    assert!(
        model
            .explicit_specializations(weight)
            .contains(&("Redefinition", mass))
    );
    assert_eq!(model.redefiners(mass), vec![weight]);
    assert!(!model.inherited_features(child, false).contains(&mass));
    assert!(matches!(
        model.evaluate_qualified("P::Child::weight"),
        Ok(sysmlv2_model::eval::Value::Integer(7))
    ));
    let site = model
        .references_to(mass)
        .into_iter()
        .find(|s| s.kind == "redefinedFeature")
        .unwrap();
    assert!(!site.plain);
    let before = loaded.to_compact_json();
    let warnings = loaded.warnings().to_vec();
    let p = loaded.resolved().resolve_qualified("P").unwrap();
    let mut edit = loaded.edit();
    edit.insert_member(p, "part unrelated;");
    edit.check().unwrap();
    assert_eq!(loaded.to_compact_json(), before);
    assert_eq!(loaded.warnings(), warnings);
    // Qualification minimization rebuilds and verifies the semantic graph too.
    loaded.minimize_qualifications().unwrap();
    let model = loaded.resolved();
    let mass = model.element_by_id(&mass_id).unwrap();
    let weight = model.resolve_qualified("P::Child::weight").unwrap();
    assert_eq!(model.redefiners(mass), vec![weight]);
}

#[test]
fn unnamed_namespace_import_replays_dependents_without_duplicating_reference_arrays() {
    let source = "package Q {
        attribute a = 3;
        attribute b = 4;
        dependency D from a, b to a, b;
    }
    package P { public import Q::*; attribute total = a + b; }";
    let original = Session::from_sources(vec![("p.sysml".into(), source.into())]).unwrap();
    let (mut document, _) = foreignize(&original.to_compact_json());
    let namespace = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "Q")
        .unwrap();
    namespace.as_object_mut().unwrap().remove("declaredName");
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    let model = loaded.resolved();
    assert!(model.resolve_qualified("P::a").is_some());
    assert!(matches!(
        model.evaluate_qualified("P::total"),
        Ok(sysmlv2_model::eval::Value::Integer(7))
    ));
    assert_eq!(model.unresolved_count(), 0);
    let output = loaded.to_compact_json();
    let dependency = output
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["@type"] == "Dependency")
        .unwrap();
    assert_eq!(dependency["client"].as_array().unwrap().len(), 2);
    assert_eq!(dependency["supplier"].as_array().unwrap().len(), 2);
}

#[test]
fn loaded_identity_spelling_does_not_capture_a_distinct_uuid_named_type() {
    let target_id = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"anonymous-type").to_string();
    let source = format!(
        "package P {{
        part def Anonymous;
        part def '{target_id}';
        part anonymous : Anonymous;
        part named : '{target_id}';
    }}"
    );
    let original = Session::from_sources(vec![("p.sysml".into(), source)]).unwrap();
    let mut document = original.to_compact_json();
    let target = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "Anonymous")
        .unwrap();
    let old_id = target["@id"].as_str().unwrap().to_owned();
    target.as_object_mut().unwrap().remove("declaredName");
    // Substitute the anonymous type's identity consistently in the payload.
    fn replace(value: &mut Value, old: &str, new: &str) {
        match value {
            Value::String(s) if s == old => *s = new.to_owned(),
            Value::Array(a) => a.iter_mut().for_each(|v| replace(v, old, new)),
            Value::Object(o) => o.values_mut().for_each(|v| replace(v, old, new)),
            _ => {}
        }
    }
    replace(&mut document, &old_id, &target_id);
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    for iteration in 0..2 {
        let model = loaded.resolved();
        let anonymous = model.resolve_qualified("P::anonymous").unwrap();
        let named = model.resolve_qualified("P::named").unwrap();
        let target = model.element_by_id(&target_id).unwrap();
        let lexical = model
            .resolve_qualified(&format!("P::'{target_id}'"))
            .unwrap();
        assert_ne!(target, lexical);
        assert_eq!(model.typings(anonymous), vec![target]);
        assert_eq!(model.typings(named), vec![lexical]);
        if iteration == 0 {
            let p = loaded.resolved().resolve_qualified("P").unwrap();
            let mut edit = loaded.edit();
            edit.insert_member(p, "part unrelated;");
            edit.commit().unwrap();
        }
    }
}

#[test]
fn later_document_root_scope_restores_anonymous_typing() {
    let original = Session::from_sources(vec![
        ("one.sysml".into(), "part initialPart;".into()),
        ("two.sysml".into(), "part def Base; part p : Base;".into()),
    ])
    .unwrap();
    let mut document = original.to_compact_json();
    let base = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "Base")
        .unwrap();
    let id = base["@id"].as_str().unwrap().to_owned();
    base.as_object_mut().unwrap().remove("declaredName");
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    let model = loaded.resolved();
    let base = model.element_by_id(&id).unwrap();
    let p = model.resolve_qualified("p").unwrap();
    assert_eq!(model.typings(p), vec![base]);
    assert!(model.conforms(p, base));
}

#[test]
fn inherited_default_with_anonymous_reference_preserves_its_identity() {
    let original = Session::from_sources(vec![("p.sysml".into(),
        "package P { attribute original = 7; part def Base { attribute value default = original; } part def Child :> Base { attribute result :>> value; } }".into())]).unwrap();
    let mut document = original.to_compact_json();
    let original = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "original")
        .unwrap();
    original.as_object_mut().unwrap().remove("declaredName");
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    assert!(matches!(
        loaded.resolved().evaluate_qualified("P::Child::result"),
        Ok(sysmlv2_model::eval::Value::Integer(7))
    ));
}

#[test]
fn equal_spans_in_distinct_documents_do_not_confuse_identity_and_lexical_references() {
    let target_id = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"anonymous-type").to_string();
    let original = Session::from_sources(vec![
        ("one.sysml".into(), "part aLong : Anonymous;".into()),
        ("two.sysml".into(), format!("part ab : '{target_id}';")),
        (
            "defs.sysml".into(),
            format!("part def Anonymous; part def '{target_id}';"),
        ),
    ])
    .unwrap();
    let mut document = original.to_compact_json();
    let target = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "Anonymous")
        .unwrap();
    let old = target["@id"].as_str().unwrap().to_owned();
    target.as_object_mut().unwrap().remove("declaredName");
    let mut document = serde_json::from_str::<Value>(
        &serde_json::to_string(&document)
            .unwrap()
            .replace(&old, &target_id),
    )
    .unwrap();
    // Ensure no declared name or target spelling is normalized away.
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    let model = loaded.resolved();
    let target = model.element_by_id(&target_id).unwrap();
    let lexical = model.resolve_qualified(&format!("'{target_id}'")).unwrap();
    let a = model.resolve_qualified("aLong").unwrap();
    let b = model.resolve_qualified("ab").unwrap();
    assert_eq!(model.typings(a), vec![target]);
    assert_eq!(model.typings(b), vec![lexical]);
    let identity_site = model
        .references_to(target)
        .into_iter()
        .find(|s| s.kind == "type")
        .unwrap();
    let lexical_site = model
        .references_to(lexical)
        .into_iter()
        .find(|s| s.kind == "type")
        .unwrap();
    assert_eq!(identity_site.name_span, lexical_site.name_span);
    assert_ne!(identity_site.unit, lexical_site.unit);
    document.as_array_mut().unwrap().reverse();
    let mut reordered = Session::from_interchange_json(&document).unwrap();
    let model = reordered.resolved();
    let a = model.resolve_qualified("aLong").unwrap();
    let target = model.element_by_id(&target_id).unwrap();
    assert_eq!(model.typings(a), vec![target]);
}

#[test]
fn cross_document_alias_keeps_its_anonymous_target_provenance() {
    let original = Session::from_sources(vec![
        ("defs.sysml".into(), "package Defs { part def Base { attribute mass = 7; } alias Alias for Base; }".into()),
        ("uses.sysml".into(), "package Uses { part p : Defs::Alias[1]; attribute total = p.mass; public import Defs::Alias; part q : Alias; }".into()),
    ]).unwrap();
    let mut document = original.to_compact_json();
    let base = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "Base")
        .unwrap();
    let base_id = base["@id"].as_str().unwrap().to_owned();
    base.as_object_mut().unwrap().remove("declaredName");
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    let model = loaded.resolved();
    let base = model.element_by_id(&base_id).unwrap();
    assert_eq!(model.resolve_qualified("Defs::Alias"), Some(base));
    let p = model.resolve_qualified("Uses::p").unwrap();
    let q = model.resolve_qualified("Uses::q").unwrap();
    assert_eq!(model.typings(p), vec![base]);
    assert_eq!(model.typings(q), vec![base]);
    assert!(
        matches!(
            model.evaluate_qualified("Uses::total"),
            Ok(sysmlv2_model::eval::Value::Integer(7))
        ),
        "{:?}",
        model.evaluate_qualified("Uses::total")
    );
}

#[test]
fn uuid_shaped_unresolved_names_keep_legacy_identity_recovery() {
    let original = Session::from_sources(vec![(
        "p.sysml".into(),
        "package P { part def Base; part p : Base; part lexical : Missing; }".into(),
    )])
    .unwrap();
    let mut document = original.to_compact_json();
    let base = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "Base")
        .unwrap();
    base.as_object_mut().unwrap().remove("declaredName");
    let spelling = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"unresolved-name").to_string();
    for element in document.as_array_mut().unwrap() {
        if element["@type"] == "FeatureTyping" && element["type"].get("@ref").is_some() {
            element["type"] = serde_json::json!({"@ref":format!("'{spelling}'")});
        }
    }
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    let model = loaded.resolved();
    assert_eq!(model.unresolved_count(), 0);
    let lexical = model.resolve_qualified("P::lexical").unwrap();
    let typing = model
        .owned_relationships(lexical)
        .into_iter()
        .find(|e| model.element_type(*e) == "FeatureTyping")
        .unwrap();
    assert_eq!(model.element_properties(typing)["type"]["@id"], spelling);
    assert!(model.typings(lexical).is_empty());
}

#[test]
fn identity_resolution_follows_explicit_id_overrides_after_loading() {
    let original = Session::from_sources(vec![(
        "p.sysml".into(),
        "package P { attribute original = 7; attribute answer = original; }".into(),
    )])
    .unwrap();
    let mut document = original.to_compact_json();
    let target = document
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["declaredName"] == "original")
        .unwrap();
    let old = Uuid::parse_str(target["@id"].as_str().unwrap()).unwrap();
    target.as_object_mut().unwrap().remove("declaredName");
    let mut loaded = Session::from_interchange_json(&document).unwrap();
    let model = loaded.resolved();
    let new = Uuid::new_v5(&Uuid::NAMESPACE_OID, b"replacement-identity");
    model.override_ids(&HashMap::from([(old, new)]));
    assert!(model.element_by_id(&old.to_string()).is_none());
    assert!(model.element_by_id(&new.to_string()).is_some());
    assert!(matches!(
        model.evaluate_qualified("P::answer"),
        Ok(sysmlv2_model::eval::Value::Integer(7))
    ));
}
#[test]
fn sysml_generated_binding_full_json_and_cbor_preserve_source_and_foreign_ids() {
    let source = Session::from_sources(vec![(
        "reference.sysml".into(),
        "part def Container { attribute n; attribute x=n; }".into(),
    )])
    .unwrap();
    let original = source.to_compact_json();
    for foreign in [false, true] {
        // Foreignize only authored compact rows: generated identities should
        // be derived from their preserved owners, not imported as source IDs.
        let compact = if foreign {
            foreignize(&original).0
        } else {
            original.clone()
        };
        let session =
            Session::from_interchange_json_named(&compact, None, &["reference.sysml".into()])
                .unwrap();
        assert!(session.warnings().is_empty(), "{:?}", session.warnings());
        assert_eq!(by_id(&session.to_compact_json()), by_id(&compact));
        let full = session.to_full_json_with(false);
        assert!(
            full.as_array()
                .unwrap()
                .iter()
                .any(|row| { row["@type"] == "BindingConnector" && row["isImplied"] == true })
        );
        let binary = session.to_full_cbor(false);
        let decoded = session.decode_cbor(&binary).unwrap();
        assert_eq!(by_id(&decoded), by_id(&full));
        for payload in [&full, &decoded] {
            let lifted = sysmlv2_model::lift::from_compact_json(payload).unwrap();
            assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
            assert_eq!(lifted.unit.dialect, sysmlv2_syntax::ast::Dialect::Sysml);
            let loaded =
                Session::from_interchange_json_named(payload, None, &["reference.sysml".into()])
                    .unwrap();
            assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
            assert_eq!(by_id(&loaded.to_compact_json()), by_id(&compact));
            assert_eq!(by_id(&loaded.to_full_json_with(false)), by_id(&full));
        }
    }
}
