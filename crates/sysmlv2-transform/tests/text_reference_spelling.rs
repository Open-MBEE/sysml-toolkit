//! Textual UUID-shaped names retain lexical meaning through interchange.
use serde_json::{Value, json};
use std::collections::HashMap;
use sysmlv2_model::{json::ResolvedModel, model::Model};
use sysmlv2_transform::{Library, Session};

const LIBRARY: &str = "standard library package Lib { feature visible; }";
const MISSING: &str = "88888888-8888-4888-8888-888888888888";

fn library() -> Library {
    Library::sources(vec![("lib.kerml".into(), LIBRARY.into())])
}

fn library_target_id() -> String {
    let mut model = Model::new();
    model.add_library_source("lib.kerml", LIBRARY);
    let mut resolved = ResolvedModel::build(&model);
    let target = resolved.resolve_qualified("Lib::visible").unwrap();
    resolved.element_id(target).to_string()
}

fn rows(value: &Value) -> HashMap<String, Value> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|row| (row["@id"].as_str().unwrap().to_owned(), row.clone()))
        .collect()
}

fn load(value: &Value, lib: Option<&Library>) -> Session {
    Session::from_interchange_json_named(value, lib, &["u.kerml".into()]).unwrap()
}

fn text(source: String, lib: Option<Library>) -> Session {
    Session::from_sources_with_library(vec![("u.kerml".into(), source)], lib).unwrap()
}

#[test]
fn text_uuid_name_stays_unresolved_before_and_after_loading_its_namesake_identity() {
    let id = library_target_id();
    let spelling = format!("'{id}'");
    let mut session = text(format!("package P {{ feature value = {spelling}; }}"), None);
    let compact = session.to_compact_json();
    assert_eq!(session.resolved().unresolved_count(), 1);
    let full = session.to_full_json();
    assert!(full.as_array().unwrap().iter().any(|e| {
        e["language"] == sysmlv2_model::full::UNRESOLVED_REP_LANGUAGE && e["body"] == spelling
    }));
    let dangling = sysmlv2_model::json::dangling_id(&spelling);
    assert!(
        full.as_array()
            .unwrap()
            .iter()
            .any(|e| { e["@type"] == "Membership" && e["memberElement"]["@id"] == dangling })
    );
    assert_ne!(dangling, id);
    let mut recovered = load(&full, None);
    assert!(
        recovered.warnings().is_empty(),
        "{:?}",
        recovered.warnings()
    );
    assert_eq!(recovered.resolved().unresolved_count(), 1);
    assert_eq!(rows(&compact), rows(&recovered.to_compact_json()));
    recovered.load_library_from(library()).unwrap();
    assert_eq!(recovered.resolved().unresolved_count(), 1);
    assert_eq!(rows(&compact), rows(&recovered.to_compact_json()));
    assert!(recovered.resolved().element_by_id(&id).is_some());
    assert_eq!(
        rows(&full),
        rows(&session.decode_cbor(&session.to_full_cbor(true)).unwrap())
    );
}

#[test]
fn text_resolved_and_unresolved_uuid_names_keep_lexical_meaning_with_library() {
    let id = library_target_id();
    let source = format!(
        "package P {{ feature '{id}'; feature lexical = '{id}'; feature missing = '{MISSING}'; }} \
         package Other {{ feature disguised = '{id}'; }}"
    );
    let mut session = text(source, Some(library()));
    let compact = session.to_compact_json();
    assert_eq!(session.resolved().unresolved_count(), 2);
    let lexical = session
        .resolved()
        .resolve_qualified(&format!("P::'{id}'"))
        .unwrap();
    assert_ne!(session.resolved().element_id(lexical).to_string(), id);
    let full = session.to_full_json();
    let mut recovered = load(&full, Some(&library()));
    assert!(
        recovered.warnings().is_empty(),
        "{:?}",
        recovered.warnings()
    );
    assert_eq!(recovered.resolved().unresolved_count(), 2);
    assert_eq!(rows(&compact), rows(&recovered.to_compact_json()));
    assert_eq!(rows(&full), rows(&recovered.to_full_json()));
}

fn remap_user_ids(value: &mut Value) {
    let replacements: HashMap<_, _> = value
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
        .map(|(i, e)| {
            (
                e["@id"].as_str().unwrap().to_owned(),
                format!("66666666-6666-4666-8666-{i:012x}"),
            )
        })
        .collect();
    fn rewrite(value: &mut Value, replacements: &HashMap<String, String>) {
        match value {
            Value::Object(object) => {
                for (key, value) in object {
                    if matches!(key.as_str(), "@id" | "elementId") {
                        if let Some(replacement) = value.as_str().and_then(|s| replacements.get(s))
                        {
                            *value = Value::String(replacement.clone());
                        }
                    } else {
                        rewrite(value, replacements);
                    }
                }
            }
            Value::Array(items) => {
                for item in items {
                    rewrite(item, replacements);
                }
            }
            _ => {}
        }
    }
    rewrite(value, &replacements);
}

#[test]
fn nonfallback_payloads_preserve_uuid_names_with_derived_and_foreign_user_ids() {
    let id = library_target_id();
    for foreign in [false, true] {
        let session = text(
            format!("package P {{ feature value = '{id}'; }}"),
            Some(library()),
        );
        let mut compact = session.to_compact_json();
        if foreign {
            remap_user_ids(&mut compact);
        }
        let mut loaded = load(&compact, Some(&library()));
        assert_eq!(loaded.has_explicit_ids(), foreign);
        assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
        assert_eq!(loaded.resolved().unresolved_count(), 1);
        assert_eq!(rows(&compact), rows(&loaded.to_compact_json()));
        let compact_bytes = loaded.to_compact_cbor();
        let mut binary = Session::from_compact_cbor_with(&compact_bytes, Some(&library())).unwrap();
        assert!(binary.warnings().is_empty(), "{:?}", binary.warnings());
        assert_eq!(binary.resolved().unresolved_count(), 1);
        assert_eq!(rows(&compact), rows(&binary.to_compact_json()));
        let full = loaded.to_full_json();
        let mut recovered = load(&full, Some(&library()));
        assert!(
            recovered.warnings().is_empty(),
            "{:?}",
            recovered.warnings()
        );
        assert_eq!(recovered.resolved().unresolved_count(), 1);
        assert_eq!(rows(&compact), rows(&recovered.to_compact_json()));
        assert_eq!(rows(&full), rows(&recovered.to_full_json()));
        assert_eq!(
            rows(&full),
            rows(&loaded.decode_cbor(&loaded.to_full_cbor(true)).unwrap())
        );
    }
}

#[test]
fn legacy_payload_identity_fallback_keeps_existing_uuid_interpretation() {
    let session = text(
        format!("package P {{ feature value = '{MISSING}'; }}"),
        None,
    );
    let mut payload = session.to_compact_json();
    let membership = payload
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["@type"] == "Membership" && e["memberElement"].get("@ref").is_some())
        .unwrap();
    membership["memberElement"] = json!({"@id": MISSING});
    let loaded = load(&payload, None);
    assert_eq!(rows(&payload), rows(&loaded.to_compact_json()));
    let full = loaded.to_full_json();
    assert!(
        full.as_array()
            .unwrap()
            .iter()
            .any(|e| { e["@type"] == "Membership" && e["memberElement"]["@id"] == MISSING })
    );
    assert!(!full.as_array().unwrap().iter().any(|e| {
        e["language"] == sysmlv2_model::full::UNRESOLVED_REP_LANGUAGE
            && e["body"] == format!("'{MISSING}'")
    }));
}
