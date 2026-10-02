//! Library identity fallback is distinct from authored lexical spelling.
use serde_json::{Value, json};
use std::collections::HashMap;
use sysmlv2_model::{json::ResolvedModel, model::Model};
use sysmlv2_transform::{Library, Session};

const LIBRARY: &str = "standard library package Lib { private function Hidden { return result; } function Public specializes Hidden; feature visible; datatype Scalar; function Anonymous { return : Scalar; } }";
fn library() -> Library {
    Library::sources(vec![("lib.kerml".into(), LIBRARY.into())])
}
fn model(source: &str) -> (Model, ResolvedModel) {
    let mut m = Model::new();
    m.add_library_source("lib.kerml", LIBRARY);
    m.add_source("u.kerml", source);
    assert!(!m.has_errors());
    let r = ResolvedModel::build(&m);
    (m, r)
}
fn rows(v: &Value) -> HashMap<String, Value> {
    v.as_array()
        .unwrap()
        .iter()
        .map(|e| (e["@id"].as_str().unwrap().to_owned(), e.clone()))
        .collect()
}
fn load(v: &Value) -> Session {
    Session::from_interchange_json_named(v, Some(&library()), &["u.kerml".into()]).unwrap()
}
#[test]
fn private_declaring_path_preserves_inherited_library_result_and_import_identity() {
    let source = "package P { feature x = Lib::Public::result; import Lib::Public::result; import Lib::visible; }";
    let (m, mut r) = model(source);
    let hidden = r.resolve_qualified("Lib::Hidden::result").unwrap();
    let public = r.resolve_qualified("Lib::Public::result").unwrap();
    assert_eq!(hidden, public);
    let compact = sysmlv2_model::json::model_to_compact_json(&m);
    let full = sysmlv2_model::full::model_to_full_json_with(&m, false);
    let mut loaded = load(&compact);
    assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
    assert!(!loaded.has_explicit_ids());
    assert_eq!(rows(&compact), rows(&loaded.to_compact_json()));
    let reloaded_full = loaded.to_full_json_with(false);
    assert_eq!(rows(&full), rows(&reloaded_full));
    let compact_bytes = loaded.to_compact_cbor();
    let binary = Session::from_compact_cbor_with(&compact_bytes, Some(&library())).unwrap();
    assert!(binary.warnings().is_empty(), "{:?}", binary.warnings());
    assert_eq!(rows(&compact), rows(&binary.to_compact_json()));
    let elided = loaded.to_compact_cbor_elided().unwrap();
    assert_eq!(rows(&compact), rows(&loaded.decode_cbor(&elided).unwrap()));
    let full_bytes = loaded.to_full_cbor(false);
    assert_eq!(rows(&full), rows(&loaded.decode_cbor(&full_bytes).unwrap()));
    for e in compact
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["@type"] == "MembershipImport")
    {
        let id = e["importedMembership"]["@id"].as_str().unwrap();
        let target = loaded.resolved().element_by_id(id).unwrap();
        assert!(
            loaded
                .resolved()
                .element_type(target)
                .ends_with("Membership")
        );
    }
}
#[test]
fn fallback_preserves_unresolved_and_resolved_uuid_shaped_authored_names() {
    let (_, mut r) = model("");
    let target = r.resolve_qualified("Lib::Public::result").unwrap();
    let id = r.element_id(target);
    let missing = "88888888-8888-4888-8888-888888888888";
    let source = format!(
        "package P {{ feature '{id}'; feature lexical = '{id}'; feature missing = '{missing}'; feature actual = Lib::Public::result; }} package Other {{ feature disguised = '{id}'; }}"
    );
    let (m, _) = model(&source);
    let compact = sysmlv2_model::json::model_to_compact_json(&m);
    assert!(
        compact
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["memberElement"] == json!({"@ref":format!("'{missing}'")}))
    );
    let mut loaded = load(&compact);
    assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
    assert_eq!(rows(&compact), rows(&loaded.to_compact_json()));
    let lexical = loaded
        .resolved()
        .resolve_qualified(&format!("P::'{id}'"))
        .unwrap();
    assert_ne!(loaded.resolved().element_id(lexical), id);
    assert_eq!(loaded.resolved().unresolved_count(), 2);
    let recovered = load(&loaded.to_full_json());
    assert!(
        recovered.warnings().is_empty(),
        "{:?}",
        recovered.warnings()
    );
    assert_eq!(rows(&compact), rows(&recovered.to_compact_json()));
    loaded.minimize_qualifications().unwrap();
    loaded.load_library_from(library()).unwrap();
    assert_eq!(rows(&compact), rows(&loaded.to_compact_json()));
}
#[test]
fn strict_identity_site_survives_unrelated_edit_and_parent_rename_then_releases_changed_target() {
    let (m, mut original) = model("package P { feature x = Lib::Public::result; }");
    let target = original.resolve_qualified("Lib::Public::result").unwrap();
    let target_id = original.element_id(target).to_string();
    let mut loaded = load(&sysmlv2_model::json::model_to_compact_json(&m));
    let p = loaded.resolved().resolve_qualified("P").unwrap();
    let mut edit = loaded.edit();
    edit.insert_member(p, "package Unrelated;");
    edit.commit().unwrap();
    let p = loaded.resolved().resolve_qualified("P").unwrap();
    let mut edit = loaded.edit();
    edit.rename(p, "Renamed");
    edit.commit().unwrap();
    let compact = loaded.to_compact_json();
    assert!(
        compact
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "Membership" && e["memberElement"]["@id"] == target_id)
    );
    loaded.load_library_from(library()).unwrap();
    assert_eq!(rows(&compact), rows(&loaded.to_compact_json()));
    let x = loaded.resolved().resolve_qualified("Renamed::x").unwrap();
    let mut edit = loaded.edit();
    edit.set_feature_value(x, "Lib::visible");
    edit.commit().unwrap();
    let visible = loaded.resolved().resolve_qualified("Lib::visible").unwrap();
    let visible_id = loaded.resolved().element_id(visible).to_string();
    let after = loaded.to_compact_json();
    assert!(
        after
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "Membership" && e["memberElement"]["@id"] == visible_id)
    );
    assert!(
        !after
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "Membership" && e["memberElement"]["@id"] == target_id)
    );
}
#[test]
fn strict_fallback_preserves_an_unnamed_library_return_parameter() {
    let (m, mut r) = model(
        "package P { feature actual = Lib::Public::result; feature unnamed = Lib::visible; }",
    );
    let owner = r.resolve_qualified("Lib::Anonymous").unwrap();
    let elements: Vec<_> = r.elements().collect();
    let target = elements
        .into_iter()
        .find(|&e| {
            r.element_type(e) == "Feature"
                && r.element_name(e).is_none()
                && r.owner(e) == Some(owner)
        })
        .unwrap();
    let target_id = r.element_id(target).to_string();
    let visible = r.resolve_qualified("Lib::visible").unwrap();
    let visible_id = r.element_id(visible).to_string();
    let mut compact = sysmlv2_model::json::model_to_compact_json(&m);
    let row = compact
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["@type"] == "Membership" && e["memberElement"]["@id"] == visible_id)
        .unwrap();
    row["memberElement"] = json!({"@id":target_id});
    let mut loaded = load(&compact);
    assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
    assert_eq!(rows(&compact), rows(&loaded.to_compact_json()));
    assert!(loaded.resolved().element_by_id(&target_id).is_some());
}

#[test]
fn private_library_reference_survives_foreign_user_ids_and_full_reload() {
    let (_, mut r) = model("");
    let target = r.resolve_qualified("Lib::Public::result").unwrap();
    let id = r.element_id(target);
    let (m, _) = model(&format!(
        "package P {{ feature '{id}'; feature lexical = '{id}'; feature x = Lib::Public::result; import Lib::Public::result; alias kept for '{id}'; }}"
    ));
    let mut compact = sysmlv2_model::json::model_to_compact_json(&m);
    let replacements: HashMap<_, _> = compact
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
        .map(|(i, e)| {
            (
                e["@id"].as_str().unwrap().to_owned(),
                format!("99999999-9999-4999-8999-{i:012x}"),
            )
        })
        .collect();
    fn rewrite(value: &mut Value, replacements: &HashMap<String, String>) {
        match value {
            Value::Object(o) => {
                for (key, value) in o {
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
    rewrite(&mut compact, &replacements);
    let loaded = load(&compact);
    assert!(loaded.has_explicit_ids());
    assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
    assert_eq!(rows(&compact), rows(&loaded.to_compact_json()));
    let full = loaded.to_full_json_with(false);
    let again = load(&full);
    assert!(again.warnings().is_empty(), "{:?}", again.warnings());
    assert_eq!(rows(&compact), rows(&again.to_compact_json()));
    assert_eq!(rows(&full), rows(&again.to_full_json_with(false)));
}

#[test]
fn strict_library_identity_survives_member_move_and_dry_run_then_can_be_deleted() {
    let (m, mut r) = model("package P { feature x = Lib::Public::result; } package Destination;");
    let target = r.resolve_qualified("Lib::Public::result").unwrap();
    let target_id = r.element_id(target).to_string();
    let mut loaded = load(&sysmlv2_model::json::model_to_compact_json(&m));
    let before = loaded.to_compact_json();
    let x = loaded.resolved().resolve_qualified("P::x").unwrap();
    let destination = loaded.resolved().resolve_qualified("Destination").unwrap();
    let mut edit = loaded.edit();
    edit.move_member(x, destination, None);
    edit.check().unwrap();
    assert_eq!(rows(&before), rows(&loaded.to_compact_json()));
    let x = loaded.resolved().resolve_qualified("P::x").unwrap();
    let destination = loaded.resolved().resolve_qualified("Destination").unwrap();
    let mut edit = loaded.edit();
    edit.move_member(x, destination, None);
    edit.commit().unwrap();
    assert!(
        loaded
            .resolved()
            .resolve_qualified("Destination::x")
            .is_some()
    );
    let moved = loaded.to_compact_json();
    assert!(
        moved
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "Membership" && e["memberElement"]["@id"] == target_id)
    );
    assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
    let x = loaded
        .resolved()
        .resolve_qualified("Destination::x")
        .unwrap();
    let mut edit = loaded.edit();
    edit.remove(x);
    edit.commit().unwrap();
    assert!(
        !loaded
            .to_compact_json()
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "Membership" && e["memberElement"]["@id"] == target_id)
    );
}

#[test]
fn unsupported_consumed_identity_provenance_refuses_transactionally() {
    let (m, _) = model("package P { feature x = Lib::Public::result; }");
    let mut loaded = load(&sysmlv2_model::json::model_to_compact_json(&m));
    let before = loaded.to_compact_json();
    let p = loaded.resolved().resolve_qualified("P").unwrap();
    let mut edit = loaded.edit();
    edit.add_unit("moved.kerml");
    edit.hoist_to_unit(p, "moved.kerml", None);
    let error = edit.commit().unwrap_err();
    assert!(
        matches!(
            error,
            sysmlv2_transform::TransformError::SemanticIdentity { .. }
        ),
        "{error}"
    );
    assert!(
        error.to_string().contains("payload identity reference"),
        "{error}"
    );
    assert_eq!(rows(&before), rows(&loaded.to_compact_json()));
    loaded.load_library_from(library()).unwrap();
    assert_eq!(rows(&before), rows(&loaded.to_compact_json()));
}

#[test]
fn changing_an_unnamed_user_target_identity_refuses_instead_of_leaving_external_id() {
    let (m, mut r) = model(
        "package P { feature; feature x = Lib::Public::result; feature user = Lib::visible; }",
    );
    let p = r.resolve_qualified("P").unwrap();
    let elements: Vec<_> = r.elements().collect();
    let anonymous = elements
        .into_iter()
        .find(|&e| {
            r.element_type(e) == "Feature" && r.element_name(e).is_none() && r.owner(e) == Some(p)
        })
        .unwrap();
    let anonymous_id = r.element_id(anonymous).to_string();
    let visible = r.resolve_qualified("Lib::visible").unwrap();
    let visible_id = r.element_id(visible).to_string();
    let mut payload = sysmlv2_model::json::model_to_compact_json(&m);
    let site = payload
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|e| e["@type"] == "Membership" && e["memberElement"]["@id"] == visible_id)
        .unwrap();
    site["memberElement"] = json!({"@id":anonymous_id});
    let mut loaded = load(&payload);
    let before = loaded.to_compact_json();
    assert!(loaded.resolved().element_by_id(&anonymous_id).is_some());
    let p = loaded.resolved().resolve_qualified("P").unwrap();
    let mut edit = loaded.edit();
    edit.rename(p, "Renamed");
    let error = edit.commit().unwrap_err();
    assert!(
        matches!(
            error,
            sysmlv2_transform::TransformError::SemanticIdentity { .. }
        ),
        "{error}"
    );
    assert!(
        error.to_string().contains("payload identity reference"),
        "{error}"
    );
    assert_eq!(rows(&before), rows(&loaded.to_compact_json()));
}

#[test]
fn bound_compact_full_policy_treats_remaining_uuid_refs_as_lexical() {
    use sysmlv2_model::full::{EmissionError, EmissionPolicy, UnresolvedReferencePolicy};
    let spelling = "'88888888-8888-4888-8888-888888888888'";
    let (m, mut r) = model(&format!("package P {{ feature x = {spelling}; }}"));
    let compact = sysmlv2_model::json::model_to_compact_json(&m);
    let previous = r.closure_policy();
    let reject = sysmlv2_model::full::resolved_compact_to_full_json(
        &mut r,
        &m,
        compact.clone(),
        EmissionPolicy {
            unresolved: UnresolvedReferencePolicy::Reject,
            closures: Default::default(),
        },
    )
    .unwrap_err();
    assert!(
        matches!(reject, EmissionError::UnresolvedReferences(error) if error.references == vec![spelling])
    );
    assert_eq!(r.closure_policy(), previous);
    let full = sysmlv2_model::full::resolved_compact_to_full_json(
        &mut r,
        &m,
        compact,
        EmissionPolicy::default(),
    )
    .unwrap();
    assert!(full.as_array().unwrap().iter().any(|e| e["language"]
        == sysmlv2_model::full::UNRESOLVED_REP_LANGUAGE
        && e["body"] == spelling));
    let dangling = sysmlv2_model::json::dangling_id(spelling);
    assert!(
        full.as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "Membership" && e["memberElement"]["@id"] == dangling)
    );
    // Existing compatibility entry points retain their documented ID-shaped
    // spelling interpretation; only bound-compact input establishes provenance.
    let legacy = sysmlv2_model::full::model_to_full_json_with(&m, true);
    assert!(
        legacy
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == "Membership"
                && e["memberElement"]["@id"] == spelling.trim_matches('\''))
    );
}

#[test]
fn recovered_effective_names_preserve_structural_pairing() {
    for keyword in ["references", "redefines"] {
        for spelling in [
            "Missing",
            "'88888888-8888-4888-8888-888888888888'",
            "'missing::quoted'",
            "Missing::'quoted::leaf'",
        ] {
            let source = format!(
                "package P {{ feature actual = Lib::Public::result; feature {keyword} {spelling}; }}"
            );
            let (m, _) = model(&source);
            let compact = sysmlv2_model::json::model_to_compact_json(&m);
            let loaded = load(&compact);
            assert!(
                loaded.warnings().is_empty(),
                "{keyword} {spelling}: {:?}",
                loaded.warnings()
            );
            let recovered = load(&loaded.to_full_json());
            assert!(
                recovered.warnings().is_empty(),
                "{keyword} {spelling}: {:?}",
                recovered.warnings()
            );
            assert!(!recovered.has_explicit_ids(), "{keyword} {spelling}");
            assert_eq!(
                rows(&compact),
                rows(&recovered.to_compact_json()),
                "{keyword} {spelling}"
            );
        }
    }
}

fn check_expression_reference_membership_roundtrip(fragment: &str, expression_type: &str) {
    let (m, _) = model(&format!(
        "package P {{ feature actual = Lib::Public::result; \
         feature target; alias kept for target; \
         feature body = {{ alias bodyKept for target; bodyKept }}; {fragment} }}"
    ));
    let mut compact = sysmlv2_model::json::model_to_compact_json(&m);
    assert!(
        compact
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["@type"] == expression_type)
    );
    let replacements: HashMap<_, _> = compact
        .as_array()
        .unwrap()
        .iter()
        .enumerate()
        .map(|(i, e)| {
            (
                e["@id"].as_str().unwrap().to_owned(),
                format!("77777777-7777-4777-8777-{i:012x}"),
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
    rewrite(&mut compact, &replacements);
    let loaded = load(&compact);
    assert!(loaded.has_explicit_ids());
    assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
    assert_eq!(rows(&compact), rows(&loaded.to_compact_json()));
    let full = loaded.to_full_json_with(false);
    let recovered = load(&full);
    assert!(recovered.has_explicit_ids());
    assert!(
        recovered.warnings().is_empty(),
        "{:?}",
        recovered.warnings()
    );
    assert_eq!(rows(&compact), rows(&recovered.to_compact_json()));
    assert_eq!(rows(&full), rows(&recovered.to_full_json_with(false)));
    for alias in ["kept", "bodyKept"] {
        assert!(
            recovered
                .to_compact_json()
                .as_array()
                .unwrap()
                .iter()
                .any(|e| { e["@type"] == "Membership" && e["memberName"] == alias })
        );
    }
}

#[test]
fn invocation_reference_membership_preserves_foreign_identity() {
    check_expression_reference_membership_roundtrip(
        "function F { return result; } feature value = F();",
        "InvocationExpression",
    );
}

#[test]
fn constructor_reference_membership_preserves_foreign_identity() {
    check_expression_reference_membership_roundtrip(
        "class T; feature value = new T();",
        "ConstructorExpression",
    );
}

#[test]
fn metadata_reference_membership_preserves_foreign_identity() {
    check_expression_reference_membership_roundtrip(
        "class T; feature value = T.metadata;",
        "MetadataAccessExpression",
    );
}

#[test]
fn chain_reference_membership_preserves_foreign_identity() {
    check_expression_reference_membership_roundtrip(
        "class T { feature child; } feature obj : T; feature value = obj.child;",
        "FeatureChainExpression",
    );
}
