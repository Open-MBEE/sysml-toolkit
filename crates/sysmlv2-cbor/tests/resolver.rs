//! Resolver gates: the resolver artifact round-trips through the
//! Model-free loader, answers both directions with the normative
//! ids, enforces its collision and version policies, and — the
//! decisive gate — decodes an id-elided payload identically to the
//! model-backed resolver.

use serde_json::Value;
use sysmlv2_cbor::resolver::StdlibResolver;
use sysmlv2_parser::json::{
    library_name_map, library_resolver_artifact, library_to_compact_json, model_to_compact_json,
};
use sysmlv2_parser::model::Model;

const REAL: &str = "14c0aa22-5489-59b5-b438-ded26e83ba31";

fn library_model() -> Option<Model> {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: library not present");
        return None;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).expect("library loads");
    Some(model)
}

fn artifact_of(model: &Model) -> Value {
    let export = library_to_compact_json(model);
    let digest = sysmlv2_cbor::state_digest(&export).unwrap();
    library_resolver_artifact(
        model,
        &digest.to_string(),
        sysmlv2_cbor::tables::CBOR_TABLES_VERSION,
        sysmlv2_cbor::ID_SCHEME_VERSION,
        "test",
    )
}

#[test]
fn artifact_answers_both_directions_without_a_model() {
    let Some(model) = library_model() else { return };
    let value = artifact_of(&model);
    // The consumer sees only bytes.
    let bytes = serde_json::to_vec(&value).unwrap();
    let resolver = StdlibResolver::from_json_bytes(&bytes).unwrap();
    resolver.assert_compatible().unwrap();

    assert_eq!(resolver.external_name(REAL).as_deref(), Some("Real"));
    assert_eq!(
        resolver.segments(REAL).map(|s| s.join("::")).as_deref(),
        Some("ScalarValues::Real")
    );
    assert_eq!(resolver.id_of("ScalarValues::Real"), Some(REAL));
    // Memberships/aliases resolve forward but never inversely: the
    // forward map is strictly larger, and collisions never leak.
    assert!(resolver.forward_len() > resolver.inverse_len());
    assert!(resolver.units() >= 90, "{} units", resolver.units());
}

#[test]
fn elided_payload_decodes_through_the_artifact_alone() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: library not present");
        return;
    }
    // A user model with a live library reference.
    let mut model = Model::new();
    model.load_library_dir(&lib).expect("library loads");
    model.add_source(
        "m.sysml".to_string(),
        "package P { import ScalarValues::*; attribute x : Real; }",
    );
    let compact = model_to_compact_json(&model);
    // Encoder side: model-backed names (the session path).
    let model_names: std::collections::HashMap<String, String> = library_name_map(&model)
        .into_iter()
        .filter_map(|(id, segs)| segs.last().cloned().map(|last| (id, last)))
        .collect();
    let bytes =
        sysmlv2_cbor::to_compact_cbor_elided(&compact, &|s| model_names.get(s).cloned()).unwrap();

    // Decoder side: the artifact, nothing else.
    let resolver =
        StdlibResolver::from_json_bytes(&serde_json::to_vec(&artifact_of(&model)).unwrap())
            .unwrap();
    let decoded = sysmlv2_cbor::from_cbor_with(&bytes, &|s| resolver.external_name(s)).unwrap();
    assert_eq!(decoded, compact, "artifact-backed decode is identical");
}

#[test]
fn collision_and_version_policies_are_loud() {
    let mut v = serde_json::json!({
        "format": "sysmlv2-stdlib-resolver", "formatVersion": 1,
        "toolkit": "t", "tablesVersion": sysmlv2_cbor::tables::CBOR_TABLES_VERSION,
        "schemeVersion": sysmlv2_cbor::ID_SCHEME_VERSION,
        "libraryStateDigest": "d", "units": 1,
        "forward": {
            "00000000-0000-4000-8000-000000000001": ["Pkg", "Dup"],
            "00000000-0000-4000-8000-000000000002": ["Pkg", "Dup"],
        },
        "inverse": {},
        "collisions": ["Pkg::Dup"],
    });
    let r = StdlibResolver::from_value(&v).unwrap();
    assert_eq!(r.id_of("Pkg::Dup"), None, "collisions never resolve");
    assert!(r.is_collision("Pkg::Dup"));

    v["tablesVersion"] = serde_json::json!(9999);
    let r = StdlibResolver::from_value(&v).unwrap();
    let err = r.assert_compatible().unwrap_err().to_string();
    assert!(err.contains("tables version"), "{err}");

    v["format"] = serde_json::json!("something-else");
    assert!(StdlibResolver::from_value(&v).is_err());
}

#[test]
fn generated_collisions_never_leak_into_the_inverse() {
    let Some(model) = library_model() else { return };
    let value = artifact_of(&model);
    let inverse = value["inverse"].as_object().unwrap();
    let collisions = value["collisions"].as_array().unwrap();
    for c in collisions {
        assert!(
            !inverse.contains_key(c.as_str().unwrap()),
            "collision {c} leaked into the inverse"
        );
    }
    println!(
        "library collisions: {} (inverse {}, forward {})",
        collisions.len(),
        inverse.len(),
        value["forward"].as_object().unwrap().len()
    );
}
