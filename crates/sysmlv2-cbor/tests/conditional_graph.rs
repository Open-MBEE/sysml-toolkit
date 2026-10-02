use serde_json::json;
use std::collections::HashMap;
use sysmlv2_model::{
    eval::Value as EvalValue,
    json::{ResolvedModel, model_to_compact_json, model_to_compact_json_with_units},
    loader::{load_document, load_document_with_format, overlay_explicit_ids},
    migration::{migrate_conditional_graph, validate_graph_format},
    model::{GraphFormat, Model},
};

const TEXT: &str = "package P { attribute a = false and (1/0 == 1); attribute b = true or (1/0 == 1); attribute c = false implies (1/0 == 1); attribute d = 7 ?? (1/0); attribute e = if true ? (if false ? 1/0 else 8) else 1/0; attribute f = null ?? 9; }";
fn model(format: GraphFormat) -> Model {
    let mut model = Model::with_graph_format(format);
    assert!(
        model
            .add_source("conditionals.sysml", TEXT)
            .diagnostics
            .is_empty()
    );
    model
}
fn evaluate(r: &mut ResolvedModel) {
    for (name, expected) in [
        ("a", EvalValue::Boolean(false)),
        ("b", EvalValue::Boolean(true)),
        ("c", EvalValue::Boolean(true)),
        ("d", EvalValue::Integer(7)),
        ("e", EvalValue::Integer(8)),
        ("f", EvalValue::Integer(9)),
    ] {
        assert_eq!(r.evaluate_qualified(&format!("P::{name}")), Ok(expected));
    }
}
#[test]
fn migration_matches_canonical_lowering_and_preserves_short_circuiting() {
    let legacy = model(GraphFormat::LegacyV2);
    let canonical = model(GraphFormat::CanonicalV3);
    let before = model_to_compact_json(&legacy);
    let snapshot = before.clone();
    let expected = model_to_compact_json(&canonical);
    let migration = migrate_conditional_graph(&before, &|_| None).unwrap();
    assert_eq!(before, snapshot);
    assert_eq!(
        migration.document.as_array().unwrap().len(),
        expected.as_array().unwrap().len()
    );
    for (i, (actual, expected)) in migration
        .document
        .as_array()
        .unwrap()
        .iter()
        .zip(expected.as_array().unwrap())
        .enumerate()
    {
        assert_eq!(actual, expected, "row {i}");
    }
    assert_eq!(migration.added.len(), 18);
    assert_eq!(migration.ids.len(), before.as_array().unwrap().len());
    for (i, &j) in migration.element_indices.iter().enumerate() {
        assert_eq!(before[i]["@type"], expected[j]["@type"]);
        assert_eq!(
            migration.ids[&uuid::Uuid::parse_str(before[i]["@id"].as_str().unwrap()).unwrap()]
                .to_string(),
            expected[j]["@id"]
        );
    }
    assert!(validate_graph_format(&expected, GraphFormat::LegacyV2).is_err());
    assert!(validate_graph_format(&before, GraphFormat::CanonicalV3).is_err());
    assert!(migrate_conditional_graph(&expected, &|_| None).is_err());
    evaluate(&mut ResolvedModel::build(&legacy));
    evaluate(&mut ResolvedModel::build(&canonical));
    let (_, mut legacy_replay, _, warnings) = load_document(&before, &HashMap::new()).unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    evaluate(&mut legacy_replay);
    let (loaded, mut replay, ids, warnings) =
        load_document_with_format(&expected, &HashMap::new(), GraphFormat::CanonicalV3).unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    let mut after = model_to_compact_json(&loaded);
    overlay_explicit_ids(&mut after, &ids);
    assert_eq!(after, expected);
    evaluate(&mut replay);
    let full = sysmlv2_model::full::model_to_full_json(&canonical);
    let (loaded, mut replay, ids, warnings) =
        load_document_with_format(&full, &HashMap::new(), GraphFormat::CanonicalV3).unwrap();
    assert!(warnings.is_empty(), "{warnings:?}");
    let mut after = model_to_compact_json(&loaded);
    overlay_explicit_ids(&mut after, &ids);
    assert_eq!(
        after.as_array().unwrap().len(),
        expected.as_array().unwrap().len()
    );
    for (i, (actual, original)) in after
        .as_array()
        .unwrap()
        .iter()
        .zip(expected.as_array().unwrap())
        .enumerate()
    {
        for (key, value) in original.as_object().unwrap() {
            assert_eq!(&actual[key], value, "row {i}, {key}");
        }
    }
    evaluate(&mut replay);
}
#[test]
fn binary_format_and_unit_paths_survive_both_snapshot_encodings() {
    let canonical = model(GraphFormat::CanonicalV3);
    let (document, units) = model_to_compact_json_with_units(&canonical);
    for elided in [false, true] {
        let bytes = if elided {
            sysmlv2_cbor::to_compact_cbor_elided_with_format(
                &document,
                &|_| None,
                &units,
                GraphFormat::CanonicalV3,
            )
        } else {
            sysmlv2_cbor::to_compact_cbor_with_format(&document, &units, GraphFormat::CanonicalV3)
        }
        .unwrap();
        assert_eq!(
            sysmlv2_cbor::describe(&bytes).unwrap()["versions"]["scheme"],
            3
        );
        let (decoded, decoded_units, format) =
            sysmlv2_cbor::from_cbor_with_format(&bytes, &|_| None).unwrap();
        assert_eq!(decoded, document);
        assert_eq!(
            decoded_units,
            units
                .iter()
                .map(|(i, n)| (*i as u64, n.clone()))
                .collect::<Vec<_>>()
        );
        assert_eq!(format, GraphFormat::CanonicalV3);
        let (_, mut replay, _, warnings) =
            load_document_with_format(&decoded, &HashMap::new(), format).unwrap();
        assert!(warnings.is_empty(), "{warnings:?}");
        evaluate(&mut replay);
    }
}
#[test]
fn migration_updates_inbound_references_simultaneously_and_refuses_bad_ownership() {
    let mut before = model_to_compact_json(&model(GraphFormat::LegacyV2));
    // An existing non-ownership reference may point at the moved operand.
    let migration = migrate_conditional_graph(&before, &|_| None).unwrap();
    let old = *migration.ids.iter().find(|(a, b)| a != b).unwrap().0;
    let alias = uuid::Uuid::new_v5(
        &uuid::Uuid::parse_str(before[0]["@id"].as_str().unwrap()).unwrap(),
        b"::alias",
    );
    let root = before[0]["@id"].clone();
    before[0]["ownedRelationship"]
        .as_array_mut()
        .unwrap()
        .push(json!({"@id":alias}));
    before.as_array_mut().unwrap().push(json!({"@id":alias,"@type":"Membership","isImplied":false,"ownedRelationship":[],"ownedRelatedElement":[],"owningRelationship":null,"owningRelatedElement":{"@id":root},"memberElement":{"@id":old},"memberName":"alias"}));
    let migrated = migrate_conditional_graph(&before, &|_| None).unwrap();
    assert!(
        migrated
            .document
            .as_array()
            .unwrap()
            .iter()
            .any(|r| r.get("memberElement") == Some(&json!({"@id": migrated.ids[&old]})))
    );
    let mut malformed = before.clone();
    malformed.as_array_mut().unwrap().push(before[1].clone());
    assert!(migrate_conditional_graph(&malformed, &|_| None).is_err());
    let mut malformed = before.clone();
    let child = malformed
        .as_array_mut()
        .unwrap()
        .iter_mut()
        .find(|r| r["owningRelationship"].is_object())
        .unwrap();
    child["owningRelationship"] = json!({"@id":uuid::Uuid::nil()});
    assert!(migrate_conditional_graph(&malformed, &|_| None).is_err());
}
#[test]
fn prepared_and_resolution_caches_keep_their_graph_contract() {
    let source = "standard library package L { feature value = if true ? 1 else 2; }";
    let mut legacy = Model::new();
    legacy.add_library_source("library.kerml", source);
    legacy.record_library_cache();
    ResolvedModel::build(&legacy);
    let cache = legacy.take_recorded_library_cache().unwrap();
    let prepared = legacy.prepare_library().unwrap();
    let mut canonical = Model::with_graph_format(GraphFormat::CanonicalV3);
    assert!(prepared.install(&mut canonical).is_err());
    canonical.add_library_source("library.kerml", source);
    canonical.set_library_cache(cache);
    let actual = sysmlv2_model::json::library_to_compact_json(&canonical);
    let mut cold = Model::with_graph_format(GraphFormat::CanonicalV3);
    cold.add_library_source("library.kerml", source);
    assert_eq!(actual, sysmlv2_model::json::library_to_compact_json(&cold));
    let prepared = cold.prepare_library().unwrap();
    let bytes = prepared.to_bytes(71).unwrap();
    let decoded = std::sync::Arc::new(
        sysmlv2_model::prepared::PreparedLibrary::from_bytes(&bytes, 71).unwrap(),
    );
    assert_eq!(decoded.graph_format(), GraphFormat::CanonicalV3);
    let mut restored = Model::with_graph_format(GraphFormat::CanonicalV3);
    decoded.install(&mut restored).unwrap();
    assert_eq!(
        actual,
        sysmlv2_model::json::library_to_compact_json(&restored)
    );
}

#[test]
fn supplied_sources_migrate_to_the_same_canonical_graph() {
    let root = sysmlv2_testkit::corpus_root();
    let mut legacy = Model::new();
    let mut canonical = Model::with_graph_format(GraphFormat::CanonicalV3);
    for file in sysmlv2_testkit::user_files() {
        let name = sysmlv2_testkit::relative_source_name(&root, &file);
        let text = std::fs::read_to_string(file).unwrap();
        legacy.add_source(name.clone(), &text);
        canonical.add_source(name, &text);
    }
    let before = model_to_compact_json(&legacy);
    let expected = model_to_compact_json(&canonical);
    let migration = migrate_conditional_graph(&before, &|_| None).unwrap();
    assert_eq!(
        migration.document.as_array().unwrap().len(),
        expected.as_array().unwrap().len()
    );
    for (i, (actual, expected)) in migration
        .document
        .as_array()
        .unwrap()
        .iter()
        .zip(expected.as_array().unwrap())
        .enumerate()
    {
        assert_eq!(actual, expected, "row {i}");
    }
    assert!(!migration.added.is_empty());
    let bytes = sysmlv2_cbor::to_compact_cbor_elided_with_format(
        &expected,
        &|_| None,
        &[],
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    assert_eq!(
        sysmlv2_cbor::from_cbor_with_format(&bytes, &|_| None)
            .unwrap()
            .0,
        expected
    );
}

#[test]
fn canonical_standard_library_cold_recorded_and_prepared_replay_agree() {
    let mut cold = Model::with_graph_format(GraphFormat::CanonicalV3);
    cold.load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    cold.record_library_cache();
    let prepared = cold.prepare_library().unwrap();
    let cache = cold.take_recorded_library_cache().unwrap();
    let library = sysmlv2_model::json::library_to_compact_json(&cold);
    validate_graph_format(&library, GraphFormat::CanonicalV3).unwrap();
    let mut recorded = Model::with_graph_format(GraphFormat::CanonicalV3);
    recorded
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    recorded.set_library_cache(cache);
    assert_eq!(
        sysmlv2_model::json::library_to_compact_json(&recorded),
        library
    );
    let mut warm = Model::with_graph_format(GraphFormat::CanonicalV3);
    prepared.install(&mut warm).unwrap();
    for m in [&mut cold, &mut recorded, &mut warm] {
        m.add_source("conditionals.sysml", TEXT);
    }
    let expected = model_to_compact_json(&cold);
    assert_eq!(model_to_compact_json(&recorded), expected);
    assert_eq!(model_to_compact_json(&warm), expected);
    evaluate(&mut ResolvedModel::build(&cold));
    evaluate(&mut ResolvedModel::build(&recorded));
    evaluate(&mut ResolvedModel::build(&warm));
    let full = sysmlv2_model::full::model_to_full_json(&warm);
    sysmlv2_model::migration::validate_conditional_graph_format(&full, GraphFormat::CanonicalV3)
        .unwrap();
}
