use std::collections::{HashMap, HashSet};
use sysmlv2_model::{
    json::{model_to_compact_json, model_to_compact_json_with_units},
    loader::{load_document_with_format, overlay_explicit_ids},
    migration::{migrate_conditional_graph, validate_graph_format},
    model::{GraphFormat, Model},
};

const TEXT: &str = "class Point {feature x; feature y;} feature empty=new Point(); feature positional=new Point(1,2); feature named=new Point(y=3,x=4); feature nested=new Point(x=if true ? new Point(5) else new Point(x=6)); class Holder {feature t:Point;} feature h:Holder; feature chained=new h.t(9);";

fn model(format: GraphFormat) -> Model {
    let mut model = Model::with_graph_format(format);
    assert!(
        model
            .add_source("constructors.kerml", TEXT)
            .diagnostics
            .is_empty()
    );
    model
}

#[test]
fn nested_constructor_migration_preserves_rows_and_does_not_capture_argument_ids() {
    let legacy = model_to_compact_json(&model(GraphFormat::LegacyV2));
    let canonical = model_to_compact_json(&model(GraphFormat::CanonicalV3));
    let migrated = migrate_conditional_graph(&legacy, &|_| None).unwrap();
    assert_eq!(migrated.document, canonical);
    validate_graph_format(&canonical, GraphFormat::CanonicalV3).unwrap();
    let old_arguments: HashSet<_> = legacy
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row["@type"] == "ParameterMembership")
        .flat_map(|row| {
            [
                row["@id"].as_str().unwrap(),
                row["ownedRelatedElement"][0]["@id"].as_str().unwrap(),
            ]
        })
        .collect();
    for row in canonical
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row["@type"] == "ReturnParameterMembership")
    {
        assert!(!old_arguments.contains(row["@id"].as_str().unwrap()));
        assert!(!old_arguments.contains(row["ownedRelatedElement"][0]["@id"].as_str().unwrap()));
    }
    for (i, &j) in migrated.element_indices.iter().enumerate() {
        assert_eq!(legacy[i]["@type"], canonical[j]["@type"]);
    }
}

#[test]
fn canonical_constructor_compact_and_full_replay_preserve_argument_ownership() {
    let model = model(GraphFormat::CanonicalV3);
    let expected = model_to_compact_json(&model);
    for document in [
        expected.clone(),
        sysmlv2_model::full::model_to_full_json(&model),
    ] {
        let (loaded, _, ids, warnings) =
            load_document_with_format(&document, &HashMap::new(), GraphFormat::CanonicalV3)
                .unwrap();
        assert!(warnings.is_empty(), "{warnings:?}");
        let mut replay = model_to_compact_json(&loaded);
        overlay_explicit_ids(&mut replay, &ids);
        assert_eq!(
            replay.as_array().unwrap().len(),
            expected.as_array().unwrap().len()
        );
        for (actual, expected) in replay
            .as_array()
            .unwrap()
            .iter()
            .zip(expected.as_array().unwrap())
        {
            for (key, value) in expected.as_object().unwrap() {
                assert_eq!(&actual[key], value, "{key} on {}", expected["@type"]);
            }
        }
        assert!(
            load_document_with_format(&document, &HashMap::new(), GraphFormat::LegacyV2).is_err()
        );
    }
}

#[test]
fn canonical_constructor_explicit_and_elided_binary_snapshots_replay_exactly() {
    let (document, units) = model_to_compact_json_with_units(&model(GraphFormat::CanonicalV3));
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
        let (decoded, _, format) = sysmlv2_cbor::from_cbor_with_format(&bytes, &|_| None).unwrap();
        assert_eq!(format, GraphFormat::CanonicalV3);
        assert_eq!(decoded, document);
    }
}

#[test]
fn canonical_constructors_keep_library_preparation_and_full_replay_equivalent() {
    let mut cold = Model::with_graph_format(GraphFormat::CanonicalV3);
    cold.load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    cold.record_library_cache();
    let prepared = cold.prepare_library().unwrap();
    let cache = cold.take_recorded_library_cache().unwrap();
    let encoded = prepared.to_bytes(29).unwrap();
    let decoded = std::sync::Arc::new(
        sysmlv2_model::prepared::PreparedLibrary::from_bytes(&encoded, 29).unwrap(),
    );
    let mut recorded = Model::with_graph_format(GraphFormat::CanonicalV3);
    recorded
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    recorded.set_library_cache(cache);
    let mut warm = Model::with_graph_format(GraphFormat::CanonicalV3);
    prepared.install(&mut warm).unwrap();
    let mut restored = Model::with_graph_format(GraphFormat::CanonicalV3);
    decoded.install(&mut restored).unwrap();
    let mut compact = None;
    let mut full = None;
    for model in [&mut cold, &mut recorded, &mut warm, &mut restored] {
        model.add_source("constructors.kerml", TEXT);
        let actual = model_to_compact_json(model);
        if let Some(ref expected) = compact {
            assert_eq!(&actual, expected);
        } else {
            compact = Some(actual);
        }
        let actual = sysmlv2_model::full::model_to_full_json(model);
        sysmlv2_model::migration::validate_conditional_graph_format(
            &actual,
            GraphFormat::CanonicalV3,
        )
        .unwrap();
        if let Some(ref expected) = full {
            assert_eq!(&actual, expected);
        } else {
            full = Some(actual);
        }
    }
}
