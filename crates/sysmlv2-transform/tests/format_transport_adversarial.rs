use std::collections::HashMap;
use sysmlv2_model::loader::load_document_with_format;
use sysmlv2_transform::{GraphFormat, Indent, Library, Session};

fn session(format: GraphFormat, conditional: bool, value: usize) -> Session {
    let expression = if conditional {
        format!("if true ? {value} else 1/0")
    } else {
        value.to_string()
    };
    Session::from_sources_with_graph_format(
        vec![(
            "model.sysml".into(),
            format!("package P {{ attribute x = {expression}; }}"),
        )],
        None,
        format,
    )
    .unwrap()
}

#[test]
fn graph_aware_loaders_refuse_cross_format_conditional_rebuilds() {
    for (source, target) in [
        (GraphFormat::LegacyV2, GraphFormat::CanonicalV3),
        (GraphFormat::CanonicalV3, GraphFormat::LegacyV2),
    ] {
        let document = session(source, true, 7).to_compact_json();
        assert!(
            Session::from_interchange_json_with_graph_format(
                &document,
                None,
                &["model.sysml".into()],
                Indent::default(),
                target,
            )
            .is_err(),
            "a graph contract mismatch must not reassign an operand ID to its wrapper"
        );
        assert!(load_document_with_format(&document, &HashMap::new(), target).is_err());
    }
}

#[test]
fn session_snapshot_context_rejects_other_contract_even_without_conditionals() {
    for (source, target) in [
        (GraphFormat::LegacyV2, GraphFormat::CanonicalV3),
        (GraphFormat::CanonicalV3, GraphFormat::LegacyV2),
    ] {
        let producer = session(source, false, 7);
        let receiver = session(target, false, 7);
        // The graph shapes happen to coincide here. The header, not shape
        // inference, must keep the selected library/identity context intact.
        assert_eq!(producer.to_compact_json(), receiver.to_compact_json());
        for bytes in [
            producer.to_compact_cbor(),
            producer.to_compact_cbor_elided().unwrap(),
            producer.to_full_cbor(false),
        ] {
            assert!(receiver.decode_cbor(&bytes).is_err());
            assert!(producer.decode_cbor(&bytes).is_ok());
        }
    }
}

#[test]
fn session_delta_context_refuses_cross_contract_strict_elided_and_portable_payloads() {
    for (source, target) in [
        (GraphFormat::LegacyV2, GraphFormat::CanonicalV3),
        (GraphFormat::CanonicalV3, GraphFormat::LegacyV2),
    ] {
        let base = session(source, false, 7).to_compact_json();
        let producer = session(source, false, 8);
        let receiver = session(target, false, 7);
        assert_eq!(base, receiver.to_compact_json());
        for (bytes, lenient) in [
            (producer.delta_cbor_from(&base, false).unwrap(), false),
            (producer.delta_cbor_elided_from(&base).unwrap(), false),
            (producer.delta_cbor_from(&base, true).unwrap(), true),
        ] {
            assert!(receiver.apply_delta_cbor(&bytes, lenient).is_err());
            assert!(
                receiver
                    .apply_delta_cbor_to(&bytes, &base, lenient)
                    .is_err()
            );
            assert!(producer.apply_delta_cbor_to(&bytes, &base, lenient).is_ok());
        }
    }
}

#[test]
fn explicit_legacy_snapshots_keep_historical_scheme_compatibility() {
    let original = session(GraphFormat::LegacyV2, true, 7);
    let document = original.to_compact_json();
    for scheme in [1, 255] {
        let mut bytes = original.to_compact_cbor();
        // Eight-byte magic, outer array, uint64 header; scheme byte at 16.
        bytes[16] = scheme;
        assert_eq!(sysmlv2_cbor::from_compact_cbor(&bytes).unwrap(), document);
        assert_eq!(original.decode_cbor(&bytes).unwrap(), document);
        let replay = Session::from_compact_cbor(&bytes).unwrap();
        assert_eq!(replay.model().graph_format(), GraphFormat::LegacyV2);
        assert_eq!(replay.to_compact_json(), document);
        assert!(
            session(GraphFormat::CanonicalV3, true, 7)
                .decode_cbor(&bytes)
                .is_err()
        );
    }
}

#[test]
fn source_checks_can_use_canonical_prepared_libraries_explicitly() {
    let library = Library::prepared_sources_with_format(
        vec![(
            "library.kerml".into(),
            "package L { datatype Number; feature x = if true ? 7 else 8; }".into(),
        )],
        None,
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    let sources = vec![(
        "model.sysml".into(),
        "package P { attribute x : L::Number; }".into(),
    )];
    assert!(
        sysmlv2_transform::check_sources_with_graph_format(
            &sources,
            Some(&library),
            GraphFormat::CanonicalV3,
        )
        .is_ok()
    );
    assert!(sysmlv2_transform::check_sources_with_library(&sources, Some(&library)).is_err());
}

#[test]
fn canonical_delta_decoder_refuses_legacy_graph_hidden_under_canonical_stamp() {
    let base = session(GraphFormat::CanonicalV3, false, 7).to_compact_json();
    let bad_target = session(GraphFormat::LegacyV2, true, 8).to_compact_json();
    for portable in [false, true] {
        let mut bytes = sysmlv2_cbor::delta_compact_cbor(
            &base,
            &bad_target,
            &sysmlv2_cbor::DeltaOptions::new().with_portable(portable),
        )
        .unwrap();
        bytes[16] = 3;
        assert!(sysmlv2_cbor::apply_delta_cbor(&bytes, &base).is_err());
        if portable {
            assert!(sysmlv2_cbor::apply_delta_cbor_lenient(&bytes, &base).is_err());
        }
    }
}

#[test]
fn canonical_transport_refuses_contradictory_conditional_input_direction() {
    let original = session(GraphFormat::CanonicalV3, true, 7).to_compact_json();
    let rows = original.as_array().unwrap();
    let index_of = |reference: &serde_json::Value| {
        rows.iter()
            .position(|row| row["@id"] == reference["@id"])
            .unwrap()
    };
    let conditional = rows.iter().find(|row| row["operator"] == "if").unwrap();
    let membership = index_of(&conditional["ownedRelationship"][1]);
    let parameter = index_of(&rows[membership]["ownedRelatedElement"][0]);
    for direction in [
        serde_json::json!("out"),
        serde_json::json!("inout"),
        serde_json::Value::Null,
    ] {
        let mut malformed = original.clone();
        malformed[parameter]["direction"] = direction;
        assert!(
            Session::from_interchange_json_with_graph_format(
                &malformed,
                None,
                &["model.sysml".into()],
                Indent::default(),
                GraphFormat::CanonicalV3,
            )
            .is_err()
        );
        assert!(
            sysmlv2_cbor::to_compact_cbor_with_format(&malformed, &[], GraphFormat::CanonicalV3,)
                .is_err()
        );
        // Construct a validly encoded but falsely stamped payload through the
        // legacy codec to exercise decoder validation independently of encoding.
        let mut bytes = sysmlv2_cbor::to_compact_cbor(&malformed).unwrap();
        bytes[16] = 3;
        assert!(sysmlv2_cbor::from_compact_cbor(&bytes).is_err());
        let mut delta = sysmlv2_cbor::delta_compact_cbor(
            &original,
            &malformed,
            &sysmlv2_cbor::DeltaOptions::new(),
        )
        .unwrap();
        delta[16] = 3;
        assert!(sysmlv2_cbor::apply_delta_cbor(&delta, &original).is_err());
    }
}

#[test]
fn session_delta_generation_and_application_refuse_foreign_graph_bases() {
    for (source, target) in [
        (GraphFormat::LegacyV2, GraphFormat::CanonicalV3),
        (GraphFormat::CanonicalV3, GraphFormat::LegacyV2),
    ] {
        let foreign_base = session(source, true, 7).to_compact_json();
        let receiver = session(target, true, 8);
        assert!(receiver.delta_cbor_from(&foreign_base, false).is_err());
        assert!(receiver.delta_cbor_from(&foreign_base, true).is_err());
        assert!(receiver.delta_cbor_elided_from(&foreign_base).is_err());
        if target == GraphFormat::LegacyV2 {
            let bytes = sysmlv2_cbor::delta_compact_cbor(
                &foreign_base,
                &receiver.to_compact_json(),
                &sysmlv2_cbor::DeltaOptions::new(),
            )
            .unwrap();
            assert!(
                receiver
                    .apply_delta_cbor_to(&bytes, &foreign_base, false)
                    .is_err()
            );
        }
    }
}
