use sysmlv2_cbor::{from_compact_cbor, from_full_cbor, to_compact_cbor, to_full_cbor};
use sysmlv2_parser::{
    full::{EmissionPolicy, UnresolvedReferencePolicy, resolved_to_full_json},
    json::{ClosurePolicy, ResolvedModel, model_to_compact_json},
    model::Model,
};

#[test]
fn connector_end_owned_defaults_survive_full_cbor_without_changing_source_transport() {
    let mut model = Model::new();
    assert!(
        model
            .add_source(
                "ends.kerml",
                "class A { end feature x; end feature y; connector c from x to y; }"
            )
            .diagnostics
            .is_empty()
    );
    let compact = model_to_compact_json(&model);
    let source_bytes = to_compact_cbor(&compact).unwrap();
    assert_eq!(from_compact_cbor(&source_bytes).unwrap(), compact);
    let mut resolved = ResolvedModel::build(&model);
    for closures in [
        ClosurePolicy::Passthrough,
        ClosurePolicy::Closure {
            include_implied: false,
        },
        ClosurePolicy::Closure {
            include_implied: true,
        },
    ] {
        let full = resolved_to_full_json(
            &mut resolved,
            &model,
            EmissionPolicy {
                unresolved: UnresolvedReferencePolicy::Reject,
                closures,
            },
        )
        .unwrap();
        let decoded = from_full_cbor(&to_full_cbor(&full).unwrap()).unwrap();
        assert_eq!(decoded, full);
        let ends = decoded
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["@type"] == "Feature" && row["isEnd"] == true)
            .collect::<Vec<_>>();
        assert_eq!(ends.len(), 4);
        assert!(ends.iter().all(|row| row["isConstant"] == false));
        assert_eq!(
            decoded
                .as_array()
                .unwrap()
                .iter()
                .map(|row| row["@id"].clone())
                .collect::<Vec<_>>(),
            compact
                .as_array()
                .unwrap()
                .iter()
                .map(|row| row["@id"].clone())
                .collect::<Vec<_>>()
        );
        assert_eq!(
            to_compact_cbor(&model_to_compact_json(&model)).unwrap(),
            source_bytes
        );
    }
}
