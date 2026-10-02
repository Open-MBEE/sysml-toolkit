//! Source transport remains scheme 2; semantic result/binding nodes travel in full form.
use sysmlv2_cbor::{
    from_compact_cbor, from_compact_cbor_elided, from_full_cbor, to_compact_cbor,
    to_compact_cbor_elided, to_full_cbor,
};
use sysmlv2_parser::{
    full::{EmissionPolicy, UnresolvedReferencePolicy, resolved_to_full_json},
    json::{ClosurePolicy, ResolvedModel, model_to_compact_json},
    lift::from_compact_json,
    model::Model,
    print::print_source,
};

#[test]
fn owned_results_preserve_source_cbor_and_roundtrip_atomic_full_subtrees() {
    let mut model = Model::new();
    model.add_source("declarations.kerml", "package P {datatype T; feature n:T;}");
    model.add_source("references.kerml", "feature x=P::n; feature y=P::n;");
    assert!(!model.has_errors());
    let compact = model_to_compact_json(&model);
    let compact_bytes = to_compact_cbor(&compact).unwrap();
    let no_external =
        |name: &str| -> Option<String> { panic!("unexpected external reference {name}") };
    let elided_bytes = to_compact_cbor_elided(&compact, &no_external).unwrap();
    assert_eq!(from_compact_cbor(&compact_bytes).unwrap(), compact);
    assert_eq!(
        from_compact_cbor_elided(&elided_bytes, &no_external).unwrap(),
        compact
    );
    let expected_source = print_source(&from_compact_json(&compact).unwrap().unit);
    let mut resolved = ResolvedModel::build(&model);
    let expressions: Vec<_> = resolved
        .elements()
        .filter(|&e| resolved.element_type(e) == "FeatureReferenceExpression")
        .collect();
    assert_eq!(expressions.len(), 2);
    for policy in [
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
                closures: policy,
            },
        )
        .unwrap();
        assert_eq!(
            full.as_array().unwrap().len(),
            compact.as_array().unwrap().len() + 28
        );
        assert_eq!(
            full.as_array()
                .unwrap()
                .iter()
                .filter(|row| row["@type"] == "TypeFeaturing")
                .count(),
            6
        );
        let encoded = to_full_cbor(&full).unwrap();
        let decoded = from_full_cbor(&encoded).unwrap();
        assert_eq!(decoded, full);
        assert_eq!(
            print_source(&from_compact_json(&decoded).unwrap().unit),
            expected_source
        );
        assert_eq!(
            to_compact_cbor(&model_to_compact_json(&model)).unwrap(),
            compact_bytes
        );
        assert_eq!(
            to_compact_cbor_elided(&model_to_compact_json(&model), &no_external).unwrap(),
            elided_bytes
        );
    }
    assert_eq!(sysmlv2_cbor::ID_SCHEME_VERSION, 2);
    assert_eq!(sysmlv2_cbor::LAYOUT_VERSION, 1);
}

#[test]
fn full_binding_cbor_preserves_sysml_dialect() {
    let mut model = Model::new();
    model.add_source(
        "reference.sysml",
        "part def Container { attribute n; attribute x=n; }",
    );
    assert!(!model.has_errors());
    let compact = model_to_compact_json(&model);
    let expected = from_compact_json(&compact).unwrap();
    let full = sysmlv2_parser::full::model_to_full_json(&model);
    assert!(
        full.as_array()
            .unwrap()
            .iter()
            .any(|row| row["@type"] == "BindingConnector")
    );
    let decoded = from_full_cbor(&to_full_cbor(&full).unwrap()).unwrap();
    assert_eq!(decoded, full);
    let actual = from_compact_json(&decoded).unwrap();
    assert!(actual.errors.is_empty(), "{:?}", actual.errors);
    assert_eq!(actual.unit.dialect, sysmlv2_parser::ast::Dialect::Sysml);
    assert_eq!(print_source(&actual.unit), print_source(&expected.unit));
}
