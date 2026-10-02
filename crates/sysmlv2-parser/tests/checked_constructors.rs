//! Constructor obligations over the real standard library and replay paths.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{ModelLevelEvaluability, ResolvedModel},
    libcache::LibraryCache,
    model::{GraphFormat, Model},
    prepared::PreparedLibrary,
};

#[test]
fn checked_constructor_obligations_preserve_actual_library_replay_results() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        return;
    }
    let mut base = Model::with_graph_format(GraphFormat::CanonicalV3);
    base.load_library_dir(&library).unwrap();
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(149).unwrap(), 149).unwrap());
    let mut expected = None;
    for mode in 0..4 {
        let mut model = Model::with_graph_format(GraphFormat::CanonicalV3);
        match mode {
            2 => Arc::clone(&prepared).install(&mut model).unwrap(),
            3 => Arc::clone(&decoded).install(&mut model).unwrap(),
            _ => {
                model.load_library_dir(&library).unwrap();
                if mode == 1 {
                    model.set_library_cache(cache.clone());
                }
            }
        }
        let parsed = model.add_source(
            "checked-constructor.kerml",
            "class C {feature a; feature b default = 2;} feature instance=new C(1);",
        );
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let expressions: Vec<_> = r
            .user_elements()
            .filter(|&e| r.element_type(e) == "ConstructorExpression")
            .collect();
        assert_eq!(
            expressions.len(),
            1,
            "one user constructor valuation, mode {mode}"
        );
        let expression = expressions[0];
        r.implied_relationships(expression);
        let report = r.constructor_result_report(expression);
        let result = report
            .result
            .unwrap_or_else(|issue| panic!("mode {mode}: {issue:?}, steps {}", report.steps));
        assert_eq!(result.arguments.bindings.len(), 1, "mode {mode}");
        // A Class specializes Occurrences::Occurrence. Its eight inherited
        // defaults are result obligations as well as the locally omitted b.
        let expected_defaults: Vec<_> = [
            "C::b",
            "Occurrences::Occurrence::portionOfLife",
            "Occurrences::Occurrence::this",
            "Occurrences::Occurrence::localClock",
            "Occurrences::Occurrence::isDispatch",
            "Occurrences::Occurrence::dispatchScope",
            "Occurrences::Occurrence::isRunToCompletion",
            "Occurrences::Occurrence::runToCompletionScope",
            "Occurrences::Occurrence::incomingTransferSort",
        ]
        .into_iter()
        .map(|name| r.resolve_qualified(name).unwrap())
        .collect();
        assert_eq!(
            result
                .defaults
                .iter()
                .map(|binding| binding.feature)
                .collect::<Vec<_>>(),
            expected_defaults,
            "mode {mode}"
        );
        assert_eq!(
            result.arguments.bindings[0].feature,
            r.resolve_qualified("C::a").unwrap(),
            "mode {mode}"
        );
        assert_eq!(
            result.defaults[0].feature,
            r.resolve_qualified("C::b").unwrap(),
            "mode {mode}"
        );
        assert_eq!(
            r.model_level_evaluability(expression).classification,
            ModelLevelEvaluability::Evaluable,
            "mode {mode}"
        );
        let identities = (
            r.element_id(result.arguments.bindings[0].feature),
            result
                .defaults
                .iter()
                .map(|binding| {
                    (
                        r.element_id(binding.feature),
                        r.element_id(binding.feature_with_value),
                        r.element_id(binding.valuation),
                        r.element_id(binding.value),
                    )
                })
                .collect::<Vec<_>>(),
        );
        if let Some(expected) = &expected {
            assert_eq!(&identities, expected, "mode {mode}");
        } else {
            expected = Some(identities);
        }
        assert_eq!(
            r.constructor_result_report(expression).result.unwrap(),
            result,
            "warm mode {mode}"
        );
        if mode == 0 {
            let full = sysmlv2_parser::full::resolved_to_full_json_with_policy(
                &mut r,
                &model,
                sysmlv2_parser::full::UnresolvedReferencePolicy::Preserve,
            )
            .unwrap();
            let rows = full.as_array().unwrap();
            assert_eq!(
                rows.iter()
                    .filter(|row| row["@type"] == "BindingConnector" && row["isImplied"] == true)
                    .count(),
                9
            );
            let by_id: std::collections::HashMap<_, _> = rows
                .iter()
                .map(|row| (row["@id"].as_str().unwrap(), row))
                .collect();
            for connector in rows
                .iter()
                .filter(|row| row["@type"] == "BindingConnector" && row["isImplied"] == true)
            {
                let featuring: Vec<_> = rows
                    .iter()
                    .filter(|row| {
                        row["@type"] == "TypeFeaturing"
                            && row["featuringType"]["@id"] == connector["@id"]
                    })
                    .collect();
                assert_eq!(
                    featuring.len(),
                    2,
                    "each default connector has both end featuring relationships"
                );
                let mut sources = std::collections::HashSet::new();
                for relationship in featuring {
                    let source_id = relationship["featureOfType"]["@id"].as_str().unwrap();
                    assert!(sources.insert(source_id));
                    let source = by_id[source_id];
                    assert_eq!(source["isEnd"], true);
                    assert!(
                        source["ownedTypeFeaturing"]
                            .as_array()
                            .unwrap()
                            .iter()
                            .any(|reference| reference["@id"] == relationship["@id"])
                    );
                }
            }
            let schema: serde_json::Value = serde_json::from_str(
                &std::fs::read_to_string(
                    sysmlv2_testkit::workspace_root().join("spec-refs/SysML.schema.json"),
                )
                .unwrap(),
            )
            .unwrap();
            let mut validators = std::collections::HashMap::new();
            for row in rows {
                let kind = row["@type"].as_str().unwrap();
                let validator = validators.entry(kind.to_owned()).or_insert_with(|| {
                    let definition = &schema["$defs"][kind];
                    let mut exact = if definition.get("anyOf").is_some() {
                        definition["anyOf"][0].clone()
                    } else {
                        definition.clone()
                    };
                    exact["$defs"] = schema["$defs"].clone();
                    jsonschema::validator_for(&exact).unwrap()
                });
                let failures: Vec<_> = validator
                    .iter_errors(row)
                    .map(|error| error.to_string())
                    .collect();
                assert!(failures.is_empty(), "{kind}: {failures:?}");
            }
        }
    }
}
