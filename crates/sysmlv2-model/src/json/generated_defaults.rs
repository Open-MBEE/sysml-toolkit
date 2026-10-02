//! Owned defaults for newly generated Feature-family full-form records.
//! This is serialization of declared defaults, not a semantic completeness
//! certificate. Source rows and the historical generic relationship rows do
//! not use this projection.
use crate::{properties::Properties, semantic_catalog};
use serde_json::{Map, Value};

pub(super) fn fill_owned_defaults(ty: &str, stored: &Properties, record: &mut Map<String, Value>) {
    let Some(properties) = semantic_catalog::properties(ty) else {
        return;
    };
    for &(requested, effective) in properties {
        let requested = &semantic_catalog::PROPERTIES[usize::from(requested)];
        let name = requested.name;
        let Some(spec) = semantic_catalog::PROPERTIES.get(usize::from(effective)) else {
            continue;
        };
        if spec.derived
            || record.contains_key(name)
            || spec
                .storage_names
                .iter()
                .any(|name| stored.get(name).is_some())
        {
            continue;
        }
        let Some(default) = spec.default_json else {
            continue;
        };
        let Ok(value) = serde_json::from_str(default) else {
            continue;
        };
        let Ok(value) = super::semantic::reshape(value, requested) else {
            continue;
        };
        record.insert(name.into(), value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn feature_defaults_match_owned_declarations_without_derived_guesses() {
        let stored = Properties::new();
        let mut record = Map::new();
        fill_owned_defaults("Feature", &stored, &mut record);
        assert_eq!(record["isUnique"], true);
        for name in [
            "isAbstract",
            "isSufficient",
            "isComposite",
            "isOrdered",
            "isEnd",
            "isConstant",
            "isDerived",
            "isPortion",
            "isVariable",
        ] {
            assert_eq!(record[name], false, "{name}");
        }
        for name in [
            "isConjugated",
            "direction",
            "type",
            "owningType",
            "multiplicity",
        ] {
            assert!(!record.contains_key(name), "{name}");
        }
    }
    #[test]
    fn explicit_values_and_nulls_are_preserved_and_effective_defaults_win() {
        let mut stored = Properties::new();
        stored.insert("isUnique", serde_json::json!(false));
        stored.insert("isAbstract", Value::Null);
        let mut record = stored.to_json();
        fill_owned_defaults("Feature", &stored, &mut record);
        assert_eq!(record["isUnique"], false);
        assert!(record["isAbstract"].is_null());
        let stored = Properties::new();
        let mut record = Map::new();
        fill_owned_defaults("ConnectionDefinition", &stored, &mut record);
        assert_eq!(
            record["isSufficient"], true,
            "effective ConnectionDefinition override wins over Type=false"
        );
    }
}

#[cfg(test)]
mod model_tests {
    use crate::{
        json::{ClosurePolicy, Derived, ResolvedModel},
        model::Model,
    };
    #[test]
    fn generated_feature_full_record_matches_checked_owned_defaults_and_keeps_source_sparse() {
        let mut model = Model::new();
        model.add_library_source("defaults-library.kerml","standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;}");
        assert!(
            model
                .add_source(
                    "defaults-user.kerml",
                    "class A; feature referent; feature read=referent;"
                )
                .diagnostics
                .is_empty()
        );
        let compact = crate::json::model_to_compact_json(&model);
        let mut r = ResolvedModel::build(&model);
        let authored: Vec<_> = r
            .elements()
            .map(|e| (r.element_id(e), r.element_properties(e)))
            .collect();
        let expr = r
            .elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let result = match r.derived(expr, "result") {
            Derived::Value(v) => v.element().unwrap(),
            v => panic!("{v:?}"),
        };
        let result_id = r.element_id(result).to_string();
        let record = r.generated_node_record(result).unwrap();
        for name in [
            "isUnique",
            "isAbstract",
            "isSufficient",
            "isComposite",
            "isOrdered",
            "isEnd",
            "isConstant",
            "isDerived",
            "isPortion",
            "isVariable",
        ] {
            assert_eq!(record[name], r.property(result, name).unwrap(), "{name}");
            assert!(
                !r.element_properties(result).contains_key(name),
                "serialization must not mutate storage"
            );
        }
        assert_eq!(record["direction"], "out");
        assert!(!record.contains_key("isConjugated"));
        let a = r.resolve_qualified("A").unwrap();
        let generic = r
            .implied_relationships(a)
            .into_iter()
            .find(|&e| r.element_type(e) == "Subclassification")
            .unwrap();
        let generic_record = r.generated_node_record(generic).unwrap();
        assert_eq!(generic_record["isImplied"], true);
        assert!(!generic_record.contains_key("visibility"));
        assert!(!generic_record.contains_key("isUnique"));
        let full = crate::full::resolved_to_full_json(
            &mut r,
            &model,
            crate::full::EmissionPolicy {
                closures: ClosurePolicy::Closure {
                    include_implied: true,
                },
                ..Default::default()
            },
        )
        .unwrap();
        let full_result = full
            .as_array()
            .unwrap()
            .iter()
            .find(|v| v["@id"] == result_id)
            .unwrap();
        for name in ["isUnique", "isAbstract", "isOrdered"] {
            assert_eq!(full_result[name], record[name]);
        }
        let ends: Vec<_> = full
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["@type"] == "Feature" && row["isEnd"] == true)
            .collect();
        assert_eq!(ends.len(), 2);
        for row in ends {
            let end = r.element_by_id(row["@id"].as_str().unwrap()).unwrap();
            assert_eq!(r.property(end, "isVariable").unwrap(), false);
            assert_eq!(r.property(end, "isConstant").unwrap(), false);
            assert_eq!(row["isVariable"], false);
            assert_eq!(row["isConstant"], false);
            assert!(!r.element_properties(end).contains_key("isConstant"));
        }
        assert_eq!(crate::json::model_to_compact_json(&model), compact);
        assert_eq!(
            r.elements()
                .map(|e| (r.element_id(e), r.element_properties(e)))
                .collect::<Vec<_>>(),
            authored
        );
    }
    #[test]
    fn nonunique_ordered_referent_does_not_fabricate_result_flag_inheritance() {
        let mut model = Model::new();
        assert!(
            model
                .add_source(
                    "collection-defaults.kerml",
                    "feature referent[*] ordered nonunique; feature read=referent;"
                )
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let referent = r.resolve_qualified("referent").unwrap();
        assert_eq!(r.property(referent, "isUnique").unwrap(), false);
        assert_eq!(r.property(referent, "isOrdered").unwrap(), true);
        let expr = r
            .elements()
            .find(|&e| r.element_type(e) == "FeatureReferenceExpression")
            .unwrap();
        let result = match r.derived(expr, "result") {
            Derived::Value(v) => v.element().unwrap(),
            v => panic!("{v:?}"),
        };
        let record = r.generated_node_record(result).unwrap();
        assert_eq!(record["isUnique"], r.property(result, "isUnique").unwrap());
        assert_eq!(
            record["isOrdered"],
            r.property(result, "isOrdered").unwrap()
        );
        assert_eq!(record["isUnique"], true);
        assert_eq!(record["isOrdered"], false);
        // This records the current graph's defaults. Correct collection-value
        // preservation by the result/Binding family remains a separate audit;
        // Subsetting's one-way uniqueness constraint is not flag inheritance.
    }
}
