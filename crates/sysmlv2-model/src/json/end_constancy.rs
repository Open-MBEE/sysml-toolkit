//! Local constancy obligations over owned flags and checked Usage variability.
//! Canonical textual completion shares the checked Usage variability evidence.
use super::{ElementRef, ResolvedModel, UsageVariabilityIssue, structural_index::StoredStructure};
use crate::metaclass::conforms;

/// Why the local constancy obligations cannot be certified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum EndConstancyIssue {
    InvalidElement,
    InvalidBoolean(&'static str),
    UnsupportedConfiguration,
    StaleEvidence,
    WorkLimit,
    UsageVariability(UsageVariabilityIssue),
}

/// Results of the two independent KerML Feature constancy implications.
/// `Ok(false)` is a witnessed violation; an error is unavailable evidence.
/// Success does not certify ownership, featuring or whole-model validity.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct EndConstancyReport {
    /// `isEnd and isVariable implies isConstant`.
    pub variable_end_is_constant: Result<bool, EndConstancyIssue>,
    /// `isConstant implies isVariable` (also applies to non-end Features).
    pub constant_is_variable: Result<bool, EndConstancyIssue>,
    pub steps: usize,
}

impl EndConstancyReport {
    fn refused(issue: EndConstancyIssue, steps: usize) -> Self {
        Self {
            variable_end_is_constant: Err(issue),
            constant_is_variable: Err(issue),
            steps,
        }
    }
}

fn owned_boolean(
    r: &ResolvedModel,
    feature: ElementRef,
    key: &'static str,
) -> Result<bool, EndConstancyIssue> {
    // These three owned Feature declarations have a normative false default.
    // Absence and explicit false have the same implication truth, but neither
    // is rewritten as a textual/default repair. Explicit null is malformed.
    match r.b.elements[feature.0].props.get(key) {
        None => Ok(false),
        Some(value) => value
            .as_bool()
            .ok_or(EndConstancyIssue::InvalidBoolean(key)),
    }
}

impl ResolvedModel {
    /// Canonical textual defaults are completed only with shared variability
    /// evidence. Imported flags and explicit textual constant prefixes remain
    /// owned evidence, including inconsistent values diagnosed by the report.
    pub(crate) fn canonical_end_constant_with_budget(
        &mut self,
        feature: ElementRef,
        initial_steps: usize,
    ) -> Option<super::UsageVariabilityReport> {
        if !self.canonical_text_end(feature) {
            return None;
        }
        let steps = initial_steps.saturating_add(1);
        let stored = self.b.elements[feature.0].props.get("isConstant");
        let value = match stored {
            None => Ok(false),
            Some(value) => value
                .as_bool()
                .ok_or(UsageVariabilityIssue::InvalidBoolean("isConstant")),
        };
        if steps > crate::eval::MAX_STEPS {
            return Some(super::UsageVariabilityReport {
                value: Err(UsageVariabilityIssue::WorkLimit),
                steps,
            });
        }
        match value {
            Ok(false) => Some(self.usage_variability_report_with_budget(feature, steps)),
            value => Some(super::UsageVariabilityReport { value, steps }),
        }
    }

    /// Check the conditional constant-end and constant-variable obligations.
    ///
    /// Exact Features use their owned isVariable value/default. Usages use the
    /// shared mayTimeVary certificate for their effective isVariable declaration;
    /// stored derived aliases do not override that result. Other Feature kinds
    /// remain qualified. Malformed flags are refused before Boolean shortcuts.
    /// CanonicalV3 textual ends use the same proven completion as checked reads
    /// and emission. Imported flags are retained. This never mutates rows or certifies evaluability.
    pub fn end_constancy_report(&mut self, feature: ElementRef) -> EndConstancyReport {
        self.end_constancy_report_with_budget(feature, 0)
    }

    pub(in crate::json) fn end_constancy_report_with_budget(
        &mut self,
        feature: ElementRef,
        initial_steps: usize,
    ) -> EndConstancyReport {
        use EndConstancyIssue::*;
        let mut steps = initial_steps.saturating_add(4);
        if steps > crate::eval::MAX_STEPS {
            return EndConstancyReport::refused(WorkLimit, steps);
        }
        let Some(row) = self.b.elements.get(feature.0) else {
            return EndConstancyReport::refused(InvalidElement, steps);
        };
        let usage = conforms(row.ty, "Usage");
        if row.ty != "Feature" && !usage {
            return EndConstancyReport::refused(UnsupportedConfiguration, steps);
        }
        if self.b.positional_planning {
            return EndConstancyReport::refused(UnsupportedConfiguration, steps);
        }
        let flags = (|| {
            Ok((
                owned_boolean(self, feature, "isEnd")?,
                owned_boolean(self, feature, "isConstant")?,
                owned_boolean(self, feature, "isVariable")?,
            ))
        })();
        let (is_end, constant, owned_variable) = match flags {
            Ok(flags) => flags,
            Err(issue) => return EndConstancyReport::refused(issue, steps),
        };
        let Some(structure) = StoredStructure::for_query(&mut self.b, &mut steps) else {
            return EndConstancyReport::refused(
                if steps > crate::eval::MAX_STEPS {
                    WorkLimit
                } else {
                    InvalidElement
                },
                steps,
            );
        };
        if !structure.ids_unique {
            return EndConstancyReport::refused(InvalidElement, steps);
        }
        let variable = if usage {
            let report = self.usage_variability_report_with_budget(feature, steps);
            steps = report.steps;
            match report.value {
                // Malformed retained input is not a missing optional dependency.
                Err(UsageVariabilityIssue::InvalidBoolean(key)) => {
                    return EndConstancyReport::refused(InvalidBoolean(key), steps);
                }
                Err(
                    issue @ (UsageVariabilityIssue::InvalidElement
                    | UsageVariabilityIssue::InvalidOwnership),
                ) => {
                    return EndConstancyReport::refused(UsageVariability(issue), steps);
                }
                result => result.map_err(UsageVariability),
            }
        } else {
            Ok(owned_variable)
        };
        if steps > crate::eval::MAX_STEPS {
            return EndConstancyReport::refused(WorkLimit, steps);
        }
        if !structure.is_current(&self.b) {
            return EndConstancyReport::refused(StaleEvidence, steps);
        }
        if self.canonical_text_end(feature) && !constant {
            // Completion is conditional on this exact certificate. Unknown
            // evidence cannot certify either implication via a stored false.
            return EndConstancyReport {
                variable_end_is_constant: variable.map(|_| true),
                constant_is_variable: variable.map(|_| true),
                steps,
            };
        }
        EndConstancyReport {
            variable_end_is_constant: if !is_end || constant {
                Ok(true)
            } else {
                variable.map(|variable| !variable)
            },
            constant_is_variable: if !constant { Ok(true) } else { variable },
            steps,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::{GraphFormat, Model};
    use serde_json::json;

    fn feature() -> (ResolvedModel, ElementRef) {
        let mut model = Model::new();
        assert!(
            model
                .add_source("flags.kerml", "feature x;")
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let x = r.resolve_qualified("x").unwrap();
        (r, x)
    }

    fn canonical(source: &str) -> Model {
        let mut model = Model::with_graph_format(GraphFormat::CanonicalV3);
        model.add_library_source(
            "links.kerml",
            "standard library package Links { assoc SelfLink; }",
        );
        let result = model.add_source("ends.sysml", source);
        assert!(result.diagnostics.is_empty(), "{:?}", result.diagnostics);
        model
    }

    fn named_row(document: &serde_json::Value) -> &serde_json::Value {
        document
            .as_array()
            .unwrap()
            .iter()
            .find(|row| row["declaredName"] == "x")
            .unwrap()
    }

    #[test]
    fn canonical_excluded_end_uses_proven_false_across_reads_and_emission() {
        let model = canonical("part def P { end ref x : Links::SelfLink; }");
        let mut r = ResolvedModel::build(&model);
        let x = r.resolve_qualified("P::x").unwrap();
        let before = r.element_properties(x);
        assert_eq!(r.usage_variability_report(x).value, Ok(false));
        assert_eq!(r.property(x, "isConstant"), Ok(json!(false)));
        let report = r.end_constancy_report(x);
        assert_eq!(report.variable_end_is_constant, Ok(true));
        assert_eq!(report.constant_is_variable, Ok(true));
        assert_eq!(
            named_row(&super::super::model_to_compact_json(&model))["isConstant"],
            false
        );
        let full = crate::full::model_to_full_json(&model);
        for property in ["isConstant", "isVariable", "mayTimeVary"] {
            assert_eq!(named_row(&full)[property], false, "{property}");
        }
        assert_eq!(r.element_properties(x), before);
        assert!(matches!(
            r.canonical_end_constant_with_budget(x, crate::eval::MAX_STEPS)
                .unwrap()
                .value,
            Err(UsageVariabilityIssue::WorkLimit)
        ));
        assert_eq!(r.property(x, "isConstant"), Ok(json!(false)));
    }

    #[test]
    fn canonical_unknown_end_stays_qualified_and_never_acquires_blanket_true() {
        let model = canonical("part def P { end ref x; }");
        let mut r = ResolvedModel::build(&model);
        let x = r.resolve_qualified("P::x").unwrap();
        assert!(matches!(
            r.property(x, "isConstant"),
            Err(super::super::PropertyError::IncompleteUsageVariability(_))
        ));
        assert!(r.end_constancy_report(x).constant_is_variable.is_err());
        assert!(r.end_constancy_report(x).variable_end_is_constant.is_err());
        for doc in [
            super::super::model_to_compact_json(&model),
            crate::full::model_to_full_json(&model),
        ] {
            assert_eq!(named_row(&doc)["isConstant"], false);
            assert_ne!(named_row(&doc)["mayTimeVary"], true);
            assert_ne!(named_row(&doc)["isVariable"], true);
        }
        let errors = r.to_full_json_strict().unwrap_err();
        assert!(
            errors
                .issues
                .iter()
                .any(|issue| issue.element_id == r.element_id(x) && issue.property == "isConstant")
        );
    }

    #[test]
    fn canonical_payload_flags_remain_owned_across_rebuild_and_new_source_units() {
        use std::collections::HashMap;
        for constant in [
            None,
            Some(json!(false)),
            Some(json!(true)),
            Some(json!(null)),
        ] {
            let mut doc = super::super::model_to_compact_json(&canonical(
                "part def P { end ref x : Links::SelfLink; }",
            ));
            let row = doc
                .as_array_mut()
                .unwrap()
                .iter_mut()
                .find(|row| row["declaredName"] == "x")
                .unwrap();
            row.as_object_mut().unwrap().remove("isConstant");
            if let Some(value) = &constant {
                row["isConstant"] = value.clone();
            }
            let (mut model, mut loaded, _, _) = crate::loader::load_document_with_format(
                &doc,
                &HashMap::new(),
                GraphFormat::CanonicalV3,
            )
            .unwrap();
            let x = loaded.resolve_qualified("P::x").unwrap();
            assert!(!loaded.canonical_text_end(x));
            if constant.as_ref().is_some_and(serde_json::Value::is_null) {
                assert!(loaded.property(x, "isConstant").is_err());
            } else {
                assert_eq!(
                    loaded.property(x, "isConstant"),
                    Ok(constant.clone().unwrap_or(json!(false)))
                );
                if constant == Some(json!(true)) {
                    // The library is intentionally absent on this imported
                    // graph, so the retained inconsistency is not guessed.
                    assert!(loaded.end_constancy_report(x).constant_is_variable.is_err());
                }
            }
            model.add_library_source("extra.kerml", "package Extra { class C; }");
            model.add_source("new.sysml", "end ref y;");
            let mut rebuilt = ResolvedModel::build(&model);
            let x = rebuilt.resolve_qualified("P::x").unwrap();
            let y = rebuilt.resolve_qualified("y").unwrap();
            assert!(!rebuilt.canonical_text_end(x));
            assert!(rebuilt.canonical_text_end(y));
            let full = crate::full::model_to_full_json(&model);
            assert_eq!(
                named_row(&full)["isConstant"],
                constant.unwrap_or(json!(false))
            );
        }
    }

    #[test]
    fn canonical_text_provenance_survives_prepared_library_paths() {
        use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
        use std::sync::Arc;
        let mut base = Model::with_graph_format(GraphFormat::CanonicalV3);
        base.add_library_source(
            "base.kerml",
            "standard library package Base { classifier Anything; feature things : Anything; } standard library package Links { assoc SelfLink; }",
        );
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(151).unwrap(), 151).unwrap());
        for mode in 0..4 {
            let mut model = Model::with_graph_format(GraphFormat::CanonicalV3);
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("base.kerml", "standard library package Base { classifier Anything; feature things : Anything; } standard library package Links { assoc SelfLink; }");
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            model.add_source("ends.sysml", "part def P { end ref x : Links::SelfLink; }");
            let mut r = ResolvedModel::build(&model);
            let x = r.resolve_qualified("P::x").unwrap();
            assert!(r.canonical_text_end(x));
            assert_eq!(r.property(x, "isConstant"), Ok(json!(false)));
            assert_eq!(
                named_row(&crate::full::model_to_full_json(&model))["isConstant"],
                false
            );
        }
    }

    #[test]
    fn exact_feature_truth_table_preserves_rows_and_same_length_edits() {
        let (mut r, x) = feature();
        for end in [false, true] {
            for variable in [false, true] {
                for constant in [false, true] {
                    r.b.set(x.0, "isEnd", json!(end));
                    r.b.set(x.0, "isVariable", json!(variable));
                    r.b.set(x.0, "isConstant", json!(constant));
                    let before = r.element_properties(x);
                    let count = r.b.elements.len();
                    let report = r.end_constancy_report(x);
                    assert_eq!(
                        report.variable_end_is_constant,
                        Ok(!end || !variable || constant)
                    );
                    assert_eq!(report.constant_is_variable, Ok(!constant || variable));
                    assert_eq!(r.element_properties(x), before);
                    assert_eq!(r.b.elements.len(), count);
                }
            }
        }
    }

    #[test]
    fn defaults_are_false_and_malformed_flags_precede_shortcuts() {
        let (mut r, x) = feature();
        for key in ["isEnd", "isVariable", "isConstant"] {
            r.b.elements[x.0]
                .props
                .entries
                .make_mut()
                .retain(|(k, _)| k.name() != key);
        }
        let report = r.end_constancy_report(x);
        assert_eq!(report.variable_end_is_constant, Ok(true));
        assert_eq!(report.constant_is_variable, Ok(true));
        for key in ["isEnd", "isVariable", "isConstant"] {
            for value in [serde_json::Value::Null, json!("false"), json!(0), json!([])] {
                r.b.set(x.0, key, value);
                let report = r.end_constancy_report(x);
                assert_eq!(
                    report.variable_end_is_constant,
                    Err(EndConstancyIssue::InvalidBoolean(key))
                );
                assert_eq!(
                    report.constant_is_variable,
                    Err(EndConstancyIssue::InvalidBoolean(key))
                );
                r.b.elements[x.0]
                    .props
                    .entries
                    .make_mut()
                    .retain(|(k, _)| k.name() != key);
            }
        }
    }

    #[test]
    fn work_and_identity_failures_do_not_poison_retry() {
        let (mut r, x) = feature();
        let report = r.end_constancy_report_with_budget(x, crate::eval::MAX_STEPS);
        assert_eq!(
            report.variable_end_is_constant,
            Err(EndConstancyIssue::WorkLimit)
        );
        assert_eq!(
            report.constant_is_variable,
            Err(EndConstancyIssue::WorkLimit)
        );
        assert!(r.end_constancy_report(x).constant_is_variable.is_ok());
        let other = r.b.elements[0].id;
        let original = r.b.elements[x.0].id;
        r.b.elements[x.0].id = other;
        assert_eq!(
            r.end_constancy_report(x).constant_is_variable,
            Err(EndConstancyIssue::InvalidElement)
        );
        r.b.elements[x.0].id = original;
        assert!(r.end_constancy_report(x).constant_is_variable.is_ok());
    }

    #[test]
    fn usage_uses_checked_variability_instead_of_stored_aliases() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut model = Model::with_graph_format(format);
            assert!(
                model
                    .add_source("root.sysml", "ref x;")
                    .diagnostics
                    .is_empty()
            );
            let mut r = ResolvedModel::build(&model);
            let x = r.resolve_qualified("x").unwrap();
            r.b.set(x.0, "isEnd", json!(true));
            r.b.set(x.0, "isConstant", json!(true));
            r.b.set(x.0, "isVariable", json!(true));
            r.b.set(x.0, "mayTimeVary", json!(true));
            assert_eq!(r.usage_variability_report(x).value, Ok(false));
            let before = r.element_properties(x);
            let report = r.end_constancy_report(x);
            assert_eq!(report.variable_end_is_constant, Ok(true));
            assert_eq!(report.constant_is_variable, Ok(false));
            assert_eq!(r.element_properties(x), before);
            r.b.set(x.0, "mayTimeVary", json!(null));
            assert_eq!(
                r.end_constancy_report(x).constant_is_variable,
                Err(EndConstancyIssue::InvalidBoolean("mayTimeVary"))
            );
        }
    }

    #[test]
    fn unknown_usage_variability_cannot_become_a_missing_false() {
        let mut model = Model::new();
        assert!(
            model
                .add_source("unknown.sysml", "part def P { ref x; }")
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let x = r.resolve_qualified("P::x").unwrap();
        assert!(r.usage_variability_report(x).value.is_err());
        r.b.set(x.0, "isEnd", json!(true));
        r.b.set(x.0, "isConstant", json!(false));
        let report = r.end_constancy_report(x);
        assert!(report.variable_end_is_constant.is_err());
        assert_eq!(report.constant_is_variable, Ok(true));
        r.b.set(x.0, "isConstant", json!(true));
        let report = r.end_constancy_report(x);
        assert_eq!(report.variable_end_is_constant, Ok(true));
        assert!(report.constant_is_variable.is_err());
    }

    #[test]
    fn positive_usage_variability_ignores_false_derived_aliases() {
        let mut model = Model::new();
        assert!(model.add_library_source("roles.kerml", "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; assoc HappensLink specializes Base::Anything;} standard library package Links {assoc SelfLink specializes Base::Anything;}").diagnostics.is_empty());
        assert!(
            model
                .add_source(
                    "positive.sysml",
                    "part def P :> Occurrences::Occurrence { ref x :> Base::things; }"
                )
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let x = r.resolve_qualified("P::x").unwrap();
        r.b.set(x.0, "isConstant", json!(true));
        r.b.set(x.0, "isVariable", json!(false));
        r.b.set(x.0, "mayTimeVary", json!(false));
        let report = r.end_constancy_report(x);
        assert_eq!(report.variable_end_is_constant, Ok(true));
        assert_eq!(report.constant_is_variable, Ok(true));
        let p = r.resolve_qualified("P").unwrap();
        assert_eq!(
            r.end_constancy_report(p).constant_is_variable,
            Err(EndConstancyIssue::UnsupportedConfiguration)
        );
        assert_eq!(
            r.end_constancy_report(ElementRef(usize::MAX))
                .constant_is_variable,
            Err(EndConstancyIssue::InvalidElement)
        );
    }
}
