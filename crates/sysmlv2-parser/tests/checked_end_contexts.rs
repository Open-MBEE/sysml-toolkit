//! Checked end completion preserves its supported ownership boundary across replay.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{ClosurePolicy, PropertyError, ResolvedModel, UsageVariabilityIssue},
    libcache::LibraryCache,
    model::{GraphFormat, Model},
    prepared::PreparedLibrary,
};

#[test]
fn typed_occurrence_ends_and_positional_redefinitions_preserve_replay_evidence() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        return;
    }
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut base = Model::with_graph_format(format);
        base.load_library_dir(&library).unwrap();
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(73).unwrap(), 73).unwrap());
        let mut expected_ids = None;
        for mode in 0..4 {
            let mut model = Model::with_graph_format(format);
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
            let unit = model.add_source(
                "checked-ends.sysml",
                "occurrence def Ends {\n\
                    end item itemEnd : Items::Item;\n\
                    end part partEnd : Parts::Part;\n\
                    end ref referenceEnd : Items::Item :> Objects::objects;\n\
                 }\n\
                 occurrence def Refined :> Ends {\n\
                    end item itemEnd; end part partEnd;\n\
                    end ref referenceEnd : Items::Item :> Objects::objects;\n\
                 }\n\
                 part def ContextualOwner {end item itemEnd;}\n\
                 part def MissingType {end item itemEnd : Missing;}\n\
                 occurrence def TypedReference {end ref typedEnd : Items::Item;}",
            );
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            let mut resolved = ResolvedModel::build(&model);
            resolved.set_closure_policy(ClosurePolicy::Closure {
                include_implied: true,
            });
            let ids: Vec<_> = resolved
                .user_elements()
                .map(|e| resolved.element_id(e))
                .collect();
            if let Some(expected) = &expected_ids {
                assert_eq!(&ids, expected, "{format:?} replay {mode}");
            } else {
                expected_ids = Some(ids.clone());
            }
            for name in [
                "Ends::itemEnd",
                "Ends::partEnd",
                "Ends::referenceEnd",
                "Refined::itemEnd",
                "Refined::partEnd",
                "Refined::referenceEnd",
                "ContextualOwner::itemEnd",
            ] {
                let end = resolved.resolve_qualified(name).unwrap();
                let owned = resolved.element_properties(end);
                let report = resolved.usage_variability_report(end);
                assert_eq!(report.value, Ok(true), "{format:?} replay {mode}: {name}");
                for property in ["isVariable", "mayTimeVary"] {
                    assert_eq!(resolved.property(end, property), Ok(true.into()));
                }
                let constant = resolved.property(end, "isConstant");
                if format == GraphFormat::CanonicalV3 {
                    assert_eq!(constant, Ok(true.into()));
                    let obligations = resolved.end_constancy_report(end);
                    assert_eq!(obligations.variable_end_is_constant, Ok(true));
                    assert_eq!(obligations.constant_is_variable, Ok(true));
                } else {
                    assert_eq!(constant, Err(PropertyError::NotComputed));
                }
                assert_eq!(resolved.element_properties(end), owned);
            }
            // An unresolved type cannot certify the end's specialization
            // exclusions, even under a supported structural owner.
            let unresolved_end = resolved.resolve_qualified("MissingType::itemEnd").unwrap();
            assert_eq!(
                resolved.usage_variability_report(unresolved_end).value,
                Err(UsageVariabilityIssue::IncompleteSpecialization),
                "{format:?} replay {mode}: MissingType::itemEnd"
            );
            assert!(resolved.property(unresolved_end, "isConstant").is_err());
            let typed = resolved
                .resolve_qualified("TypedReference::typedEnd")
                .unwrap();
            if format == GraphFormat::CanonicalV3 {
                assert_eq!(resolved.usage_variability_report(typed).value, Ok(true));
                assert_eq!(resolved.property(typed, "isConstant"), Ok(true.into()));
            } else {
                assert_eq!(
                    resolved.usage_variability_report(typed).value,
                    Err(UsageVariabilityIssue::IncompleteSpecialization)
                );
            }
            assert_eq!(
                ids,
                resolved
                    .user_elements()
                    .map(|e| resolved.element_id(e))
                    .collect::<Vec<_>>()
            );
        }
    }
}
