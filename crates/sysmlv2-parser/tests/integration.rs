//! Every integration test of this crate, built as one test binary: one
//! link and one set of shared instantiations instead of one per file, and
//! one test pool across all of them. Each file under `tests/` joins as a
//! module below, unless it needs a process of its own (Cargo.toml then
//! gives it a test target of its own); `every_test_file_is_declared`
//! fails for a file in neither place. One file's tests:
//! `cargo test -p sysmlv2-parser --test integration annotation_precision::`.

mod accept_trigger;
mod annex_a_resolution;
mod annotation_precision;
mod apollo;
mod binary_connection_bases;
mod cardinality_body;
mod cardinality_context;
mod cardinality_subject;
mod certified_type_properties;
mod check;
mod checked_authored_prerequisites;
mod checked_cardinality;
mod checked_chain_scopes;
mod checked_constructors;
mod checked_definition_usage;
mod checked_end_contexts;
mod checked_expression_receivers;
mod checked_import_planning;
mod checked_metadata_receivers;
mod checked_owned_relationships;
mod checked_owner_contexts;
mod checked_owner_roles;
mod checked_parameter_prerequisites;
mod checked_positional_prerequisites;
mod checked_receiver_flags;
mod checked_recursive_providers;
mod checked_structural_members;
mod checked_structure_properties;
mod checked_type_imports;
mod checked_type_memberships;
mod checked_usage_receivers;
mod checked_usage_typing;
mod checked_visible_prerequisites;
mod checker_identity;
mod closure_policy;
mod conformance_operations;
mod connector_bound_scopes;
mod connector_end_bindings;
mod connector_end_references;
mod connector_relationship_ends;
mod constructor_static_evaluation;
mod corpus;
mod corpus_identity;
mod cross_feature_operations;
mod cross_feature_scopes;
mod default_featuring_identity;
mod default_multiplicity;
mod derived_api;
mod derived_correspondence;
mod derived_parity;
mod determinism;
mod distinguishability;
mod dynamic_invocations;
mod effective_name_operation;
mod eval;
mod evaluation_operations;
mod exposure_context;
mod exposure_memberships;
mod expression_fixed_roles;
mod expression_generated_results;
mod expression_static_ancestry;
mod feature_chain_static_typing;
mod feature_library_bases;
mod feature_type_report;
mod filter_identity;
mod format;
mod full_baseline;
mod full_json;
mod fuzz;
mod goldens;
mod grammar_edge;
mod ids_derive;
mod implied_name_seams;
mod import_memberships;
mod inherited_base_context;
mod inherited_battery;
mod inherited_default_report;
mod inherited_lookup;
mod inherited_lookup_provenance;
mod instantiation_callee_typing;
mod json;
mod kerml;
mod lexer;
mod libcache;
mod literal_results;
mod meta_cast_chains;
mod metadata_about;
mod metadata_results;
mod model;
mod model_level_evaluability;
mod model_level_function_identity;
mod multiplicity_library_base;
mod multiplicity_validation;
mod naming_group_operations;
mod negative;
mod opensysml;
mod operations;
mod owned_result_featuring;
mod owned_result_redefinition;
mod owned_results;
mod parser;
mod positional_alias_memberships;
mod positional_members;
mod positional_redefinitions;
mod prepared_library;
mod qualified_positional_slots;
mod quantity;
mod query;
mod recorded_alias_paths;
mod recorded_lookup_effects;
mod redefinition_direction;
mod reference_bindings;
mod refs;
mod roundtrip;
mod sdk_semantic_regressions;
mod semantic_base_conformance;
mod semantic_names_reporting;
mod semantic_reads;
mod shared_implied_plan;
mod specialization_operations;
mod spelling;
mod state_target_transitions;
mod static_rules;
mod supertypes_operation;
mod sysml_assertion_roles;
mod transition_sources;
mod usage_operations;
mod visit;
mod xmi_audit;

#[test]
fn every_test_file_is_declared() {
    sysmlv2_testkit::assert_suite_declares_every_test_file(
        env!("CARGO_MANIFEST_DIR"),
        include_str!("integration.rs"),
    );
}
