//! Every integration test of this crate, built as one test binary: one
//! link and one set of shared instantiations instead of one per file, and
//! one test pool across all of them. Each file under `tests/` joins as a
//! module below, unless it needs a process of its own (Cargo.toml then
//! gives it a test target of its own); `every_test_file_is_declared`
//! fails for a file in neither place. One file's tests:
//! `cargo test -p sysmlv2-transform --test integration cardinality_identity::`.

mod cardinality_identity;
mod cbor_session;
mod compact_emission;
mod eligibility;
mod exposure_roundtrip;
mod extract;
mod format_transport_adversarial;
mod full_json_policy;
mod graph_format;
mod inherited_lookup_provenance;
mod inline;
mod insert_at;
mod insert_order;
mod json_path;
mod library_reference_spelling;
mod library_subjects;
mod line_endings;
mod minimize;
mod parsed_sources;
mod payload_loader;
mod prepared_sources;
mod projection;
mod refusal_message;
mod settled_outcomes;
mod store_head_delta;
mod store_to_store_delta;
mod text_confinement;
mod text_reference_spelling;
mod transform;
mod type_inputs;
mod unused_imports;

#[test]
fn every_test_file_is_declared() {
    sysmlv2_testkit::assert_suite_declares_every_test_file(
        env!("CARGO_MANIFEST_DIR"),
        include_str!("integration.rs"),
    );
}
