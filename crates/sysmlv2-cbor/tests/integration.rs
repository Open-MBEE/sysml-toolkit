//! Every integration test of this crate, built as one test binary: one
//! link and one set of shared instantiations instead of one per file, and
//! one test pool across all of them. Each file under `tests/` joins as a
//! module below, unless it needs a process of its own (Cargo.toml then
//! gives it a test target of its own); `every_test_file_is_declared`
//! fails for a file in neither place. One file's tests:
//! `cargo test -p sysmlv2-cbor --test integration canonical::`.

mod canonical;
mod canonical_constructors;
mod conditional_graph;
mod connector_end_defaults;
mod delta;
mod describe;
mod determinism;
mod elide;
mod full_roundtrip;
mod fuzz;
mod index;
mod normalized_lift;
mod owned_results;
mod resolver;
mod roundtrip;
mod stream;
mod tables;
mod tables_twin;
mod units;

#[test]
fn every_test_file_is_declared() {
    sysmlv2_testkit::assert_suite_declares_every_test_file(
        env!("CARGO_MANIFEST_DIR"),
        include_str!("integration.rs"),
    );
}
