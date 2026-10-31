//! Every integration test of this crate, built as one test binary: one
//! link and one set of shared instantiations instead of one per file, and
//! one test pool across all of them. Each file under `tests/` joins as a
//! module below, unless it needs a process of its own (Cargo.toml then
//! gives it a test target of its own); `every_test_file_is_declared`
//! fails for a file in neither place. One file's tests:
//! `cargo test -p sysmlv2-solve --test integration apollo::`.

// Fixtures that the propagation and native-solving tests share.
#[path = "common/collection_identity.rs"]
mod collection_identity;

mod apollo;
mod corpus;
mod environment_identity;
mod prepared;
mod propagate;
mod propagation_approximation;
mod runtime_frame_visibility;
mod solve;
mod source_identity;
mod source_identity_chains;
mod value_receiver_identity;

#[test]
fn every_test_file_is_declared() {
    sysmlv2_testkit::assert_suite_declares_every_test_file(
        env!("CARGO_MANIFEST_DIR"),
        include_str!("integration.rs"),
    );
}
