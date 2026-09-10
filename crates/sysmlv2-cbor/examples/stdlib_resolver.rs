//! Generate the standard-library resolver artifact:
//!
//!     cargo run -p sysmlv2-cbor --example stdlib_resolver -- <library-dir> > stdlib-resolver.json
//!
//! Pins the artifact to the library's compact-export state digest and
//! this build's codec table/scheme versions; `sysmlv2_cbor::resolver`
//! is the consumer side.

use sysmlv2_parser::json::{library_resolver_artifact, library_to_compact_json};
use sysmlv2_parser::model::Model;

fn main() {
    let dir = std::env::args()
        .nth(1)
        .expect("usage: stdlib_resolver <library-dir>");
    let mut model = Model::new();
    model.load_library_dir(dir.as_ref()).expect("library loads");
    let export = library_to_compact_json(&model);
    let digest = sysmlv2_cbor::state_digest(&export).expect("digests");
    let artifact = library_resolver_artifact(
        &model,
        &digest.to_string(),
        sysmlv2_cbor::tables::CBOR_TABLES_VERSION,
        sysmlv2_cbor::ID_SCHEME_VERSION,
        env!("CARGO_PKG_VERSION"),
    );
    println!("{}", serde_json::to_string(&artifact).unwrap());
}
