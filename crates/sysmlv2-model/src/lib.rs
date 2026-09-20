//! Semantic model layer for the OMG SysML v2 / KerML stack: lowers the
//! syntax AST (`sysmlv2-syntax`) to the abstract-syntax element graph with
//! name resolution and deterministic/normative element IDs, serializes the
//! JSON interchange forms (compact + full, KerML 10.4), reads them back,
//! holds multi-file models resolved against the OMG standard library, runs
//! referential checks, and evaluates expressions.

pub mod ambient;
mod cache_codec;
pub mod cbor_tables;
pub mod check;
mod derived_names;
pub mod eval;
pub mod full;
pub mod ids;
pub mod json;
mod layered;
pub mod libcache;
pub mod lift;
pub mod loader;
mod metaclass;

/// The canonical (`'static`) spelling of an abstract-syntax metaclass
/// name, `None` for a name the metamodel does not declare.
pub fn metaclass_name(name: &str) -> Option<&'static str> {
    metaclass::canonical_name(name)
}
#[cfg(test)]
mod metaclass_tests;
pub mod model;
pub mod prepared;
pub mod quantity;
pub mod rational;
pub mod render;
mod schema_props;
pub mod structure;

mod semantic_memo;

mod properties;

mod flat;
