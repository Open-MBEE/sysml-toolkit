//! Semantic model layer for the OMG SysML v2 / KerML stack: lowers the
//! syntax AST (`sysmlv2-syntax`) to the abstract-syntax element graph with
//! name resolution and deterministic/normative element IDs, serializes the
//! JSON interchange forms (compact + full, KerML 10.4), reads them back,
//! holds multi-file models resolved against the OMG standard library, runs
//! referential checks, and evaluates expressions.

pub mod ambient;
pub mod cbor_tables;
pub mod check;
pub mod eval;
pub mod full;
pub mod ids;
pub mod json;
pub mod libcache;
pub mod lift;
pub mod model;
pub mod quantity;
pub mod render;
mod schema_props;
pub mod structure;
