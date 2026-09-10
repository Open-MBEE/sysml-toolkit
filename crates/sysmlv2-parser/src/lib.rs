//! Facade for the sysmlv2 workspace: re-exports the syntax layer
//! (`sysmlv2-syntax`: lexer → parser → AST → printer/formatter) and, behind
//! the `json` feature, the semantic model layer (`sysmlv2-model`: element
//! graph, name resolution, JSON interchange, referential checks,
//! expression evaluation) under the module paths this crate has always had.
//!
//! ```text
//! source text ──lexer──▶ tokens ──parser──▶ AST ──build──▶ element graph ──▶ JSON
//! ```
//!
//! New code may depend on `sysmlv2-syntax` / `sysmlv2-model` directly; this
//! crate keeps the original `sysmlv2_parser::…` paths stable. See the
//! workspace `README.md` for the workspace architecture.

pub use sysmlv2_syntax::{Diagnostic, Span};
pub use sysmlv2_syntax::{ast, diag, lexer, name, parser, print, span, token, visit};

#[cfg(feature = "json")]
pub use sysmlv2_model::{ambient, eval, full, ids, json, libcache, lift, model, quantity, render};

/// Post-parse validation: body-context legality (syntax-level) and — with
/// the `json` feature — model-level referential checks.
pub mod check {
    pub use sysmlv2_syntax::check::*;

    #[cfg(feature = "json")]
    pub use sysmlv2_model::check::{
        ConstraintBinding, ConstraintCheck, ConstraintVerdict, check_constraints,
        constraint_bindings, satisfaction_checks, validate_model, validate_model_with,
        validate_semantics, validate_semantics_with,
    };
}
