//! Syntax layer for the OMG SysML v2 and KerML textual notations: lexer,
//! hand-written recursive-descent parser (both dialects), a syntax-faithful
//! AST with spans everywhere, a printer/formatter, and post-parse
//! body-context validation. No semantic resolution here — that lives in
//! `sysmlv2-model`.

pub mod ast;
pub mod check;
pub mod diag;
pub mod lexer;
pub mod name;
pub mod parser;
pub mod print;
pub mod span;
pub mod token;
pub mod visit;

pub use diag::{Diagnostic, Diagnostics};
pub use span::Span;
