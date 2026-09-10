//! Canonical identifier spelling: the one answer to "is this string a
//! legal element name, and how does the toolkit print it?".
//!
//! Generators that mint names from external vocabularies call this
//! instead of copying the reserved-word table or
//! the escaping rules: a reserved word (`part`, `after`, `frame`) prints
//! as a quoted restricted name even though it is lexically basic, a
//! non-basic name is quoted with the lexer's escapes, and anything else
//! prints bare. The printer uses the same function, so a generated
//! spelling can never disagree with what the formatter would emit.

use crate::ast::{Dialect, escape_name};
use crate::parser::is_reserved;

/// The canonical textual spelling of a legal name.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CanonicalName {
    /// Exactly what the printer emits for this name: bare, or
    /// single-quoted with escapes.
    pub spelling: String,
    /// True when `spelling` is a quoted restricted name (reserved word
    /// or non-basic characters).
    pub quoted: bool,
}

/// Why a string cannot be an element name.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NameError {
    /// The empty string: a quoted name may hold any text, but not none.
    Empty,
}

impl std::fmt::Display for NameError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            NameError::Empty => f.write_str("a name must not be empty"),
        }
    }
}

impl std::error::Error for NameError {}

/// Spell `name` as the printer would in `dialect`, without a legality
/// check (an empty name spells as `''`).
pub fn spell_name(dialect: Dialect, name: &str) -> String {
    if is_reserved(dialect, name) {
        format!("'{name}'")
    } else {
        escape_name(name)
    }
}

/// The canonical spelling of `name` in `dialect`, or why it is not a
/// legal name.
pub fn canonical_name(dialect: Dialect, name: &str) -> Result<CanonicalName, NameError> {
    if name.is_empty() {
        return Err(NameError::Empty);
    }
    let spelling = spell_name(dialect, name);
    let quoted = spelling.starts_with('\'');
    Ok(CanonicalName { spelling, quoted })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sysml(name: &str) -> CanonicalName {
        canonical_name(Dialect::Sysml, name).unwrap()
    }

    #[test]
    fn basic_names_print_bare() {
        for n in ["Node", "nodeType", "_x", "H3", "a1"] {
            assert_eq!(
                sysml(n),
                CanonicalName {
                    spelling: n.into(),
                    quoted: false
                }
            );
        }
    }

    #[test]
    fn reserved_words_are_quoted_per_dialect() {
        for n in [
            "part", "action", "item", "all", "loop", "default", "as", "after", "assign", "frame",
            "end",
        ] {
            let c = sysml(n);
            assert!(c.quoted, "{n} must quote");
            assert_eq!(c.spelling, format!("'{n}'"));
        }
        // `part` is a SysML word only; KerML prints it bare.
        assert_eq!(
            canonical_name(Dialect::Kerml, "part").unwrap().spelling,
            "part"
        );
        assert!(canonical_name(Dialect::Kerml, "end").unwrap().quoted);
    }

    #[test]
    fn non_basic_names_are_quoted_with_escapes() {
        assert_eq!(sysml("no-referrer").spelling, "'no-referrer'");
        assert_eq!(sysml("m/s²").spelling, "'m/s²'");
        assert_eq!(sysml("it's").spelling, "'it\\'s'");
        assert_eq!(sysml("a\\b").spelling, "'a\\\\b'");
        assert_eq!(sysml("1st").spelling, "'1st'");
        assert_eq!(sysml(" ").spelling, "' '");
        assert_eq!(sysml("line\nbreak").spelling, "'line\\nbreak'");
    }

    #[test]
    fn empty_is_illegal() {
        assert_eq!(canonical_name(Dialect::Sysml, ""), Err(NameError::Empty));
        assert_eq!(spell_name(Dialect::Sysml, ""), "''");
    }

    #[test]
    fn canonical_spelling_round_trips_through_the_lexer() {
        use crate::lexer::{tokenize, unescape};
        use crate::token::TokenKind;
        for n in [
            "Node",
            "part",
            "no-referrer",
            "it's",
            "a\\b",
            "line\nbreak",
            "tab\tx",
            "\"q\"",
        ] {
            let c = sysml(n);
            let (toks, diags) = tokenize(&c.spelling);
            assert!(diags.is_empty(), "{n}: {diags:?}");
            let tok = toks.iter().find(|t| t.kind != TokenKind::Eof).unwrap();
            let raw = tok.span.slice(&c.spelling);
            let value = if c.quoted {
                unescape(raw)
            } else {
                raw.to_string()
            };
            assert_eq!(value, n);
        }
    }
}
