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
//!
//! Two forms of a name exist side by side and must not be confused:
//!
//! - the **canonical** form, [`escape_name`] — the specification's
//!   `escapedName` derivation (KerML 8.3.2.1: a name with the *form* of
//!   a basic name is returned as-is), which the model's qualified names,
//!   the interchange `qualifiedName` property and the normative id
//!   computations use. A reserved word used as a name stays bare there
//!   (`ControlFunctions::if`), exactly as the pilot implementation
//!   derives and hashes it;
//! - the **reference** form, [`spell_name`] / [`spell_path`] — what the
//!   textual notation re-parses. A reserved word has the form of a
//!   basic name but cannot be used as one (KerML 8.2.2.6), so it is
//!   quoted here. Anything that turns a canonical name back into source
//!   text goes through this form; [`respell_canonical`] converts.
//!
//! Which reserved-word table governs is a property of the text being
//! produced, not of the element: text printed into a known unit uses
//! that unit's dialect, and a spelling produced without a destination
//! (an API answer a host splices anywhere, a rename touching both
//! kinds of unit) quotes the words of *either* dialect — a quoted name
//! is legal in both, so the union is the destination-agnostic safe
//! choice.

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
#[must_use]
pub fn spell_name(dialect: Dialect, name: &str) -> String {
    spell_name_in(Some(dialect), name)
}

/// Spell `name` so it re-parses as a name in `dialect` — or, with
/// `None`, in either dialect: quoted when it is a reserved word of the
/// governing table(s) or not a basic name, bare otherwise. No legality
/// check (an empty name spells as `''`).
#[must_use]
pub fn spell_name_in(dialect: Option<Dialect>, name: &str) -> String {
    let reserved = match dialect {
        Some(d) => is_reserved(d, name),
        None => is_reserved(Dialect::Sysml, name) || is_reserved(Dialect::Kerml, name),
    };
    if reserved {
        format!("'{name}'")
    } else {
        escape_name(name)
    }
}

/// Spell raw (unescaped) name segments as a `::`-joined qualified
/// reference for `dialect` (`None`: either dialect — see
/// [`spell_name_in`]).
pub fn spell_path<I, S>(dialect: Option<Dialect>, segments: I) -> String
where
    I: IntoIterator<Item = S>,
    S: AsRef<str>,
{
    segments
        .into_iter()
        .map(|s| spell_name_in(dialect, s.as_ref()))
        .collect::<Vec<_>>()
        .join("::")
}

/// Split a canonical qualified name — [`escape_name`] segments joined
/// by `::`, as the model's qualified names and the interchange
/// `qualifiedName` are spelled — into its raw segments: the inverse of
/// `escape_name` applied per segment. Quoted segments unescape (so a
/// `::` inside quotes does not split) and bare segments are taken
/// verbatim, which reads a reserved word spelled either way.
#[must_use]
pub fn split_canonical(canonical: &str) -> Vec<String> {
    let mut out = Vec::new();
    let mut cur = String::new();
    let mut chars = canonical.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\'' => {
                while let Some(c) = chars.next() {
                    match c {
                        '\\' => match chars.next() {
                            Some('b') => cur.push('\u{0008}'),
                            Some('t') => cur.push('\t'),
                            Some('n') => cur.push('\n'),
                            Some('f') => cur.push('\u{000C}'),
                            Some('r') => cur.push('\r'),
                            Some(e) => cur.push(e),
                            None => {}
                        },
                        '\'' => break,
                        c => cur.push(c),
                    }
                }
            }
            ':' if chars.peek() == Some(&':') => {
                chars.next();
                out.push(std::mem::take(&mut cur));
            }
            c => cur.push(c),
        }
    }
    out.push(cur);
    out
}

/// Respell a canonical qualified name (see [`split_canonical`]) as
/// reference text for `dialect` (`None`: either dialect). A leading
/// global-root marker `$::` is kept. This is how a host turns a
/// reported `qualifiedName` into an `import`/`expose` target that
/// parses.
#[must_use]
pub fn respell_canonical(dialect: Option<Dialect>, canonical: &str) -> String {
    match canonical.strip_prefix("$::") {
        Some(rest) => format!("$::{}", spell_path(dialect, split_canonical(rest))),
        None => spell_path(dialect, split_canonical(canonical)),
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
    fn either_dialect_spelling_quotes_the_union() {
        // `part` is SysML-only, `end` KerML-only in name, `as` in both.
        assert_eq!(spell_name_in(None, "part"), "'part'");
        assert_eq!(spell_name_in(None, "end"), "'end'");
        assert_eq!(spell_name_in(None, "as"), "'as'");
        assert_eq!(spell_name_in(None, "Node"), "Node");
        assert_eq!(spell_name_in(None, "no-referrer"), "'no-referrer'");
        assert_eq!(spell_name_in(Some(Dialect::Kerml), "part"), "part");
        assert_eq!(spell_name_in(Some(Dialect::Sysml), "part"), "'part'");
    }

    #[test]
    fn paths_spell_per_segment() {
        assert_eq!(
            spell_path(None, ["part", "view", "Node"]),
            "'part'::'view'::Node"
        );
        assert_eq!(
            spell_path(Some(Dialect::Kerml), ["part", "view", "Node"]),
            "part::view::Node"
        );
        assert_eq!(spell_path(None, ["My Views", "x"]), "'My Views'::x");
        assert_eq!(spell_path(None, [""]), "''");
    }

    #[test]
    fn canonical_names_split_and_respell() {
        // The inverse of `escape_name` per segment, on every escape.
        for segs in [
            vec!["A", "b"],
            vec!["My Views", "part"],
            vec!["it's", "a\\b", "x::y"],
            vec!["line\nbreak", "tab\tx", "\"q\""],
            vec![""],
        ] {
            let canonical = segs
                .iter()
                .map(|s| escape_name(s))
                .collect::<Vec<_>>()
                .join("::");
            assert_eq!(split_canonical(&canonical), segs, "{canonical}");
        }
        assert_eq!(respell_canonical(None, "part::view"), "'part'::'view'");
        assert_eq!(respell_canonical(None, "part::'view'"), "'part'::'view'");
        assert_eq!(
            respell_canonical(Some(Dialect::Kerml), "part::view"),
            "part::view"
        );
        assert_eq!(respell_canonical(None, "'My Views'::x"), "'My Views'::x");
        assert_eq!(respell_canonical(None, "$::part::x"), "$::'part'::x");
        // Respelling is idempotent: reference text is its own canonical
        // form's respelling.
        let spelled = respell_canonical(None, "part::'it\\'s'::x::y");
        assert_eq!(respell_canonical(None, &spelled), spelled);
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
