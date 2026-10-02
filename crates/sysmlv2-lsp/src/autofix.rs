//! Statement repairs riding a completion accept (the auto-import
//! tier's second half): accepting a suggestion mid-statement also fixes what
//! the statement being typed still obviously needs. Today that is one
//! pass — close unbalanced quantity brackets — and the module is shaped
//! for more: each pass reads the shared [`Cx`] and appends to the fix,
//! so a new auto-fixable thing is a new pass function in
//! [`statement_repairs`]'s sequence, not a rework.
//!
//! No pass inserts the terminal `;`. The scan cannot tell whether the
//! statement is finished — a body, a multiplicity, or a value may follow
//! the accepted name — nor whether the enclosing body takes terminated
//! members at all: a constraint or calculation body ends in a bare
//! result expression, where a `;` is a syntax error. And a terminator
//! waiting behind the cursor doubles the one typed at the end.
//!
//! Repairs only ever apply when the cursor sits at the *effective end*
//! of the statement's line — everything after it is whitespace, a
//! continuation of the name chain being completed (`.volume` when the
//! accept lands mid-chain), closing brackets, or the terminator — so
//! mid-expression edits are never touched. The analysis is
//! lexical over the statement prefix, on the toolkit's own tokens
//! (strings, quoted names, comments, and notes respected);
//! a context the scan cannot judge (an unclosed `(`, an unterminated
//! string outside the completion's own replacement) yields no repairs
//! at all: a wrong fix costs more than a missing one.
//!
//! Delivery: when nothing but whitespace or the terminator follows the
//! cursor, the repair text rides the completion's main text edit
//! (`'m/s²']`, ahead of any `;`) — one edit, no ordering questions.
//! When a chain tail or auto-closed brackets already sit after the
//! cursor, what remains becomes its own insertion behind them — a
//! position strictly past the main edit, never at its end, as the
//! protocol requires of additional edits. Either way the cursor
//! belongs where typing continues — after the accepted name, *before*
//! any repair text — which the suffix path realizes as a snippet stop
//! (see [`crate::accept`]) and the insertion path gets for free.

use crate::position::offset32;

#[cfg(test)]
thread_local! {
    /// Statement scans run on this thread, so a test can pin what one
    /// completion request costs.
    pub(crate) static SCANS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// What a completion accept should additionally fix.
#[derive(Clone)]
pub(crate) struct Repairs {
    /// Appended to the completion's inserted text.
    pub suffix: String,
    /// A separate insertion `(byte offset, text)` strictly past the
    /// main edit, for what cannot ride it (the tail already holds
    /// closers or a chain tail the fix must land behind).
    pub insert: Option<(u32, String)>,
}

/// The shared repair context: what the statement prefix leaves open
/// and what the line's tail already provides.
struct Cx {
    /// Unclosed `[` count in the statement up to the completion's
    /// replacement start.
    open_brackets: usize,
    /// `]` count in the tail (before any `;`).
    closers_after: usize,
}

/// Compute the repairs a completion accept should carry. The accept
/// replaces `prefix_end..tail_start`: `stmt_start..prefix_end` is the
/// statement text it leaves in place ahead of it (`prefix_end` = the
/// main edit's replacement start, so a typed opening quote the edit
/// absorbs does not read as an unterminated string), and the line's
/// tail runs from `tail_start` — the cursor, or past what the edit
/// replaces beyond it (the rest of a quoted name being typed). `None`:
/// nothing to fix, or no safe judgment.
pub(crate) fn statement_repairs(
    text: &str,
    stmt_start: u32,
    prefix_end: u32,
    tail_start: u32,
) -> Option<Repairs> {
    #[cfg(test)]
    SCANS.with(|n| n.set(n.get() + 1));
    let stmt = text.get(stmt_start as usize..prefix_end as usize)?;
    let line_end = text[tail_start as usize..]
        .find('\n')
        .map(|i| tail_start as usize + i)
        .unwrap_or(text.len());
    let tail = &text[tail_start as usize..line_end];

    let open_brackets = open_brackets(stmt)?;
    // The tail must hold nothing but a continuation of the name chain
    // being completed (identifier characters and `.`, ahead of any
    // closer), whitespace, closers, and the terminator — anything else
    // means the cursor is mid-expression.
    let mut chain_end: Option<usize> = None;
    let mut closers_after = 0usize;
    let mut has_semicolon = false;
    let mut last_closer_end: Option<usize> = None;
    for (i, c) in tail.char_indices() {
        match c {
            ']' if !has_semicolon => {
                closers_after += 1;
                last_closer_end = Some(i + 1);
            }
            ';' if !has_semicolon => has_semicolon = true,
            c if (c.is_ascii_alphanumeric() || c == '_' || c == '.')
                && closers_after == 0
                && !has_semicolon =>
            {
                chain_end = Some(i + 1);
            }
            c if c.is_whitespace() => {}
            _ => return None,
        }
    }
    let cx = Cx {
        open_brackets,
        closers_after,
    };

    // The passes, in statement order. A future pass appends here.
    let mut fix = String::new();
    fix.push_str(&close_brackets_pass(&cx)?);
    if fix.is_empty() {
        return None;
    }

    if closers_after == 0 && chain_end.is_none() {
        // Nothing to land behind (whitespace, at most a terminator):
        // the fix rides the main edit, ahead of the tail.
        return Some(Repairs {
            suffix: fix,
            insert: None,
        });
    }
    // Land behind the existing closers and chain tail: strictly past
    // the main edit, never at its end.
    let at = last_closer_end
        .or(chain_end)
        .map(|i| tail_start + offset32(i))
        .unwrap_or(tail_start);
    Some(Repairs {
        suffix: String::new(),
        insert: Some((at, fix)),
    })
}

/// Pass: the `]` still needed for the statement's unclosed `[`.
/// `None` when the tail holds more closers than the prefix opened —
/// the scan misread something, so no repairs at all.
fn close_brackets_pass(cx: &Cx) -> Option<String> {
    let needed = cx.open_brackets.checked_sub(cx.closers_after)?;
    Some("]".repeat(needed))
}

/// Unclosed `[` count in the statement prefix. `None` for contexts a
/// repair cannot judge: text that does not lex (an unterminated string,
/// quoted name, comment, or note; a stray character such as a lone `!`
/// or an unquoted `°`), a `]` without its `[`, or an unclosed `(`/`{`
/// (the cursor is inside a grouping whose completion the user still
/// owes).
fn open_brackets(stmt: &str) -> Option<usize> {
    let g = groupings(stmt);
    (!g.unlexable && !g.unmatched && g.parens_or_braces == 0).then_some(g.brackets)
}

/// The groupings a statement prefix leaves open, counted over the
/// toolkit's own tokens: a string, a quoted name, a comment, or a note
/// (`//* … */` included) is one token, so a bracket inside it never
/// counts.
struct Groupings {
    /// Unclosed `[`.
    brackets: usize,
    /// Unclosed `(` and `{` together.
    parens_or_braces: usize,
    /// A `]` arrived with no `[` open (it is not counted).
    unmatched: bool,
    /// Some span did not lex: an unterminated string, quoted name,
    /// comment, or note (one token running to the end), or a stray
    /// character.
    unlexable: bool,
}

/// Count the groupings `stmt` leaves open (see [`Groupings`]).
fn groupings(stmt: &str) -> Groupings {
    use sysmlv2_parser::token::TokenKind;
    let mut g = Groupings {
        brackets: 0,
        parens_or_braces: 0,
        unmatched: false,
        unlexable: false,
    };
    for token in sysmlv2_parser::lexer::tokenize(stmt).0 {
        match token.kind {
            TokenKind::LBracket => g.brackets += 1,
            TokenKind::RBracket => match g.brackets.checked_sub(1) {
                Some(depth) => g.brackets = depth,
                None => g.unmatched = true,
            },
            TokenKind::LParen | TokenKind::LBrace => g.parens_or_braces += 1,
            TokenKind::RParen | TokenKind::RBrace => {
                g.parens_or_braces = g.parens_or_braces.saturating_sub(1);
            }
            TokenKind::Error => g.unlexable = true,
            _ => {}
        }
    }
    g
}

#[cfg(test)]
mod tests {
    use super::{offset32, statement_repairs};

    fn repairs(text: &str, cursor: &str) -> Option<(String, Option<(u32, String)>)> {
        let offset = offset32(text.find(cursor).expect("cursor") + cursor.len());
        let stmt_start = offset32(
            text[..offset as usize]
                .rfind([';', '{', '}'])
                .map(|i| i + 1)
                .unwrap_or(0),
        );
        let prefix_end = offset32(
            text[..offset as usize]
                .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
                .map(|i| i + 1)
                .unwrap_or(0),
        );
        statement_repairs(text, stmt_start, prefix_end, offset).map(|r| (r.suffix, r.insert))
    }

    #[test]
    fn closes_bracket_on_bare_tail() {
        let text = "package P {\n    attribute g = 9.8 [m\n}\n";
        assert_eq!(repairs(text, "[m"), Some(("]".to_string(), None)));
    }

    #[test]
    fn nothing_behind_a_closed_bracket() {
        for text in [
            "package P {\n    attribute g = 9.8 [m]\n}\n",
            "package P {\n    attribute g = 9.8 [m];\n}\n",
        ] {
            assert_eq!(repairs(text, "[m"), None, "{text:?}");
        }
    }

    #[test]
    fn closes_bracket_before_an_existing_terminator() {
        for text in [
            "package P {\n    attribute g = 9.8 [m;\n}\n",
            "package P {\n    attribute g = 9.8 [m  ;\n}\n",
        ] {
            assert_eq!(
                repairs(text, "[m"),
                Some(("]".to_string(), None)),
                "{text:?}"
            );
        }
    }

    #[test]
    fn closes_bracket_behind_a_chain_tail_ahead_of_a_terminator() {
        let text = "package P {\n    attribute v = a[b.chain;\n}\n";
        let (suffix, insert) = repairs(text, "a[b").expect("repairs");
        assert_eq!(suffix, "");
        let at = offset32(text.find(".chain").unwrap()) + 6;
        assert_eq!(insert, Some((at, "]".to_string())));
    }

    /// The terminator is never inserted: not after a plain statement,
    /// a chain tail, or an import path, and not inside a body whose
    /// last member is a bare result expression.
    #[test]
    fn never_terminates_the_statement() {
        for (text, cursor) in [
            ("package P {\n    part w : Whee\n}\n", "Whee"),
            (
                "package P {\n    attribute v = fuelTank.over.volume\n}\n",
                "over",
            ),
            ("package P {\n    private import Qua\n}\n", "Qua"),
            (
                "part def P {\n    assert constraint {\n        mass <= lim\n    }\n}\n",
                "<= lim",
            ),
            ("calc def F {\n    in x : Real;\n    x * fac\n}\n", "* fac"),
        ] {
            assert_eq!(repairs(text, cursor), None, "{text}");
        }
    }

    #[test]
    fn closes_bracket_in_a_constraint_body() {
        let text = "part def P {\n    assert constraint {\n        mass <= 2000 [k\n    }\n}\n";
        assert_eq!(repairs(text, "[k"), Some(("]".to_string(), None)));
    }

    #[test]
    fn closes_bracket_behind_a_chain_tail() {
        // Accept lands mid-chain (`a[b|.chain`): the `]` goes after the
        // tail, not at the cursor.
        let text = "package P {\n    attribute v = a[b.chain\n}\n";
        let (suffix, insert) = repairs(text, "a[b").expect("repairs");
        assert_eq!(suffix, "");
        let at = offset32(text.find(".chain").unwrap()) + 6;
        assert_eq!(insert, Some((at, "]".to_string())));
    }

    #[test]
    fn nothing_when_a_chain_tail_already_closes() {
        let text = "package P {\n    attribute v = a[b.chain]\n}\n";
        assert_eq!(repairs(text, "a[b"), None);
    }

    #[test]
    fn nothing_mid_expression() {
        let text = "package P {\n    attribute g = 9.8 [m * 2];\n}\n";
        assert_eq!(repairs(text, "[m"), None);
    }

    #[test]
    fn nothing_inside_open_parens() {
        let text = "package P {\n    calc def F(\n        x = 9.8 [m\n}\n";
        assert_eq!(repairs(text, "[m"), None);
    }

    #[test]
    fn noted_brackets_do_not_count() {
        // A note runs to its `*/`, across lines; counted, its `[` would
        // ask for a `]`.
        let text = "package P {\n    attribute g = 9.8 //* see\n    [ */ + m\n}\n";
        assert_eq!(repairs(text, "+ m"), None);
    }

    #[test]
    fn nothing_after_text_that_does_not_lex() {
        let text = "package P {\n    attribute g = x ! 9.8 [m\n}\n";
        assert_eq!(repairs(text, "[m"), None);
    }

    #[test]
    fn quoted_brackets_do_not_count() {
        // Counted, the quoted `[` would ask for a `]`.
        let text = "package P {\n    attribute g = 'a[' + m\n}\n";
        assert_eq!(repairs(text, "+ m"), None);
    }

    #[test]
    fn typed_opening_quote_is_the_main_edits_problem() {
        // prefix_end sits before the quote (the completion's replace
        // range absorbs it), so the scan never sees a dangling string.
        let text = "package P {\n    attribute g = 9.8 ['m\n}\n";
        let offset = offset32(text.find("['m").unwrap() + 3);
        let r = statement_repairs(text, 12, offset - 2, offset).expect("repairs");
        assert_eq!(r.suffix, "]");
    }
}
