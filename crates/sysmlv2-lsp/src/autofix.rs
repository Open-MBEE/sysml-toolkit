//! Statement repairs riding a completion accept (the auto-import
//! tier's second half): accepting a suggestion mid-statement also fixes what
//! the statement being typed still obviously needs. Today that is two
//! passes — close unbalanced quantity brackets, insert the terminal
//! semicolon — and the module is shaped for more: each pass reads the
//! shared [`Cx`] and appends to the fix, so a new auto-fixable thing
//! is a new pass function in [`statement_repairs`]'s sequence, not a
//! rework.
//!
//! Repairs only ever apply when the cursor sits at the *effective end*
//! of the statement's line — everything after it is whitespace, a
//! continuation of the name chain being completed (`.volume` when the
//! accept lands mid-chain), closing brackets, or the terminator itself
//! — so mid-expression edits are never touched. The analysis is
//! lexical over the statement prefix (strings and comments respected);
//! a context the scan cannot judge (an unclosed `(`, an unterminated
//! string outside the completion's own replacement) yields no repairs
//! at all: a wrong fix costs more than a missing one.
//!
//! Delivery: when nothing follows the cursor, the repair text rides
//! the completion's main text edit (`'m/s²'];`) — one edit, no
//! ordering questions. When a chain tail or auto-closed brackets
//! already sit after the cursor, what remains becomes its own
//! insertion after them (a position strictly past the main edit, so
//! clients apply it unambiguously). Either way the cursor belongs
//! where typing continues — after the accepted name, *before* any
//! repair text — which the suffix path realizes as a snippet stop
//! (see `item_edits` in `nav`) and the insertion path gets for free.

/// What a completion accept should additionally fix.
pub(crate) struct Repairs {
    /// Appended to the completion's inserted text.
    pub suffix: String,
    /// A separate insertion `(byte offset, text)` past the cursor, for
    /// what cannot ride the main edit (the tail already holds closers
    /// the fix must land behind).
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
    /// The tail already terminates the statement.
    has_semicolon: bool,
}

/// Compute the repairs a completion accepted at `offset` should carry.
/// `stmt_start`..`prefix_end` is the statement text the accept leaves
/// in place (`prefix_end` = the main edit's replacement start, so a
/// typed opening quote the edit absorbs does not read as an
/// unterminated string). `None`: nothing to fix, or no safe judgment.
pub(crate) fn statement_repairs(
    text: &str,
    stmt_start: u32,
    prefix_end: u32,
    offset: u32,
) -> Option<Repairs> {
    let stmt = text.get(stmt_start as usize..prefix_end as usize)?;
    let line_end = text[offset as usize..]
        .find('\n')
        .map(|i| offset as usize + i)
        .unwrap_or(text.len());
    let tail = &text[offset as usize..line_end];

    let open_brackets = open_brackets(stmt)?;
    // The tail must hold nothing but a continuation of the name chain
    // being completed (identifier characters and `.`, ahead of any
    // closer), whitespace, closers, and the terminator — anything else
    // means the cursor is mid-expression.
    let mut chain_end: Option<usize> = None;
    let mut closers_after = 0usize;
    let mut has_semicolon = false;
    let mut last_closer_end: Option<usize> = None;
    let mut semicolon_at: Option<usize> = None;
    for (i, c) in tail.char_indices() {
        match c {
            ']' if !has_semicolon => {
                closers_after += 1;
                last_closer_end = Some(i + 1);
            }
            ';' if !has_semicolon => {
                has_semicolon = true;
                semicolon_at = Some(i);
            }
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
        has_semicolon,
    };

    // The passes, in statement order: brackets close before the
    // terminator. A future pass appends here.
    let mut fix = String::new();
    fix.push_str(&close_brackets_pass(&cx)?);
    fix.push_str(terminator_pass(&cx));
    if fix.is_empty() {
        return None;
    }

    if closers_after == 0 && !has_semicolon && chain_end.is_none() {
        // Bare tail: everything rides the main edit.
        return Some(Repairs {
            suffix: fix,
            insert: None,
        });
    }
    // Land behind the existing closers and chain tail (and before an
    // existing `;`, where only closers remain to add).
    let at = last_closer_end
        .or(semicolon_at)
        .or(chain_end)
        .map(|i| offset + i as u32)
        .unwrap_or(offset);
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

/// Pass: the terminal `;`, when the tail does not already have one.
fn terminator_pass(cx: &Cx) -> &'static str {
    if cx.has_semicolon { "" } else { ";" }
}

/// Unclosed `[` count in the statement prefix, strings and comments
/// skipped. `None` for contexts a repair cannot judge: an unterminated
/// string or comment, or an unclosed `(`/`{` (the cursor is inside a
/// grouping whose completion the user still owes).
fn open_brackets(stmt: &str) -> Option<usize> {
    let mut depth = 0usize;
    let mut paren_or_brace = 0usize;
    let mut chars = stmt.chars().peekable();
    while let Some(c) = chars.next() {
        match c {
            '\'' | '"' => loop {
                match chars.next() {
                    None => return None,
                    Some('\\') => {
                        chars.next();
                    }
                    Some(q) if q == c => break,
                    Some(_) => {}
                }
            },
            '/' if chars.peek() == Some(&'/') => {
                for q in chars.by_ref() {
                    if q == '\n' {
                        break;
                    }
                }
            }
            '/' if chars.peek() == Some(&'*') => {
                chars.next();
                let mut prev = ' ';
                loop {
                    match chars.next() {
                        None => return None,
                        Some('/') if prev == '*' => break,
                        Some(q) => prev = q,
                    }
                }
            }
            '[' => depth += 1,
            ']' => depth = depth.checked_sub(1)?,
            '(' | '{' => paren_or_brace += 1,
            ')' | '}' => paren_or_brace = paren_or_brace.saturating_sub(1),
            _ => {}
        }
    }
    (paren_or_brace == 0).then_some(depth)
}

#[cfg(test)]
mod tests {
    use super::statement_repairs;

    fn repairs(text: &str, cursor: &str) -> Option<(String, Option<(u32, String)>)> {
        let offset = (text.find(cursor).expect("cursor") + cursor.len()) as u32;
        let stmt_start = text[..offset as usize]
            .rfind([';', '{', '}'])
            .map(|i| i + 1)
            .unwrap_or(0) as u32;
        let prefix_end = text[..offset as usize]
            .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .map(|i| i + 1)
            .unwrap_or(0) as u32;
        statement_repairs(text, stmt_start, prefix_end, offset).map(|r| (r.suffix, r.insert))
    }

    #[test]
    fn closes_bracket_and_terminates_on_bare_tail() {
        let text = "package P {\n    attribute g = 9.8 [m\n}\n";
        assert_eq!(repairs(text, "[m"), Some(("];".to_string(), None)));
    }

    #[test]
    fn terminates_behind_an_auto_closed_bracket() {
        let text = "package P {\n    attribute g = 9.8 [m]\n}\n";
        let (suffix, insert) = repairs(text, "[m").expect("repairs");
        assert_eq!(suffix, "");
        let at = text.find("m]").unwrap() as u32 + 2;
        assert_eq!(insert, Some((at, ";".to_string())));
    }

    #[test]
    fn closes_bracket_before_an_existing_terminator() {
        let text = "package P {\n    attribute g = 9.8 [m;\n}\n";
        let (suffix, insert) = repairs(text, "[m").expect("repairs");
        assert_eq!(suffix, "");
        let at = text.find(';').unwrap() as u32;
        assert_eq!(insert, Some((at, "]".to_string())));
    }

    #[test]
    fn terminates_plain_statements() {
        let text = "package P {\n    part w : Whee\n}\n";
        assert_eq!(repairs(text, "Whee"), Some((";".to_string(), None)));
    }

    #[test]
    fn terminates_behind_a_chain_tail() {
        // Accept lands mid-chain (`fuelTank.over|.volume`): the `;`
        // goes after the tail, not at the cursor.
        let text = "package P {\n    attribute v = fuelTank.over.volume\n}\n";
        let (suffix, insert) = repairs(text, "over").expect("repairs");
        assert_eq!(suffix, "");
        let at = text.find(".volume").unwrap() as u32 + 7;
        assert_eq!(insert, Some((at, ";".to_string())));
    }

    #[test]
    fn closes_bracket_behind_a_chain_and_its_closer() {
        let text = "package P {\n    attribute v = a[b.chain]\n}\n";
        let (suffix, insert) = repairs(text, "a[b").expect("repairs");
        assert_eq!(suffix, "");
        let at = text.find("chain]").unwrap() as u32 + 6;
        assert_eq!(insert, Some((at, ";".to_string())));
    }

    #[test]
    fn nothing_when_a_chain_tail_is_already_terminated() {
        let text = "package P {\n    attribute v = fuelTank.over.volume;\n}\n";
        assert_eq!(repairs(text, "over"), None);
    }

    #[test]
    fn nothing_when_already_terminated() {
        let text = "package P {\n    attribute g = 9.8 [m];\n}\n";
        assert_eq!(repairs(text, "[m"), None);
    }

    #[test]
    fn nothing_mid_expression() {
        let text = "package P {\n    attribute g = 9.8 [m * 2];\n}\n";
        assert_eq!(repairs(text, "[m"), None);
    }

    #[test]
    fn nothing_inside_open_parens() {
        let text = "package P {\n    calc def F(\n        x : Rea\n}\n";
        assert_eq!(repairs(text, "Rea"), None);
    }

    #[test]
    fn quoted_brackets_do_not_count() {
        let text = "package P {\n    attribute g = 'a[' + m\n}\n";
        assert_eq!(repairs(text, "+ m"), Some((";".to_string(), None)));
    }

    #[test]
    fn typed_opening_quote_is_the_main_edits_problem() {
        // prefix_end sits before the quote (the completion's replace
        // range absorbs it), so the scan never sees a dangling string.
        let text = "package P {\n    attribute g = 9.8 ['m\n}\n";
        let offset = (text.find("['m").unwrap() + 3) as u32;
        let r = statement_repairs(text, 12, offset - 2, offset).expect("repairs");
        assert_eq!(r.suffix, "];");
    }
}
