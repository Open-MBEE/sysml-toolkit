//! Salvage: texts that parse, made from the ones being edited, for the
//! completion tier's session. A session refuses every unit with a
//! syntax error, and a workspace being edited nearly always holds one:
//! the statement being typed, and — further up, in another file — a
//! statement half typed or a body not closed yet, any of which would
//! leave member and unit completions with no model at all. The
//! statement being typed is cut out ([`typed_statement_cut`]); in what
//! remains, a declaration missing only its `;` gets it written behind
//! its last token, the other member declarations the parser reports
//! errors in are blanked out, and the braces they leave unbalanced are
//! closed ([`salvage`], per workspace [`SalvageCache::salvage_all`]):
//! every other declaration keeps its meaning, and every byte before the
//! end of the text keeps its offset, so positions into the live
//! document still address the salvaged one.

use crate::position::offset32;
use std::borrow::Cow;
use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use sysmlv2_parser::ast::Member;
use sysmlv2_parser::span::Span;
use sysmlv2_parser::token::{Token, TokenKind};
use sysmlv2_parser::visit::{Visit, walk_member};

/// What the completion session leaves out of the document being edited:
/// the statement being typed (it starts at `stmt_start`, the cursor is
/// at `cursor`), which rarely parses mid-edit — through the cursor's
/// line, ending early after a `;` that ends it and before a closer it
/// did not open (in `assert constraint { v.| }` the `}` closes the body
/// around the statement; cut with it, the rest of the unit would not
/// balance). A body the statement opens after the cursor goes with it,
/// through its `}` on whichever line that sits.
pub(crate) fn typed_statement_cut(text: &str, stmt_start: u32, cursor: u32) -> Span {
    let start = (stmt_start as usize).min(text.len());
    let cursor = (cursor as usize).clamp(start, text.len());
    let line_end = text[cursor..].find('\n').map_or(text.len(), |i| cursor + i);
    let end = statement_end(text, start, cursor, line_end)
        .or_else(|| statement_end(text, start, cursor, text.len()))
        .unwrap_or(text.len());
    Span::new(offset32(start), offset32(end))
}

/// Where the statement that starts at byte `start` ends, scanning its
/// tokens up to `limit` (see [`typed_statement_cut`]): `limit` when
/// nothing ends it sooner, `None` when a body it opened after `cursor`
/// is still open there.
fn statement_end(text: &str, start: usize, cursor: usize, limit: usize) -> Option<usize> {
    use TokenKind as K;
    // The groupings open so far, each with whether it opened after the
    // cursor.
    let mut open: Vec<(K, bool)> = Vec::new();
    let body_open = |open: &[(K, bool)]| open.iter().any(|&(k, after)| k == K::LBrace && after);
    for token in sysmlv2_parser::lexer::tokenize(text.get(start..limit)?).0 {
        let at = start + token.span.start as usize;
        let after = at >= cursor;
        match token.kind {
            K::LParen | K::LBracket | K::LBrace => open.push((token.kind, after)),
            K::RParen | K::RBracket => {
                let opener = if token.kind == K::RParen {
                    K::LParen
                } else {
                    K::LBracket
                };
                if open.last().is_some_and(|&(k, _)| k == opener) {
                    open.pop();
                }
            }
            K::RBrace => match open.last() {
                Some(&(K::LBrace, opened_after)) => {
                    open.pop();
                    // The statement's own body closed: it ends here.
                    if opened_after && !body_open(&open) {
                        return Some(at + 1);
                    }
                }
                // A `}` the statement did not open closes the body the
                // statement sits in.
                _ if after => return Some(at),
                _ => {}
            },
            K::Semi if after && open.is_empty() => return Some(at + 1),
            _ => {}
        }
    }
    (!body_open(&open)).then_some(limit)
}

/// Repair rounds before a text is given up on. Each round writes each
/// missing `;` the parse reported and blanks every other member it
/// reported an error in; the next parse can report errors the parser's
/// recovery hid behind the first ones.
const ROUNDS: usize = 4;

/// `text` made to parse (borrowed back when it already does), or
/// `None` when a few rounds of repair do not get it there — or a round
/// changes nothing, which the next would not either. A missing `;` is
/// written over one whitespace byte behind the declaration — a line
/// break when there is no other, and after it at the very end of the
/// text — whole member declarations with other errors are blanked
/// (their bytes become spaces, line breaks kept), and missing closing
/// braces are appended, so offsets into the text stay valid.
///
/// Two repairs keep more than the member in error, and give way to
/// blanking it whole when the rounds do not get there with them: a
/// string, quoted name, comment or note left open, which the lexer runs
/// to the end of the text, ends at its own line, leaving what follows
/// to the next rounds ([`open_literal`]); and a declaration whose
/// header is in error keeps its body ([`member_around`]).
pub(crate) fn salvage(text: &str, kerml: bool) -> Option<Cow<'_, str>> {
    let parsed = Parsed::of(text, kerml);
    if parsed.errors.is_empty() {
        return Some(Cow::Borrowed(text));
    }
    match rounds(text, kerml, parsed, true) {
        (Some(repaired), _) => Some(Cow::Owned(repaired)),
        (None, true) => rounds(text, kerml, Parsed::of(text, kerml), false)
            .0
            .map(Cow::Owned),
        (None, false) => None,
    }
}

/// [`salvage`]'s rounds of repair over `original`, which `parsed` read:
/// the text they make parse, if they do, and whether a repair keeping
/// more than the member in error (`keep`) took part.
fn rounds(original: &str, kerml: bool, mut parsed: Parsed, keep: bool) -> (Option<String>, bool) {
    let mut text = original.to_string();
    let mut kept = false;
    // Where the last round took errors for the member before them.
    let mut retried = Vec::new();
    for _ in 0..ROUNDS {
        let round = repair(original, &text, &parsed, &retried, kerml, keep);
        kept |= round.kept;
        if round.text == text {
            return (None, kept);
        }
        text = round.text;
        retried = round.taken_before;
        parsed = Parsed::of(&text, kerml);
        if parsed.errors.is_empty() {
            return (Some(text), kept);
        }
    }
    (None, kept)
}

/// What [`salvage`] made of a unit.
enum Salvaged {
    /// It parses as it is.
    Parses,
    /// It parses once repaired: the repaired text.
    Repaired(String),
    /// It could not be salvaged and stays out.
    Left,
}

/// [`salvage`] over a whole workspace, remembering each unit's outcome
/// by the hash of its text: between two builds of the completion
/// session usually only the document being edited changed, and the
/// rest need neither another parse nor another repair.
#[derive(Default)]
pub(crate) struct SalvageCache {
    units: HashMap<String, (u64, Salvaged)>,
}

impl SalvageCache {
    /// `sources` made to parse: each unit as it is, salvaged, or — when
    /// it cannot be — left out.
    pub(crate) fn salvage_all(&mut self, sources: Vec<(String, String)>) -> Vec<(String, String)> {
        let mut previous = std::mem::take(&mut self.units);
        let mut out = Vec::with_capacity(sources.len());
        for (name, text) in sources {
            let hash = {
                let mut hasher = std::collections::hash_map::DefaultHasher::new();
                text.hash(&mut hasher);
                hasher.finish()
            };
            let outcome = match previous.remove(&name) {
                Some((known, outcome)) if known == hash => outcome,
                _ => match salvage(&text, crate::is_kerml(&name)) {
                    Some(Cow::Borrowed(_)) => Salvaged::Parses,
                    Some(Cow::Owned(repaired)) => Salvaged::Repaired(repaired),
                    None => Salvaged::Left,
                },
            };
            match &outcome {
                Salvaged::Parses => out.push((name.clone(), text)),
                Salvaged::Repaired(repaired) => out.push((name.clone(), repaired.clone())),
                Salvaged::Left => {}
            }
            self.units.insert(name, (hash, outcome));
        }
        out
    }
}

/// What a parse of a text being salvaged reports: where its errors
/// are, and where the member declarations it kept end — those it read
/// through, some only once it had repaired them in place.
struct Parsed {
    /// Each error's byte offset, in the order they were reported: the
    /// lexer's first — the parser reports none of its own at a token the
    /// lexer found in error — then the parser's, in the order it read
    /// the text in, a member's own errors before the `;` it found missing
    /// at its end.
    errors: Vec<usize>,
    /// Where the parser reported a `;` after a body's result expression:
    /// the result stands, and the `;` is all that is in error.
    result_terminators: Vec<usize>,
    /// Where the parser reported a `;` missing, and which of the errors
    /// that is: the errors with no width, at the end of a declaration's
    /// last token where the `;` goes — or at the end of the text, which
    /// cuts a declaration short the same way.
    missing: Vec<(usize, usize)>,
    /// Where each member declaration kept ends, at every depth, sorted.
    ends: Vec<usize>,
}

impl Parsed {
    /// Parse `text`; the members are read only when it has errors.
    fn of(text: &str, kerml: bool) -> Self {
        let parse = if kerml {
            sysmlv2_parser::parser::parse_kerml_source(text)
        } else {
            sysmlv2_parser::parser::parse_source(text)
        };
        let spans = parse.diagnostics.iter().map(|d| d.span);
        let errors: Vec<usize> = spans.clone().map(|s| s.start as usize).collect();
        let result_terminators = parse
            .diagnostics
            .iter()
            .filter(|d| d.message == sysmlv2_parser::parser::RESULT_EXPRESSION_TERMINATOR)
            .map(|d| d.span.start as usize)
            .collect();
        let missing = spans
            .enumerate()
            .filter(|(_, s)| s.start == s.end)
            .map(|(order, s)| (s.start as usize, order))
            .collect();
        let mut ends = MemberEnds::default();
        if !errors.is_empty() {
            ends.visit_unit(&parse.unit);
        }
        let mut ends = ends.0;
        ends.sort_unstable();
        Parsed {
            errors,
            result_terminators,
            missing,
            ends,
        }
    }

    /// Does a kept member end at byte `at`?
    fn ends_member_at(&self, at: usize) -> bool {
        self.ends.binary_search(&at).is_ok()
    }

    /// Did the parser report a `;` missing at byte `at`?
    fn missing_at(&self, at: usize) -> bool {
        self.missing_reported(at).is_some()
    }

    /// Which of the errors reports a `;` missing at byte `at`, if one
    /// does.
    fn missing_reported(&self, at: usize) -> Option<usize> {
        self.missing
            .iter()
            .find(|&&(missing, _)| missing == at)
            .map(|&(_, order)| order)
    }

    /// Does a kept member end with `token`, the parser reading on from
    /// there as from the start of another? A member ends with its `;`,
    /// the `}` closing its body, or its comment — or anywhere the parser
    /// reported its `;` missing, taking the line break after for it. A
    /// member kept ending anywhere else is one the parser reported
    /// unfinished at the token after.
    fn ends_member(&self, token: &Token) -> bool {
        let end = token.span.end as usize;
        self.ends_member_at(end) && (terminates(token) || self.missing_at(end))
    }
}

/// Can a member end with `token` — its `;`, the `}` closing its body,
/// its comment?
fn terminates(token: &Token) -> bool {
    matches!(
        token.kind,
        TokenKind::Semi | TokenKind::RBrace | TokenKind::RegularComment
    )
}

/// Where every member declaration in a syntax tree ends.
#[derive(Default)]
struct MemberEnds(Vec<usize>);

impl<'a> Visit<'a> for MemberEnds {
    fn visit_member(&mut self, member: &'a Member) {
        self.0.push(member.span.end as usize);
        walk_member(self, member);
    }
}

/// What one round of repair made of a text.
struct Round {
    text: String,
    /// Where it took errors for the member before them, for the next
    /// round's `retried` (see [`member_around`]).
    taken_before: Vec<usize>,
    /// Whether a repair keeping more than the member in error took part.
    kept: bool,
}

/// One round over `text`, made from `original`: terminate each
/// declaration the parser found missing its `;`, blank a `;` after a
/// body's result expression, the member around each other error, then
/// balance braces. With `keep`, a literal left open ends at its own
/// line ([`open_literal`]): blanked through it with the member it
/// opens, nothing blanked for another error reaching past it, while the
/// errors after it, the swallowed text's doing, wait for the next
/// round, which reads that text afresh; and a header in error keeps its
/// body.
fn repair(
    original: &str,
    text: &str,
    parsed: &Parsed,
    retried: &[usize],
    kerml: bool,
    keep: bool,
) -> Round {
    let tokens = significant_tokens(text);
    let (strays, open) = brace_balance(&tokens);
    let mut bytes = text.as_bytes().to_vec();
    let mut terminators = Vec::new();
    let mut blanked = Vec::new();
    let mut taken_before = Vec::new();
    let literal = keep
        .then(|| open_literal(text, &tokens, parsed, kerml))
        .flatten();
    let mut kept = literal.is_some();
    if let Some((i, line_end)) = literal {
        let start = member_start(&tokens[..i], parsed, false);
        blank(&mut bytes, original, start, line_end);
        blanked.push((start, line_end));
    }
    // A declaration the parser kept, cut short by the end of the text
    // itself, has no whitespace behind it to take its `;`, and with no
    // body left open balancing adds no line break for the next round to
    // write it into: the `;` is appended, which moves no offset either.
    let mut append = false;
    for (error, &at) in parsed.errors.iter().enumerate() {
        if literal.is_some_and(|(i, _)| at >= tokens[i].span.start as usize) {
            continue;
        }
        if parsed.result_terminators.contains(&at) {
            blank(&mut bytes, original, at, at + 1);
            blanked.push((at, at + 1));
            continue;
        }
        match terminator_space(text, &tokens, at) {
            Some(space) => terminators.push((at, space)),
            None if open == 0 && at == text.len() && cut_short_at_end(&tokens, parsed, at) => {
                append = true;
            }
            None => {
                let blanking = member_around(text, &tokens, &strays, parsed, error, retried, keep);
                if blanking.before {
                    taken_before.push(at);
                }
                kept |= blanking.header;
                let end = match literal {
                    Some((_, line_end)) => blanking.end.min(line_end),
                    None => blanking.end,
                };
                blank(&mut bytes, original, blanking.start, end);
                blanked.push((blanking.start, end));
            }
        }
    }
    // A declaration blanked for another error takes no terminator.
    for (at, space) in terminators {
        if !blanked.iter().any(|&(start, end)| start < at && at <= end) {
            bytes[space] = b';';
        }
    }
    let mut text = into_text(bytes);
    if append
        && !blanked
            .iter()
            .any(|&(start, end)| start < text.len() && text.len() <= end)
    {
        text.push(';');
    }
    close_braces(&mut text);
    Round {
        text,
        taken_before,
        kept,
    }
}

/// The literal left open in `text` — a string, quoted name, comment or
/// note the lexer ran past its own line to the end of the text, as one
/// error token — as its token's index and where the line it starts on
/// ends. A quote left open pairs with the next of its kind, and each
/// literal after it with the wrong quotes, until the last runs to the
/// end: the quote left open is then the one opening a literal of its
/// kind across lines, or that last one. Each is taken in turn for the
/// quote left open (the first [`CANDIDATES`] and the last): taken away,
/// its line on, the right one leaves the fewest literals across lines,
/// which people rarely write; among equals — a literal written across
/// lines, which any taking leaves one of — the one the unit parses the
/// most members without (the member it opens blanked through its line,
/// as a round blanks it), then the fewest errors, the first of equals
/// winning.
fn open_literal(
    text: &str,
    tokens: &[Token],
    parsed: &Parsed,
    kerml: bool,
) -> Option<(usize, usize)> {
    let spans_lines = |text: &str, t: &Token| {
        text.get(t.span.start as usize..t.span.end as usize)
            .is_some_and(|t| t.contains('\n'))
    };
    let last = parsed.errors.iter().find_map(|&at| {
        let i = tokens.partition_point(|t| (t.span.end as usize) <= at);
        let token = tokens.get(i)?;
        (token.kind == TokenKind::Error
            && token.span.start as usize == at
            && spans_lines(text, token))
        .then_some(i)
    })?;
    let line_end = |i: usize| {
        let start = tokens[i].span.start as usize;
        text[start..].find('\n').map_or(text.len(), |n| start + n)
    };
    let kind = match text.as_bytes()[tokens[last].span.start as usize] {
        b'"' => TokenKind::String,
        b'\'' => TokenKind::UnrestrictedName,
        _ => return Some((last, line_end(last))),
    };
    let mut candidates: Vec<usize> = (0..last)
        .filter(|&i| tokens[i].kind == kind && spans_lines(text, &tokens[i]))
        .take(CANDIDATES)
        .collect();
    if candidates.is_empty() {
        return Some((last, line_end(last)));
    }
    candidates.push(last);
    // The text with `from` blanked through a candidate's line.
    let without = |from: usize, i: usize| {
        let mut bytes = text.as_bytes().to_vec();
        blank(&mut bytes, text, from, line_end(i));
        into_text(bytes)
    };
    // The literals across lines (or left open) the text leaves with a
    // candidate's quote taken away, its line on.
    let across = |i: usize| {
        let text = without(tokens[i].span.start as usize, i);
        sysmlv2_parser::lexer::tokenize(&text)
            .0
            .iter()
            .filter(|t| matches!(t.kind, TokenKind::Error) || t.kind == kind)
            .filter(|t| spans_lines(&text, t))
            .count()
    };
    let scored: Vec<(usize, usize)> = candidates.iter().map(|&i| (across(i), i)).collect();
    let fewest = scored.iter().map(|&(n, _)| n).min()?;
    let tied: Vec<usize> = scored
        .into_iter()
        .filter(|&(n, _)| n == fewest)
        .map(|(_, i)| i)
        .collect();
    let chosen = match tied[..] {
        [only] => only,
        // Among equals, the unit with the member a candidate opens
        // blanked through its line, as a round blanks it.
        _ => tied.into_iter().min_by_key(|&i| {
            let text = without(member_start(&tokens[..i], parsed, false), i);
            let parse = if kerml {
                sysmlv2_parser::parser::parse_kerml_source(&text)
            } else {
                sysmlv2_parser::parser::parse_source(&text)
            };
            let mut members = MemberEnds::default();
            members.visit_unit(&parse.unit);
            (std::cmp::Reverse(members.0.len()), parse.diagnostics.len())
        })?,
    };
    Some((chosen, line_end(chosen)))
}

/// How many literals across lines [`open_literal`] weighs, before the
/// one the lexer ran to the end of the text.
const CANDIDATES: usize = 8;

/// Does a member the parser kept end at `at`, the end of the text, with
/// a token that cannot end a member — the declaration cut short there,
/// its `;` all that is missing?
fn cut_short_at_end(tokens: &[Token], parsed: &Parsed, at: usize) -> bool {
    let last = tokens.iter().rev().find(|t| t.kind != TokenKind::Eof);
    parsed.missing_at(at)
        && parsed.ends_member_at(at)
        && last.is_some_and(|t| t.span.end as usize == at && !terminates(t))
}

/// Where a missing `;` reported at byte `at` can be written without
/// moving an offset: a whitespace byte between the declaration's last
/// token and the next one, outside any comment — a space or a tab, the
/// next line's indentation as a rule, else the line break itself. The
/// parser reports a declaration missing its terminator at the end of its
/// last token, when the next line starts another member, and reads on
/// as if the `;` were there: writing it keeps the declaration the parser
/// kept. `None` for any other error.
fn terminator_space(text: &str, tokens: &[Token], at: usize) -> Option<usize> {
    let ended = tokens.iter().any(|t| t.span.end as usize == at);
    let next = tokens
        .iter()
        .find(|t| t.span.start as usize >= at)?
        .span
        .start as usize;
    if !ended || next == at {
        return None;
    }
    let gap = text.get(at..next)?;
    let spaces: Vec<usize> = sysmlv2_parser::lexer::tokenize(gap)
        .0
        .into_iter()
        .filter(|t| t.kind == TokenKind::Whitespace)
        .flat_map(|t| t.span.start as usize..t.span.end as usize)
        .collect();
    spaces
        .iter()
        .find(|&&i| matches!(gap.as_bytes()[i], b' ' | b'\t'))
        .or_else(|| spaces.first())
        .map(|&i| at + i)
}

/// The tokens the parser reads (trivia dropped), `Eof` last.
fn significant_tokens(text: &str) -> Vec<Token> {
    sysmlv2_parser::lexer::tokenize(text)
        .0
        .into_iter()
        .filter(|t| !t.kind.is_trivia())
        .collect()
}

/// The member declaration the syntax error `error` belongs to, as the
/// byte range to blank. It starts just after the member boundary before
/// it ([`member_start`]). It ends where the error is when that is
/// between tokens (a missing `;` is reported at the end of the
/// declaration's line), and at the end of the token before the one the
/// error was reported at when the parser only found out there that the
/// member had ended ([`ended_before`]); otherwise where [`member_extent`]
/// puts the end of a member in error at that token. An error at a `}`
/// nothing is open for is that closer's own, which balancing the braces
/// blanks. One at a `}` right after a `;` or a `}` that ends no member
/// the parser kept belongs to the member that token is part of — a `}`
/// closing a body its value opened (`f({ in i; i }`), say — which goes
/// whole. An error the last round took for the member before it and
/// still reported where it was (`retried`), which blanking that member
/// did not clear, is the member's at it. With `keep`, a member whose
/// header is in error keeps the body it opens: what is blanked is the
/// header from the error up to the body's `{` — from the token before,
/// when the error is at the `{` — as long as some of the header stays;
/// and a body opened right after a `}` nothing is open for waits for
/// balancing to blank that `}`.
fn member_around(
    text: &str,
    tokens: &[Token],
    strays: &[usize],
    parsed: &Parsed,
    error: usize,
    retried: &[usize],
    keep: bool,
) -> Blanking {
    let at = parsed.errors[error];
    // The first token ending past the error: the one it was reported at.
    let i = tokens
        .partition_point(|t| (t.span.end as usize) <= at)
        .min(tokens.len().saturating_sub(1));
    let token = &tokens[i];
    let Some(prev) = i.checked_sub(1).map(|p| &tokens[p]) else {
        return Blanking::of(0, member_extent(text, tokens).0);
    };
    if at < token.span.start as usize {
        let start = member_start(&tokens[..i], parsed, true);
        return Blanking::of(start, at);
    }
    let stray = |t: &Token| strays.binary_search(&(t.span.start as usize)).is_ok();
    // A `}` nothing is open for is its own error, and a body opened right
    // after one is the body of the declaration before it, which
    // balancing the braces gives back.
    if stray(token) || (keep && token.kind == TokenKind::LBrace && stray(prev)) {
        return Blanking::of(at, at);
    }
    if ended_before(text, tokens, parsed, i, error) {
        let start = member_start(&tokens[..i], parsed, true);
        // Still reported where the last round took it for the member
        // before, the error is the member's at it — unless the member
        // before leaves a group open, whose close the parser reports
        // here: blanking stopped short of that member's start, at a `;`
        // inside the group.
        if !retried.contains(&at) || leaves_group_open(tokens, start, i) {
            return Blanking {
                before: true,
                ..Blanking::of(start, prev.span.end as usize)
            };
        }
    }
    let own = token.kind == TokenKind::RBrace
        && matches!(prev.kind, TokenKind::Semi | TokenKind::RBrace)
        && !parsed.ends_member(prev);
    let start = member_start(&tokens[..i], parsed, own);
    let (end, body) = member_extent(text, &tokens[i..]);
    if let Some(body) = body.filter(|_| keep) {
        let from = if token.span.start as usize == body {
            prev.span.start as usize
        } else {
            token.span.start as usize
        };
        // Some of the header stays: the member's first token is before
        // what goes.
        let first = tokens[..i].iter().find(|t| t.span.start as usize >= start);
        if first.is_some_and(|t| (t.span.start as usize) < from) {
            return Blanking {
                header: true,
                ..Blanking::of(from, body)
            };
        }
    }
    Blanking::of(start, end)
}

/// The byte range [`member_around`] blanks for an error, and how it
/// came by it.
struct Blanking {
    start: usize,
    end: usize,
    /// The error was taken for the member before it.
    before: bool,
    /// Only a header in error goes; the body it opens stays.
    header: bool,
}

impl Blanking {
    /// `start..end`, the range never ending before it starts.
    fn of(start: usize, end: usize) -> Blanking {
        Blanking {
            start,
            end: end.max(start),
            before: false,
            header: false,
        }
    }
}

/// Do the tokens from byte `start` up to `tokens[end]` leave a `(` or
/// a `[` open?
fn leaves_group_open(tokens: &[Token], start: usize, end: usize) -> bool {
    let from = tokens.partition_point(|t| (t.span.start as usize) < start);
    let mut depth = 0usize;
    for t in tokens.get(from..end).unwrap_or_default() {
        match t.kind {
            TokenKind::LParen | TokenKind::LBracket => depth += 1,
            TokenKind::RParen | TokenKind::RBracket => depth = depth.saturating_sub(1),
            _ => {}
        }
    }
    depth > 0
}

/// Whether the member the syntax error `error`, reported at
/// `tokens[i]`, belongs to ended with the token before. The parser
/// reads a line break in an unfinished declaration as its end when the
/// next line could start a member — a group or a name left open, a
/// value left out — and reports what it missed at that next line's
/// first token. A declaration it did not keep then has its error there;
/// one it kept has the `;` it found missing reported at its end as
/// well, after the error: the parser reports a member's errors in the
/// order it reads them, the missing `;` last — an error reported after
/// that one is the next member's own. Not after a body opening, where
/// the next line starts the body's first member.
fn ended_before(text: &str, tokens: &[Token], parsed: &Parsed, i: usize, error: usize) -> bool {
    let (prev, token) = (&tokens[i - 1], &tokens[i]);
    if !starts_member_line(text, prev, token) || prev.kind == TokenKind::LBrace {
        return false;
    }
    let end = prev.span.end as usize;
    match parsed.missing_reported(end) {
        Some(missing) => error < missing,
        None => !parsed.ends_member_at(end),
    }
}

/// Does `token` start a later line than `prev` with a token that could
/// start a member — where the parser takes a declaration missing its
/// terminator to have ended? The keyword connectives continue an
/// expression instead.
fn starts_member_line(text: &str, prev: &Token, token: &Token) -> bool {
    let gap = text.get(prev.span.end as usize..token.span.start as usize);
    let could_start = match token.kind {
        TokenKind::Ident => !matches!(token.text(text), "and" | "or" | "xor" | "implies"),
        kind => matches!(
            kind,
            TokenKind::RegularComment
                | TokenKind::At
                | TokenKind::Hash
                | TokenKind::RBrace
                | TokenKind::Eof
        ),
    };
    could_start && gap.is_some_and(|gap| gap.contains('\n'))
}

/// Where the member that ends with `tokens` (or with an error right
/// after them) starts: just after the last member boundary among them,
/// or at the start of the text. Outside any group, a `;` or a `}` is a
/// boundary, the way the parser's recovery ends a member; so is a `{`
/// opening the body the member is in, or the end of a member the parser
/// kept ([`Parsed::ends_member`]) — both also inside a `(` or `[` group
/// left unmatched, but not inside a body of the member's own (one its
/// value opens), whose members are the member's too. With `own_last`
/// the last of `tokens` is the member's own, a boundary or not.
fn member_start(tokens: &[Token], parsed: &Parsed, own_last: bool) -> usize {
    use TokenKind as K;
    // The closers read whose openers have not been, innermost last.
    let mut open: Vec<K> = Vec::new();
    for (k, t) in tokens.iter().rev().enumerate() {
        let in_body = open.contains(&K::RBrace);
        let boundary = (!in_body && (t.kind == K::LBrace || parsed.ends_member(t)))
            || (open.is_empty() && matches!(t.kind, K::Semi | K::RBrace));
        if boundary && !(own_last && k == 0) {
            return t.span.end as usize;
        }
        let closer = match t.kind {
            K::RParen | K::RBracket | K::RBrace => {
                open.push(t.kind);
                continue;
            }
            K::LParen => K::RParen,
            K::LBracket => K::RBracket,
            K::LBrace => K::RBrace,
            _ => continue,
        };
        // An opener closes its closer and whatever was left unmatched
        // since; with no closer for it, it is left unmatched itself.
        if open.contains(&closer) {
            while open.pop().is_some_and(|kind| kind != closer) {}
        }
    }
    0
}

/// Where a member in error starting at `tokens[0]` ends, the way the
/// parser's recovery skips one: through the `;` that ends it outside
/// any group, or the `}` that closes a body it opened — never past a
/// `}` it did not open, which closes the body around it. Like the
/// recovery, it takes a `)` or `]` to close whatever group was opened
/// last. It ends before a later line that could start a member, too,
/// unless a body it opened is still open there: the parser reads an
/// unfinished declaration as ended there (see [`ended_before`]), and
/// the next line keeps its own meaning. With the end, where the body
/// the member ends with opens — its `{`, when it ends with one.
fn member_extent(text: &str, tokens: &[Token]) -> (usize, Option<usize>) {
    use TokenKind as K;
    // The groups the member opened and has not closed, innermost last.
    let mut open: Vec<K> = Vec::new();
    // The `{` opened with nothing else open.
    let mut body = None;
    for (k, t) in tokens.iter().enumerate() {
        let body_open = open.contains(&K::LBrace);
        if k > 0 && !body_open && starts_member_line(text, &tokens[k - 1], t) {
            return (tokens[k - 1].span.end as usize, None);
        }
        match t.kind {
            K::LBrace => {
                if open.is_empty() {
                    body = Some(t.span.start as usize);
                }
                open.push(t.kind);
            }
            K::LParen | K::LBracket => open.push(t.kind),
            K::RParen | K::RBracket => {
                open.pop();
            }
            // A body the member opened closes, and with it whatever was
            // left open inside it.
            K::RBrace if body_open => {
                while open.pop().is_some_and(|kind| kind != K::LBrace) {}
                if open.is_empty() {
                    return (t.span.end as usize, body);
                }
            }
            K::RBrace | K::Eof => return (t.span.start as usize, None),
            K::Semi if open.is_empty() => return (t.span.end as usize, None),
            _ => {}
        }
    }
    (
        tokens.last().map_or(text.len(), |t| t.span.end as usize),
        None,
    )
}

/// Blank `bytes[start..end]` of a text made from `original`: every byte
/// but line breaks becomes a space — a line break the original held
/// there, which a `;` was written over, included — so no offset moves
/// and no line merges.
fn blank(bytes: &mut [u8], original: &str, start: usize, end: usize) {
    let original = original.as_bytes();
    for (i, b) in bytes.iter_mut().enumerate().take(end).skip(start) {
        *b = match original.get(i) {
            Some(&o @ (b'\n' | b'\r')) => o,
            _ if matches!(*b, b'\n' | b'\r') => *b,
            _ => b' ',
        };
    }
}

/// Bytes back to text. Blanked ranges start and end on token
/// boundaries, so the bytes stay UTF-8; the lossy fallback only keeps a
/// misjudged range from ending the request.
fn into_text(bytes: Vec<u8>) -> String {
    String::from_utf8(bytes).unwrap_or_else(|e| String::from_utf8_lossy(e.as_bytes()).into_owned())
}

/// Balance braces: blank each `}` nothing is open for, and close what
/// is still open at the end of the text.
fn close_braces(text: &mut String) {
    let (stray, open) = brace_balance(&significant_tokens(text));
    if !stray.is_empty() {
        let mut bytes = std::mem::take(text).into_bytes();
        for at in stray {
            bytes[at] = b' ';
        }
        *text = into_text(bytes);
    }
    for _ in 0..open {
        text.push_str("\n}");
    }
}

/// Where among `tokens` a `}` closes nothing, in order, and how many
/// bodies are still open after the last of them.
fn brace_balance(tokens: &[Token]) -> (Vec<usize>, usize) {
    let mut stray = Vec::new();
    let mut open = 0usize;
    for t in tokens {
        match t.kind {
            TokenKind::LBrace => open += 1,
            TokenKind::RBrace if open == 0 => stray.push(t.span.start as usize),
            TokenKind::RBrace => open -= 1,
            _ => {}
        }
    }
    (stray, open)
}

#[cfg(test)]
mod tests {
    use super::{SalvageCache, salvage, typed_statement_cut};
    use crate::position::offset32;

    fn parses(text: &str) -> bool {
        !sysmlv2_parser::parser::parse_source(text).has_errors()
    }

    /// The text [`typed_statement_cut`] leaves out of `marked`, whose
    /// `^` marks the statement start and `|` the cursor.
    fn cut(marked: &str) -> String {
        let start = marked.find('^').expect("statement start mark");
        let text = marked.replacen('^', "", 1);
        let cursor = text.find('|').expect("cursor mark");
        let text = text.replacen('|', "", 1);
        let span = typed_statement_cut(&text, offset32(start), offset32(cursor));
        text[span.start as usize..span.end as usize].to_string()
    }

    #[test]
    fn the_cut_takes_the_statement_being_typed() {
        for (marked, expected) in [
            // through the line
            (
                "part def P {\n^  attribute m = v.|\n  attribute n;\n}",
                "  attribute m = v.",
            ),
            // not the closer of the body around it
            ("part def P {^ attribute m = v.| }", " attribute m = v. "),
            ("assert constraint {^ f(v.| }", " f(v. "),
            // groupings it opened itself, and its own terminator
            (
                "part def P {^ attribute m = f(v.|) + 1; attribute n; }",
                " attribute m = f(v.) + 1;",
            ),
            // a body it opens after the cursor, across lines
            (
                "part def P {\n^  part x :> v.| {\n    attribute a;\n  }\n  part y;\n}",
                "  part x :> v. {\n    attribute a;\n  }",
            ),
        ] {
            assert_eq!(cut(marked), expected, "{marked:?}");
        }
    }

    #[test]
    fn a_workspace_is_salvaged_unit_by_unit_and_remembered() {
        let clean = "package A { part def X; }\n";
        let broken = "package B {\n  attribute x = ;\n  part def Y;\n}\n";
        let units = |b: &str| {
            vec![
                ("a.sysml".to_string(), clean.to_string()),
                ("b.sysml".to_string(), b.to_string()),
            ]
        };
        let mut cache = SalvageCache::default();
        for _ in 0..2 {
            let out = cache.salvage_all(units(broken));
            assert_eq!(out[0].1, clean, "a unit that parses stays as it is");
            assert!(parses(&out[1].1), "{:?}", out[1].1);
            assert!(out[1].1.contains("part def Y;"), "{:?}", out[1].1);
        }
        // A new text is salvaged afresh, not answered from memory.
        let fixed = "package B {\n  attribute x = 1;\n  part def Y;\n}\n";
        assert_eq!(cache.salvage_all(units(fixed))[1].1, fixed);
    }

    #[test]
    fn parsing_text_is_unchanged() {
        let text = "package P { part def A; }\n";
        assert_eq!(salvage(text, false).as_deref(), Some(text));
    }

    #[test]
    fn a_missing_value_blanks_its_own_declaration() {
        // The parser reports the missing expression at the `;` in its
        // place, which ends the declaration: the declaration is blanked
        // through it, and the member after it survives, on the same line
        // or the next.
        for text in [
            "package P { attribute x = ; part def Y; }\n",
            "package P {\n  attribute x = ;\n  part def Y;\n}\n",
        ] {
            let out = salvage(text, false).expect("salvaged");
            assert!(parses(&out), "{out}");
            assert_eq!(out.len(), text.len(), "offsets hold");
            assert!(!out.contains("attribute x"), "{out}");
            assert!(out.contains("part def Y;"), "{out}");
        }
    }

    #[test]
    fn a_member_in_error_is_blanked_in_place() {
        let text = "package P {\n  part def A {\n    attribute x : = 5;\n  }\n  part a : A;\n}\n";
        let out = salvage(text, false).expect("salvaged");
        assert!(parses(&out), "{out}");
        assert_eq!(out.len(), text.len(), "offsets hold");
        assert!(!out.contains("attribute"), "{out}");
        assert!(out.contains("part a : A;"), "the rest survives: {out}");
        assert_eq!(out.lines().count(), text.lines().count(), "lines hold");
    }

    #[test]
    fn a_missing_terminator_is_written_where_the_parser_assumed_it() {
        // A declaration with no terminator, the next line another member.
        let text = "package P {\n  attribute y : Real\n  attribute z;\n}\n";
        let out = salvage(text, false).expect("salvaged");
        assert!(parses(&out), "{out}");
        assert_eq!(out.len(), text.len(), "offsets hold");
        assert_eq!(out.lines().count(), text.lines().count(), "lines hold");
        for kept in ["attribute y : Real", "attribute z;"] {
            assert!(out.contains(kept), "{kept} kept: {out}");
        }
        // With no indentation to write into, the line break takes it.
        let text = "package P {\nattribute y : Real\nattribute z;\n}\n";
        let out = salvage(text, false).expect("salvaged");
        assert!(parses(&out), "{out}");
        assert!(out.contains("attribute y : Real;attribute z;"), "{out}");
    }

    #[test]
    fn an_unclosed_body_is_closed_at_the_end() {
        let text = "package P {\n  part def A {\n    attribute x;\n  part def B { part c; }\n}\n";
        let out = salvage(text, false).expect("salvaged");
        assert!(parses(&out), "{out}");
        assert!(out.starts_with(text), "only appended to: {out}");
    }

    #[test]
    fn a_stray_closer_is_blanked() {
        let text = "package P { part def A; } }\npart def B;\n";
        let out = salvage(text, false).expect("salvaged");
        assert!(parses(&out), "{out}");
        assert!(out.contains("part def B;"), "{out}");
    }

    #[test]
    fn a_missing_terminator_at_the_end_of_a_kerml_unit() {
        let text = "package K {\n  private import ScalarValues::*;\n  feature m : Real\n";
        let out = salvage(text, true).expect("salvaged");
        assert!(
            !sysmlv2_parser::parser::parse_kerml_source(&out).has_errors(),
            "{out}"
        );
        assert!(out.contains("private import ScalarValues::*;"), "{out}");
        assert!(out.contains("feature m : Real;"), "{out}");
    }

    /// `text` salvaged, checked to parse with every offset and line in
    /// place.
    fn salvaged(text: &str) -> String {
        let out = salvage(text, false).expect("salvaged").into_owned();
        assert!(parses(&out), "{out}");
        assert_eq!(out.len(), text.len(), "offsets hold: {out}");
        assert_eq!(out.lines().count(), text.lines().count(), "lines hold");
        out
    }

    /// `text` with the first `member` in it blanked, line breaks kept.
    fn without(text: &str, member: &str) -> String {
        let blank = member.bytes().map(|b| if b == b'\n' { '\n' } else { ' ' });
        text.replacen(member, &blank.collect::<String>(), 1)
    }

    /// A member whose value is left out before the `}` closing the body
    /// around it goes whole — the parser reports the missing expression
    /// at the `;` where the value goes, which still ends the member — as
    /// does one whose value opens a body and closes it there; the body
    /// around them stays.
    #[test]
    fn a_member_cut_short_before_the_closing_brace_goes_whole() {
        for (body, member) in [
            ("part z", "attribute = ;"),
            ("part z", "attribute q = (1 + ;"),
            ("perform action a", "in x = ;"),
            ("part z", "attribute a = f({ in i; i }"),
        ] {
            let text = format!(
                "package P {{\n    part def V {{ attribute m; }}\n    {body} {{ {member} }}\n    part v : V;\n}}\n"
            );
            assert_eq!(salvaged(&text), without(&text, member), "{text}");
        }
    }

    /// A member left unfinished at the end of its line — a group or a
    /// name left open, an operand left out — is one the parser reports
    /// at the next line's first token, whether that starts a member of
    /// its own (read or not) or closes the body: that member goes alone,
    /// with no terminator written for it, and the next line stays.
    #[test]
    fn a_member_left_unfinished_at_the_end_of_its_line_goes_alone() {
        for member in [
            "attribute q = (1 + ;",
            "attribute q = f(1, ;",
            "attribute q = (1 + 2",
            "attribute q = 1 +",
            "attribute m = 5 [kg",
            "attribute q = v.",
            "part x [1..",
            "part x : V::",
        ] {
            for text in [
                format!("package P {{\n    part def V;\n    {member}\n    part v : V;\n}}\n"),
                format!(
                    "package P {{\n    part def V;\n    part w {{\n        {member}\n    }}\n}}\n"
                ),
            ] {
                assert_eq!(salvaged(&text), without(&text, member), "{text}");
            }
        }
        // The next line in error too, each goes alone.
        let text = "package P {\n    attribute q = 1 +\n    private import\n    part v;\n}\n";
        let out = without(&without(text, "attribute q = 1 +"), "private import");
        assert_eq!(salvaged(text), out);
        // A tail left unfinished after a body goes without the body.
        let text = "package P {\n    action a {\n        loop action l {\n            action m;\n        } until x >=\n        then action n;\n    }\n}\n";
        assert_eq!(salvaged(text), without(text, "until x >="));
    }

    /// A member missing only its `;` is kept, the `;` written, before a
    /// member in error on the next line, whose error — reported after
    /// the missing `;` — is that member's own; so is an error on the
    /// first line of a body. A member the parser kept unfinished on its
    /// line, reporting what it missed at the token after, goes with the
    /// member in error at that token.
    #[test]
    fn a_member_missing_its_terminator_is_kept_before_one_in_error() {
        for next in ["attribute z : = 5;", "x y;", "to x;"] {
            let text = format!("package P {{\n    attribute y : Real\n    {next}\n}}\n");
            let kept = format!("package P {{\n    attribute y : Real\n;   {next}\n}}\n");
            assert_eq!(salvaged(&text), without(&kept, next), "{text}");
        }
        let text = "package P {\n    part w { attribute a = 1; import X::; }\n    part v;\n}\n";
        assert_eq!(salvaged(text), without(text, "import X::;"));
        let text = "package P {\n    part def V {\n        to x;\n    }\n}\n";
        assert_eq!(salvaged(text), without(text, "to x;"));
    }

    /// A `)` whose `(` is gone does not stand for every boundary before
    /// it, nor a `}` inside a group for a body the member opened; a `[`
    /// left open does not take the `}` closing the body around the member
    /// for its own, while a `]` closes the `{` opened after the `[`, as
    /// the parser's recovery reads it; a `}` nothing is open for is an
    /// error of its own, which leaves the member before it be.
    #[test]
    fn unmatched_groupings_leave_the_members_around_them_be() {
        let text = "package P {\n    part a;\n    part b = f(x));\n    part c;\n}\n";
        assert_eq!(salvaged(text), without(text, "part b = f(x));"));
        let text = "package P {\n    assert constraint c {\n        (1..n)->forAll {in i;\n            s#(i+} 1);\n";
        let out = salvage(text, false).expect("salvaged");
        assert_eq!(out, without(text, "s#(i+} 1);") + "\n}\n}\n}");
        let text = "package P {\n    part w { attribute q = [ }\n    part v;\n}\n";
        assert_eq!(salvaged(text), without(text, "attribute q = ["));
        let text = "package P {\n    part def D {\n        part p : Q[*{ ] :>> r;\n        part s;\n    }\n}\n";
        assert_eq!(salvaged(text), without(text, "part p : Q[*{ ] :>> r;"));
        assert_eq!(
            salvaged("part def V;\npart x : V\n}\n"),
            "part def V;\npart x : V\n;\n"
        );
    }

    /// A `;` after a body's result expression is the only thing in
    /// error there: it goes, and the result stays.
    #[test]
    fn a_terminator_after_a_result_goes_alone() {
        for (text, spare) in [
            (
                "package P {\n    calc def F { in x : Real; x * 2; }\n    part v;\n}\n",
                "x * 2;",
            ),
            (
                "package P {\n    calc def F { in x : Real; x * 2;; }\n    part v;\n}\n",
                "x * 2;;",
            ),
            (
                "package P {\n    calc def F {\n        in x : Real;\n        x * 2;\n    }\n}\n",
                "x * 2;",
            ),
        ] {
            let result = spare.trim_end_matches(';');
            let kept = format!("{result}{}", " ".repeat(spare.len() - result.len()));
            assert_eq!(salvaged(text), text.replacen(spare, &kept, 1), "{text}");
        }
    }

    /// A member the parser kept, cut short at the very end of the text
    /// with nothing after it — no line break to write its `;` into, no
    /// body around it for balancing to close — takes a `;` after it.
    #[test]
    fn a_member_cut_short_at_the_end_of_the_text_is_terminated() {
        for (text, kept) in [
            ("part def V;\nprivate import X::*", "private import X::*;"),
            ("package P { part v; }\nalias A for P", "alias A for P;"),
        ] {
            let out = salvage(text, false).expect("salvaged").into_owned();
            assert!(parses(&out), "{out}");
            assert!(out.starts_with(text), "offsets hold: {out}");
            assert!(out.ends_with(kept), "{out}");
        }
    }

    /// An error still reported where it was once the member before it
    /// was blanked for it is the member's at it. Where the parser kept
    /// none of the members before the error — it read them into the body
    /// of an expression a stray `{` opened — the member just before is
    /// lost, not every one back to the `{`, one a round, until the rounds
    /// run out.
    #[test]
    fn an_error_that_blanking_the_member_before_left_is_its_own() {
        let text = "package P {\n    { part a1;\n    part a2;\n    part a3;\n    part a4;\n    \
                    part a5;\n    def C :> D { part e; }\n    part f;\n}\n";
        let out = salvage(text, false).expect("salvaged");
        let gone = without(&without(text, "part a5;"), "def C :> D { part e; }");
        assert_eq!(out, gone + "\n}");
    }

    /// A member that leaves a group open at its `;` (`f(1, ;`) is
    /// reported at that `;`, which still ends it: the member goes through
    /// its `;`, the stray line after it goes on its own, and the members
    /// around them stay.
    #[test]
    fn a_group_left_open_at_its_terminator_ends_the_member_there() {
        let text = "package P {\n    part a;\n    attribute q = f(1, ;\n    /\n    part b { part c; }\n    part d;\n}\n";
        let gone = without(&without(text, "attribute q = f(1, ;"), "/");
        assert_eq!(salvaged(text), gone);
    }

    /// A member the parser read on into the definition on the next line
    /// — a `return` left without its feature takes that definition for
    /// one, and reports so at the line after — goes with the definition,
    /// body and all; the member after it stays.
    #[test]
    fn a_member_that_read_on_into_a_body_goes_with_it() {
        let text = "package K {\n    function f { in x: Integer[1]; return\n    function g { in y: Integer[1]; }\n    function h { in z: Integer[1]; }\n}\n";
        let out = salvage(text, true).expect("salvaged");
        let gone = without(text, "return");
        assert_eq!(
            out,
            without(&gone, "function g { in y: Integer[1]; }") + "\n}"
        );
    }

    /// A declaration whose header does not parse — a stray `}` in its
    /// name, a second name, a specialization naming nothing — keeps its
    /// body: salvage blanks the header from the error up to the body's
    /// `{` (the token before, when the error is at the `{`), so the
    /// declaration and its members survive.
    #[test]
    fn a_header_in_error_keeps_its_body() {
        for (text, gone) in [
            (
                "package Foo Bar {\n    part def V;\n    part v : V;\n}\n",
                "Bar",
            ),
            (
                "package Fo}o {\n    part def V;\n    part v : V;\n}\n",
                "}o",
            ),
            ("package Foo} {\n    part def V;\n    part v : V;\n}\n", "}"),
            (
                "package P {\n  part def X :> { attribute a; }\n  part def Y;\n}\n",
                ":>",
            ),
        ] {
            assert_eq!(salvaged(text), without(text, gone), "{text}");
        }
        // A header in error from its first token leaves nothing for the
        // body to belong to: the declaration goes whole, at once.
        for text in [
            "package P {\n    123 {\n        part x;\n    }\n    part y;\n}\n",
            "package P {123 {\n        part x;\n    }\n    part y;\n}\n",
        ] {
            let gone = without(text, "123 {\n        part x;\n    }");
            let parsed = super::Parsed::of(text, false);
            assert_eq!(
                super::repair(text, text, &parsed, &[], false, true).text,
                gone
            );
        }
    }

    /// A string, quoted name, comment or note left open runs to the end
    /// of the text as the lexer reads it, and would take every member
    /// after it along: salvage ends it at its own line — blanking it with
    /// the member it opens, which an error before it does not stretch
    /// past that line either — and keeps what follows.
    #[test]
    fn a_literal_left_open_ends_at_its_own_line() {
        for open in [
            "attribute a = \"open",
            "part 'open",
            "/* open",
            "//* open",
            "attribute a = f(1 +, \"open",
        ] {
            let text = format!("package P {{\n    part def V;\n    {open}\n    part v : V;\n}}\n");
            assert_eq!(salvaged(&text), without(&text, open), "{text}");
        }
        // A quote left open pairs with the next one of its kind, and the
        // literals after it with the wrong quotes, until the last runs to
        // the end: the literal left open is the first to span a line.
        for open in ["attribute a = \"open", "part 'open"] {
            let text = format!(
                "package P {{\n    part def V;\n    {open}\n    attribute b = \"x\";\n    \
                 part 'y' : V;\n    attribute c = \"z\";\n    part v : V;\n}}\n"
            );
            assert_eq!(salvaged(&text), without(&text, open), "{text}");
        }
        // A string spanning lines before a name left open is not the
        // literal left open.
        let text = "package P {\n    part def V;\n    attribute s = \"two\nlines\";\n    \
                    part 'open\n    part v : V;\n}\n";
        assert_eq!(salvaged(text), without(text, "part 'open"));
    }

    /// A string or a name spanning lines as written — above a quote left
    /// open, two of them, below one — is no literal left open, nor is
    /// one above a comment left open: only the member that opens the
    /// literal left open goes.
    #[test]
    fn a_literal_spanning_lines_as_written_is_not_one_left_open() {
        let note = "attribute note = \"first line\nsecond line\";";
        for text in [
            format!(
                "package P {{\n    {note}\n    part def V;\n    attribute a = \"open\n    part v : V;\n}}\n"
            ),
            format!(
                "package P {{\n    {note}\n    attribute n = \"third line\nfourth line\";\n    \
                 part def V;\n    attribute a = \"open\n    part v : V;\n}}\n"
            ),
            format!(
                "package P {{\n    part def V;\n    attribute a = \"open\n    {note}\n    part v : V;\n}}\n"
            ),
            "package P {\n    part 'first\nline' : V;\n    part def V;\n    part 'open\n    \
             part v : V;\n}\n"
                .to_string(),
        ] {
            let open = if text.contains("part 'open") {
                "part 'open"
            } else {
                "attribute a = \"open"
            };
            assert_eq!(salvaged(&text), without(&text, open), "{text}");
        }
        let text = format!(
            "package P {{\n    {note}\n    part def V;\n    /* open\n    part v : V;\n}}\n"
        );
        assert_eq!(salvaged(&text), without(&text, "/* open"), "{text}");
    }

    /// A `;` written over a line break — no other whitespace there to
    /// take it — that a later round blanks gives the line break back:
    /// every line keeps its place.
    #[test]
    fn a_terminator_over_a_line_break_gives_it_back() {
        let text = "package P {\n    part x [1..\n/* c */\n}\n";
        let out = salvaged(text);
        assert_eq!(out, without(text, "part x [1.."));
    }

    /// Where keeping a body — or what follows a literal left open — does
    /// not get the text to parse within the rounds, salvage blanks the
    /// members in error whole, as it did before: a `{` typed into a
    /// flow's header takes the header apart a token a round.
    #[test]
    fn keeping_more_gives_way_to_blanking_whole() {
        let text = "package P {\n    action def A {\n        action a;\n        action b;\n        \
                    flow from a.x.y { to b.x;\n    }\n    part v;\n}\n";
        let kept = super::rounds(text, false, super::Parsed::of(text, false), true);
        assert_eq!(kept, (None, true));
        let out = salvage(text, false).expect("salvaged");
        assert!(parses(&out), "{out}");
        assert!(out.contains("part v;"), "{out}");
    }
}
