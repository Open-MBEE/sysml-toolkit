//! Where a completion request's cursor sits. One pass over the
//! toolkit's tokens of the text ahead of the cursor answers what the
//! completion tier must know before it offers anything:
//!
//! - whether there is anything to complete at all. Inside a comment, a
//!   note, a documentation body, or a string literal there is not, and
//!   neither is there inside a number (`5.`, `1.5e`) or at a range bound
//!   (`[0..`, `[1..*`) — not even when a trigger character opened the
//!   request;
//! - where the statement being typed starts: its first token after the
//!   last `;`, `{`, or `}` token, or after a comment body, which ends
//!   the comment, `doc`, or `rep` member it belongs to. Boundaries
//!   inside comments, notes, strings, and quoted names never count;
//! - whether that statement is an import, whether it leaves a `[` open
//!   ahead of the word being completed, and where the quoted name the
//!   cursor is typing opens, if it is typing one;
//! - what the word being completed fills: a name the statement declares
//!   (`part def Boat`, `in item fuel`, an enumeration literal) is new,
//!   so no existing element belongs there — only the keywords the
//!   grammar allows in its place (`part` + `def`);
//! - and otherwise which keywords and which kinds of element the
//!   position takes, best-fitting first: the definitions a usage of the
//!   statement's kind may be typed by after `:` (see
//!   [`crate::kinds::typed_by`]), the definitions a definition may
//!   specialize after `:>`, features after `:>` on a usage and after
//!   `:>>`, expression operands after `=`, the keywords the enclosing
//!   body takes at a statement's start, metadata definitions after `#`
//!   and `@`, the referenced kind after `perform`, `exhibit`, `satisfy`,
//!   …. A position the statement does not tell apart takes everything;
//! - which of the enclosing element's features the position names ahead
//!   of every other name (see [`Members`]): a redefinition its inherited
//!   ones, a succession and a usage's subsetting those in scope, a
//!   metadata body its metadata definition's;
//! - and where measurement units rank among an expression's operands:
//!   after every other name, or first where the statement's type is a
//!   unit type (see [`Want::unit_group`]). Within a group shorter names
//!   rank first (see [`sort_text`]).
//!
//! The declared-name positions are transcribed from the normative
//! grammars into one table per dialect, which a test keeps sorted and
//! made of the dialect's reserved words: each keyword after which the
//! next word is a name being declared, with the keywords that may stand
//! there instead. A keyword whose next word may be a reference is not
//! in the table, so completion stays on after it — `perform` (`perform
//! takePicture`), `then`, `first` — and neither is one whose next word
//! is either a name being declared or a reference, as only the rest of
//! the statement tells: `transition` (`transition t first s …` beside
//! `transition s then t`), `accept`, `flow`, `message`, `interface`,
//! `metadata`, `dependency`, and in KerML `connector`, `binding`,
//! `succession`, and `featuring`.

use crate::kinds::{ALL_DEFINITIONS, CALLABLES, Decl};
use std::collections::HashSet;
use sysmlv2_parser::ast::{DefKind, Dialect, UsageKind};
use sysmlv2_parser::parser::is_reserved;
use sysmlv2_parser::span::Span;
use sysmlv2_parser::token::{Token, TokenKind};

/// What one token pass over the text ahead of the cursor tells about
/// the statement being typed.
pub(crate) struct Scan {
    /// Byte offset where the statement starts: its first token after
    /// the last `;`, `{`, `}`, or comment body token ahead of the cursor
    /// (notes and whitespace skipped), the cursor when it has none yet —
    /// never on the end of the member before it, which a position query
    /// there would take for the enclosing element.
    pub stmt_start: u32,
    /// The statement is an import: `import` is among its words.
    pub import: bool,
    /// The statement leaves a `[` open ahead of the word being
    /// completed — the cursor sits where a quantity's unit is written
    /// (`9.8 [m`). A multiplicity (`[0..*]`) counts too: the tokens
    /// cannot tell the two apart, and names are rarely typed into one.
    pub in_bracket: bool,
    /// The opening quote of the quoted name the cursor is typing
    /// (`'metre per sec|`): the text ahead of the cursor ends in a
    /// quoted name left open on the cursor's line. A quote inside a
    /// comment, a string, or a note never counts, and one left open on
    /// an earlier line runs no further than it (see [`tokens_ahead`]).
    pub quote: Option<u32>,
    /// What the word being completed fills.
    pub slot: Slot,
}

/// What the word being completed fills.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Slot {
    /// Nothing to complete: the cursor is in a comment, a note, a
    /// documentation body, or a string literal, in a number, or at a
    /// range bound.
    Quiet,
    /// A name the statement declares: only these keywords may stand in
    /// its place.
    Declared(Vec<&'static str>),
    /// A position the statement tells apart: the keywords and the kinds
    /// of element it takes.
    Want(Want),
    /// A position the statement does not tell apart: every keyword and
    /// every name.
    Open,
}

/// The body a statement is a member of, as far as the keywords its
/// members start with and the names they declare or take tell apart.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Body {
    /// The root namespace, or a package's or namespace's body.
    Namespace,
    /// The body of a definition or usage of structure: a part, an item,
    /// a port, an attribute, a connection, ….
    Definition,
    /// An action's body, which also takes nodes and successions.
    Action,
    /// A state's body, which also takes entry, do, and exit actions and
    /// transitions.
    State,
    /// A calculation's, a constraint's, or a case's body, ending in a
    /// result expression; a case's also takes a subject, actors, and an
    /// objective.
    Calculation { case: bool },
    /// A requirement's, a concern's, or a viewpoint's body.
    Requirement,
    /// A view's body, which also takes exposures, filters, and
    /// renderings.
    View,
    /// An enumeration definition's body, whose bare members declare
    /// its literals (`enum def Color { red; green; }`).
    Enumeration,
    /// A metadata usage's body, whose members redefine the metadata's
    /// features, naming them as references (`@Safety { ref isMandatory
    /// = true; }`).
    Metadata,
    /// A KerML type's or feature's body.
    Type,
    /// A KerML function's, predicate's, or expression's body, ending in
    /// a result expression.
    Function,
    /// A body its header does not tell.
    Other,
}

/// Scan `text`, written in `dialect`, up to `offset`, the word being
/// completed spanning `word_start..offset`.
pub(crate) fn scan(text: &str, word_start: u32, offset: u32, dialect: Dialect) -> Scan {
    let prefix = &text[..text.floor_char_boundary(offset as usize)];
    let word_start = prefix.floor_char_boundary(word_start as usize);
    let (tokens, line) = tokens_ahead(prefix);
    let last = tokens
        .iter()
        .rev()
        .find(|t| t.kind != TokenKind::Eof)
        .copied();
    // A quoted name being typed (`'Vehicle On`) is the word being
    // completed, from its opening quote on.
    let quoted = last.filter(|t| t.kind == TokenKind::Error && t.text(prefix).starts_with('\''));
    let cut = quoted.map_or(word_start, |q| word_start.min(q.span.start as usize));
    let (begin, depth, bodies) = statement(prefix, &tokens, line);
    let statement = significant(&tokens[begin..]);
    let stmt_start = statement
        .first()
        .map_or(crate::position::offset32(prefix.len()), |t| t.span.start);
    let head: Vec<Token> = statement
        .into_iter()
        .filter(|t| t.span.end as usize <= cut)
        .collect();
    let quiet = quoted.is_none()
        && (last.is_some_and(|t| in_prose(prefix, t)) || in_number(prefix, &tokens, word_start));
    let line_start = prefix.rfind('\n').map_or(0, |i| i + 1);
    Scan {
        stmt_start,
        import: head.iter().any(|t| t.is_kw(prefix, "import")),
        in_bracket: depth > 0,
        quote: quoted
            .map(|q| q.span.start)
            .filter(|&open| open as usize >= line_start),
        slot: if quiet {
            Slot::Quiet
        } else {
            slot(
                prefix,
                &head,
                bodies.last().copied().unwrap_or(Body::Namespace),
                depth > 0,
                dialect,
            )
        },
    }
}

#[cfg(test)]
thread_local! {
    /// Lexes of the whole text ahead of the cursor on this thread, so a
    /// test can pin what one request costs.
    pub(crate) static PREFIX_LEXES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// Where the statement being typed at the end of `prefix`, the text
/// ahead of the cursor lexed as `tokens` and `line` by [`tokens_ahead`],
/// starts: its first token (see [`statement`]), the cursor when it has
/// none yet. Completion cuts this statement out of the model it reads,
/// and so does signature help: the two share one session.
pub(crate) fn statement_begins(prefix: &str, tokens: &[Token], line: Option<usize>) -> u32 {
    let (begin, _, _) = statement(prefix, tokens, line);
    tokens[begin..]
        .iter()
        .find(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof)
        .map_or(crate::position::offset32(prefix.len()), |t| t.span.start)
}

/// A group the text ahead of the cursor leaves open.
#[derive(Clone, Copy)]
enum Group {
    Paren,
    Bracket,
    /// A body: an expression's, passed within a `(` or `[` (`f({ in x;
    /// x }, …)`), keeps where the statement around it began and the
    /// brackets it had open, for that statement goes on past its `}`.
    Brace(Option<(usize, usize)>),
}

/// The statement being typed at the end of `tokens`, the toolkit's
/// tokens of `prefix` (see [`tokens_ahead`]): the index of the token it
/// begins at, how many `[` it leaves open, and the bodies around it,
/// innermost last. A statement begins after a `;`, a `{`, a `}`, or a
/// comment body — but an expression's body passed within a `(` or `[`
/// is part of the statement it sits in (`Twice({ in z; z }, v.|`) — and
/// no earlier than `line`, the token the cursor's line starts at when
/// it is read on its own.
fn statement(prefix: &str, tokens: &[Token], line: Option<usize>) -> (usize, usize, Vec<Body>) {
    // Groups a statement left open end with it, back to its body.
    fn settle(groups: &mut Vec<Group>) {
        while matches!(groups.last(), Some(Group::Paren | Group::Bracket)) {
            groups.pop();
        }
    }
    let mut begin = 0;
    let mut depth = 0usize;
    let mut bodies: Vec<Body> = Vec::new();
    let mut groups: Vec<Group> = Vec::new();
    for (i, t) in tokens.iter().enumerate() {
        if line == Some(i) {
            begin = i;
            depth = 0;
            settle(&mut groups);
        }
        match t.kind {
            TokenKind::LParen => groups.push(Group::Paren),
            TokenKind::RParen => {
                if matches!(groups.last(), Some(Group::Paren)) {
                    groups.pop();
                }
            }
            TokenKind::LBracket => {
                groups.push(Group::Bracket);
                depth += 1;
            }
            TokenKind::RBracket => {
                if matches!(groups.last(), Some(Group::Bracket)) {
                    groups.pop();
                }
                depth = depth.saturating_sub(1);
            }
            TokenKind::LBrace => {
                bodies.push(Body::opened_by(prefix, &significant(&tokens[begin..i])));
                let around = matches!(groups.last(), Some(Group::Paren | Group::Bracket))
                    .then_some((begin, depth));
                groups.push(Group::Brace(around));
                begin = i + 1;
                depth = 0;
            }
            TokenKind::RBrace => {
                bodies.pop();
                settle(&mut groups);
                if let Some(Group::Brace(Some((outer, open)))) = groups.pop() {
                    begin = outer;
                    depth = open;
                } else {
                    begin = i + 1;
                    depth = 0;
                }
            }
            TokenKind::Semi => {
                settle(&mut groups);
                begin = i + 1;
                depth = 0;
            }
            TokenKind::RegularComment => {
                begin = i + 1;
                depth = 0;
            }
            _ => {}
        }
    }
    (begin, depth, bodies)
}

/// The toolkit's tokens of `prefix`, the text ahead of the cursor. A
/// quote left open on an earlier line — of a quoted name, or of a
/// string, which then runs to the end — runs into the cursor's line,
/// swallowing it, or pairing with the first quote on it and flipping
/// every pairing after that: the line is then read on its own, as an
/// editor shows it, and the statement starts no earlier than the line;
/// its first token's index comes along.
pub(crate) fn tokens_ahead(prefix: &str) -> (Vec<Token>, Option<usize>) {
    #[cfg(test)]
    PREFIX_LEXES.with(|n| n.set(n.get() + 1));
    let mut tokens = sysmlv2_parser::lexer::tokenize(prefix).0;
    let line_start = prefix.rfind('\n').map_or(0, |i| i + 1);
    let runs_in = tokens.iter().position(|t| {
        let from = &prefix[t.span.start as usize..];
        (t.span.start as usize) < line_start
            && line_start < t.span.end as usize
            && (from.starts_with('\'') || (t.kind == TokenKind::Error && from.starts_with('"')))
    });
    let Some(at) = runs_in else {
        return (tokens, None);
    };
    tokens.truncate(at);
    let base = crate::position::offset32(line_start);
    tokens.extend(
        sysmlv2_parser::lexer::tokenize(&prefix[line_start..])
            .0
            .into_iter()
            .map(|t| Token::new(t.kind, Span::new(t.span.start + base, t.span.end + base))),
    );
    (tokens, Some(at))
}

/// What the word after the statement's `head` fills, in a member of
/// `body`; `bracket`: the statement leaves a `[` open.
fn slot(src: &str, head: &[Token], body: Body, bracket: bool, dialect: Dialect) -> Slot {
    if let Some(keywords) = declared(src, head, body, dialect) {
        return Slot::Declared(keywords);
    }
    // Inside a bracket the statement leaves open, a unit is written
    // (`9.8 [m/s`, a name typed word by word: `[metre per`), or a
    // multiplicity: no position class describes it.
    if bracket {
        return Slot::Open;
    }
    match position(src, head, body, dialect) {
        Some(mut want) => {
            want.keywords.retain(|&(k, _)| is_reserved(dialect, k));
            let mut seen = std::collections::HashSet::new();
            want.keywords.retain(|&(k, _)| seen.insert(k));
            Slot::Want(want)
        }
        None => Slot::Open,
    }
}

/// The tokens that are not trivia (whitespace and notes), the end
/// marker dropped.
fn significant(tokens: &[Token]) -> Vec<Token> {
    tokens
        .iter()
        .filter(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof)
        .copied()
        .collect()
}

/// Is the cursor in prose: a comment, a note, a documentation body, or
/// a string literal? The text ahead of the cursor ends inside one when
/// its `last` token is a line note (which runs to the end of its line)
/// or an unterminated comment, note, or string.
fn in_prose(prefix: &str, last: Token) -> bool {
    match last.kind {
        TokenKind::LineNote => true,
        TokenKind::Error => {
            let text = last.text(prefix);
            text.starts_with("/*") || text.starts_with("//*") || text.starts_with('"')
        }
        _ => false,
    }
}

/// Is the word being completed part of a number or a range bound? A
/// name never starts with a digit, so a word that does is a number
/// (`12`, `1.5e`); with no word typed yet, the cursor may follow a
/// number's decimal point (`5.`) or stand where one begins (`= .`), a
/// range's `..` (`[0..`), the infinity literal (`[1..*`), or an
/// exponent's sign (`1.5e-`).
fn in_number(prefix: &str, tokens: &[Token], word_start: usize) -> bool {
    if let Some(c) = prefix[word_start..].chars().next() {
        return c.is_ascii_digit();
    }
    let mut ahead = tokens
        .iter()
        .rev()
        .filter(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof);
    let Some(last) = ahead.next() else {
        return false;
    };
    let before = ahead.next();
    match last.kind {
        TokenKind::DotDot => true,
        TokenKind::Dot => before.is_none_or(|b| {
            matches!(b.kind, TokenKind::Decimal | TokenKind::Exp) || !ends_operand(b.kind)
        }),
        TokenKind::Star => before.is_none_or(|b| !ends_operand(b.kind)),
        TokenKind::Plus | TokenKind::Minus => {
            let letter = before.filter(|e| {
                e.kind == TokenKind::Ident
                    && e.span.end == last.span.start
                    && matches!(e.text(prefix), "e" | "E")
            });
            letter.zip(ahead.next()).is_some_and(|(e, mantissa)| {
                mantissa.kind == TokenKind::Decimal && mantissa.span.end == e.span.start
            })
        }
        _ => false,
    }
}

/// Can a token of this kind end an operand, so that an operator may
/// follow it (`a *` is a product, `[*` the infinity literal)?
fn ends_operand(kind: TokenKind) -> bool {
    matches!(
        kind,
        TokenKind::Ident
            | TokenKind::UnrestrictedName
            | TokenKind::String
            | TokenKind::Decimal
            | TokenKind::Exp
            | TokenKind::RParen
            | TokenKind::RBracket
            | TokenKind::RBrace
    )
}

impl Body {
    /// The body a `{` opens, from the significant tokens of the
    /// statement it ends (visibility and prefix metadata first, then
    /// the declaration's head).
    fn opened_by(src: &str, header: &[Token]) -> Body {
        let rest = &header[past_prefixes(src, header)..];
        // An expression's body: `->collect { … }`.
        if let [.., arrow, name] = rest {
            if arrow.kind == TokenKind::Arrow && name.kind == TokenKind::Ident {
                return Body::Calculation { case: false };
            }
        }
        if rest.first().is_some_and(|t| t.kind == TokenKind::At) {
            return Body::Metadata;
        }
        let words: Vec<&str> = rest
            .iter()
            .filter(|t| t.kind == TokenKind::Ident)
            .map(|t| t.text(src))
            .collect();
        if let Some(at) = words.iter().position(|w| *w == "def") {
            return match at.checked_sub(1).map(|i| words[i]) {
                Some("action") => Body::Action,
                Some("state") => Body::State,
                Some("calc" | "constraint") => Body::Calculation { case: false },
                Some("case" | "analysis" | "verification") => Body::Calculation { case: true },
                Some("requirement" | "concern" | "viewpoint") => Body::Requirement,
                Some("view") => Body::View,
                Some("enum") => Body::Enumeration,
                _ => Body::Definition,
            };
        }
        for w in words {
            return match w {
                // Prefixes: the kind is still to come.
                "abstract" | "composite" | "const" | "constant" | "derived" | "end" | "in"
                | "individual" | "inout" | "out" | "portion" | "snapshot" | "then"
                | "timeslice" | "use" | "var" | "variation" => continue,
                "accept" | "action" | "assign" | "decide" | "do" | "else" | "entry" | "exit"
                | "for" | "fork" | "if" | "join" | "loop" | "merge" | "perform" | "send"
                | "terminate" | "transition" | "while" => Body::Action,
                "exhibit" | "state" => Body::State,
                "assert" | "assume" | "calc" | "constraint" | "require" => {
                    Body::Calculation { case: false }
                }
                "analysis" | "case" | "include" | "verification" => {
                    Body::Calculation { case: true }
                }
                "concern" | "frame" | "objective" | "requirement" | "satisfy" | "verify"
                | "viewpoint" => Body::Requirement,
                "view" => Body::View,
                "metadata" => Body::Metadata,
                "library" | "namespace" | "package" | "standard" => Body::Namespace,
                "assoc" | "behavior" | "class" | "classifier" | "connector" | "datatype"
                | "feature" | "interaction" | "metaclass" | "multiplicity" | "step" | "struct"
                | "type" => Body::Type,
                "bool" | "expr" | "function" | "inv" | "predicate" => Body::Function,
                "alias" | "dependency" | "expose" | "filter" | "import" => Body::Other,
                // Any other usage keyword, or the name of a usage declared
                // without one.
                _ => Body::Definition,
            };
        }
        Body::Other
    }

    /// Does a statement at this body's top level read as its result
    /// expression when it does not start with a declaration keyword?
    fn results(self) -> bool {
        matches!(self, Body::Calculation { .. } | Body::Function)
    }
}

/// How many leading tokens of a statement are its visibility and its
/// prefix metadata annotations (`private #Safety #Security::Level`).
fn past_prefixes(src: &str, stmt: &[Token]) -> usize {
    let mut i = 0;
    while let Some(t) = stmt.get(i) {
        let named = stmt
            .get(i + 1)
            .is_some_and(|n| matches!(n.kind, TokenKind::Ident | TokenKind::UnrestrictedName));
        if t.kind == TokenKind::Hash && named {
            i = past_annotation(stmt, i);
        } else if t.kind == TokenKind::Ident && is_visibility(t.text(src)) {
            i += 1;
        } else {
            break;
        }
    }
    i
}

/// The index past the prefix metadata annotation at `stmt[at]` (its
/// `#`), which names a metadata definition by qualified name.
fn past_annotation(stmt: &[Token], at: usize) -> usize {
    let mut i = at + 1;
    while stmt
        .get(i)
        .is_some_and(|t| matches!(t.kind, TokenKind::Ident | TokenKind::UnrestrictedName))
    {
        i += 1;
        if stmt.get(i).is_some_and(|t| t.kind == TokenKind::ColonColon) {
            i += 1;
        } else {
            break;
        }
    }
    i
}

/// May every token of `ahead` prefix a definition? Then a `def` may
/// follow the kind keyword after it (`abstract #Safety part def`, not
/// `ref part def`).
fn definition_prefix(src: &str, ahead: &[Token]) -> bool {
    let mut i = 0;
    while let Some(t) = ahead.get(i) {
        if t.kind == TokenKind::Hash {
            i = past_annotation(ahead, i);
        } else if t.kind == TokenKind::Ident && DEFINITION_PREFIXES.contains(&t.text(src)) {
            i += 1;
        } else {
            return false;
        }
    }
    true
}

fn is_visibility(word: &str) -> bool {
    matches!(word, "public" | "private" | "protected")
}

/// A keyword after which the next word is a name the statement
/// declares.
struct Declarer {
    keyword: &'static str,
    /// The keywords that may take the name's place and continue the
    /// declaration's head: `part` → `def`, `in` → `item`, `comment` →
    /// `about`. A `def` among them is offered only where every word
    /// ahead of the keyword may prefix a definition.
    instead: &'static [&'static [&'static str]],
}

const fn declarer(keyword: &'static str, instead: &'static [&'static [&'static str]]) -> Declarer {
    Declarer { keyword, instead }
}

const NOTHING: &[&[&str]] = &[];
/// A usage's kind keyword: `def` makes it a definition's; a usage with no
/// name of its own often redefines one right away (`part redefines
/// engine`) — the one keyword after a name the table offers.
const DEF: &[&[&str]] = &[&["def", "redefines"]];

/// The SysML keywords naming a usage's kind, which may follow its prefix
/// keywords (`in item`, `ref part`, `abstract action`, `variation
/// perform`), and `redefines` for a usage redefining without a kind
/// (`ref redefines engine`).
const USAGE_KINDS: &[&str] = &[
    "action",
    "allocation",
    "analysis",
    "assert",
    "attribute",
    "binding",
    "calc",
    "case",
    "concern",
    "connection",
    "constraint",
    "enum",
    "event",
    "exhibit",
    "flow",
    "include",
    "interface",
    "item",
    "message",
    "occurrence",
    "part",
    "perform",
    "port",
    "redefines",
    "rendering",
    "requirement",
    "satisfy",
    "state",
    "succession",
    "use",
    "verification",
    "view",
    "viewpoint",
];

/// SysML: every keyword after which the next word is a name being
/// declared. Sorted by keyword.
const SYSML: &[Declarer] = &[
    declarer(
        "abstract",
        &[
            &[
                "constant",
                "individual",
                "metadata",
                "ref",
                "snapshot",
                "timeslice",
            ],
            USAGE_KINDS,
        ],
    ),
    declarer("action", DEF),
    declarer("actor", NOTHING),
    declarer("alias", NOTHING),
    declarer("allocation", &[&["allocate", "def", "redefines"]]),
    declarer("analysis", DEF),
    declarer("attribute", DEF),
    declarer("binding", &[&["bind"]]),
    declarer("calc", DEF),
    declarer("case", DEF),
    declarer("comment", &[&["about", "locale"]]),
    declarer("concern", DEF),
    declarer("connection", &[&["connect", "def", "redefines"]]),
    declarer(
        "constant",
        &[&["individual", "ref", "snapshot", "timeslice"], USAGE_KINDS],
    ),
    declarer("constraint", DEF),
    declarer("decide", NOTHING),
    declarer("def", NOTHING),
    declarer(
        "derived",
        &[
            &[
                "abstract",
                "constant",
                "individual",
                "ref",
                "snapshot",
                "timeslice",
                "variation",
            ],
            USAGE_KINDS,
        ],
    ),
    declarer("doc", &[&["locale"]]),
    declarer(
        "end",
        &[
            &[
                "abstract",
                "constant",
                "derived",
                "in",
                "inout",
                "out",
                "ref",
                "variation",
            ],
            USAGE_KINDS,
        ],
    ),
    declarer("enum", DEF),
    declarer("for", NOTHING),
    declarer("fork", NOTHING),
    declarer("in", DIRECTED),
    declarer(
        "individual",
        &[&["def", "snapshot", "timeslice"], USAGE_KINDS],
    ),
    declarer("inout", DIRECTED),
    declarer("item", DEF),
    declarer("join", NOTHING),
    declarer("merge", NOTHING),
    declarer("objective", NOTHING),
    declarer("occurrence", DEF),
    declarer("out", DIRECTED),
    declarer("package", NOTHING),
    declarer("part", DEF),
    declarer("port", DEF),
    declarer(
        "ref",
        &[&["individual", "snapshot", "timeslice"], USAGE_KINDS],
    ),
    declarer("rendering", DEF),
    declarer("rep", &[&["language"]]),
    declarer("requirement", DEF),
    declarer(
        "return",
        &[
            &[
                "abstract",
                "constant",
                "derived",
                "end",
                "in",
                "individual",
                "inout",
                "out",
                "ref",
                "snapshot",
                "timeslice",
                "variation",
            ],
            USAGE_KINDS,
        ],
    ),
    declarer("snapshot", &[USAGE_KINDS]),
    declarer("stakeholder", NOTHING),
    declarer("state", &[&["def", "parallel", "redefines"]]),
    declarer("subject", NOTHING),
    declarer("succession", &[&["first", "flow"]]),
    declarer("timeslice", &[USAGE_KINDS]),
    declarer(
        "variation",
        &[
            &["constant", "individual", "ref", "snapshot", "timeslice"],
            USAGE_KINDS,
        ],
    ),
    declarer("verification", DEF),
    declarer("view", DEF),
    declarer("viewpoint", DEF),
];

/// What may follow a SysML direction (`in`, `out`, `inout`): the rest
/// of the usage prefix, or the usage's kind.
const DIRECTED: &[&[&str]] = &[
    &[
        "abstract",
        "constant",
        "derived",
        "individual",
        "ref",
        "snapshot",
        "timeslice",
        "variation",
    ],
    USAGE_KINDS,
];

/// The words that may prefix a SysML definition besides its prefix
/// metadata: its visibility, `abstract` or `variation`, `individual`,
/// and `use` (of `use case`).
const DEFINITION_PREFIXES: &[&str] = &[
    "abstract",
    "individual",
    "private",
    "protected",
    "public",
    "use",
    "variation",
];

/// The keywords that may start a member of an enumeration body other
/// than a bare literal.
const ENUMERATION_MEMBERS: &[&str] = &[
    "comment",
    "doc",
    "enum",
    "language",
    "locale",
    "metadata",
    "private",
    "protected",
    "public",
    "rep",
];

/// The KerML keywords naming a feature's kind, which may follow its
/// prefix keywords, and `redefines` for a feature redefining without a
/// kind (`in redefines x`).
const FEATURE_KINDS: &[&str] = &[
    "binding",
    "bool",
    "connector",
    "expr",
    "feature",
    "flow",
    "inv",
    "redefines",
    "step",
    "succession",
];

/// The KerML keywords naming a type's kind.
const TYPE_KINDS: &[&str] = &[
    "assoc",
    "behavior",
    "class",
    "classifier",
    "datatype",
    "function",
    "interaction",
    "metaclass",
    "predicate",
    "struct",
    "type",
];

/// What may follow a KerML direction: the rest of the feature prefix,
/// or the feature's kind.
const DIRECTED_FEATURE: &[&[&str]] = &[
    &[
        "abstract",
        "composite",
        "const",
        "derived",
        "portion",
        "var",
    ],
    FEATURE_KINDS,
];

/// What may follow KerML `member` and `return`: a feature's whole
/// prefix, or its kind.
const FEATURE_PREFIXED: &[&[&str]] = &[
    &[
        "abstract",
        "composite",
        "const",
        "derived",
        "end",
        "in",
        "inout",
        "out",
        "portion",
        "var",
    ],
    FEATURE_KINDS,
];

/// `all` (a sufficient type) may stand where a KerML type's name would.
const ALL: &[&[&str]] = &[&["all"]];

/// `all` may stand where a KerML feature's name would, and a feature
/// with no name of its own often redefines one (`feature redefines x`).
const FEATURE_HEAD: &[&[&str]] = &[&["all", "redefines"]];

/// KerML: every keyword after which the next word is a name being
/// declared. Sorted by keyword.
const KERML: &[Declarer] = &[
    declarer(
        "abstract",
        &[
            &["composite", "const", "portion", "var"],
            FEATURE_KINDS,
            TYPE_KINDS,
        ],
    ),
    declarer("alias", NOTHING),
    declarer("assoc", &[&["all", "struct"]]),
    declarer("behavior", ALL),
    declarer("bool", FEATURE_HEAD),
    declarer("class", ALL),
    declarer("classifier", ALL),
    declarer("comment", &[&["about", "locale"]]),
    declarer("composite", &[&["const", "var"], FEATURE_KINDS]),
    declarer("conjugation", &[&["conjugate"]]),
    declarer("const", &[&["end"], FEATURE_KINDS]),
    declarer("datatype", ALL),
    declarer(
        "derived",
        &[
            &["abstract", "composite", "const", "portion", "var"],
            FEATURE_KINDS,
        ],
    ),
    declarer("disjoining", &[&["disjoint"]]),
    declarer("doc", &[&["locale"]]),
    declarer(
        "end",
        &[
            &[
                "abstract",
                "composite",
                "const",
                "derived",
                "in",
                "inout",
                "out",
                "portion",
                "var",
            ],
            FEATURE_KINDS,
        ],
    ),
    declarer("expr", FEATURE_HEAD),
    declarer("feature", FEATURE_HEAD),
    declarer("function", ALL),
    declarer("in", DIRECTED_FEATURE),
    declarer("inout", DIRECTED_FEATURE),
    declarer("interaction", ALL),
    declarer("inv", &[&["false", "true"]]),
    declarer("inverting", &[&["inverse"]]),
    declarer("member", FEATURE_PREFIXED),
    declarer("metaclass", ALL),
    declarer("multiplicity", NOTHING),
    declarer("namespace", NOTHING),
    declarer("out", DIRECTED_FEATURE),
    declarer("package", NOTHING),
    declarer("portion", &[&["const", "var"], FEATURE_KINDS]),
    declarer("predicate", ALL),
    declarer("rep", &[&["language"]]),
    declarer("return", FEATURE_PREFIXED),
    declarer(
        "specialization",
        &[&[
            "redefinition",
            "subclassifier",
            "subset",
            "subtype",
            "typing",
        ]],
    ),
    declarer("step", FEATURE_HEAD),
    declarer("struct", ALL),
    declarer("type", ALL),
    declarer("var", &[FEATURE_KINDS]),
];

fn table(dialect: Dialect) -> &'static [Declarer] {
    match dialect {
        Dialect::Sysml => SYSML,
        Dialect::Kerml => KERML,
    }
}

/// The keywords that may stand where the word being completed is, when
/// that word is a name the statement declares; `None` when it is not.
fn declared(src: &str, head: &[Token], body: Body, dialect: Dialect) -> Option<Vec<&'static str>> {
    let keyword = |t: &Token| {
        (t.kind == TokenKind::Ident && is_reserved(dialect, t.text(src))).then(|| t.text(src))
    };
    // A bare member of an enumeration body declares a literal.
    let literal = |ahead: &[Token]| {
        dialect == Dialect::Sysml
            && body == Body::Enumeration
            && ahead.iter().all(|t| keyword(t).is_some_and(is_visibility))
    };
    // The declarer the keyword at `head[at]` is, read in its statement.
    let declarer_at = |at: usize| -> Option<&'static Declarer> {
        let word = keyword(&head[at])?;
        let d = table(dialect)
            .binary_search_by(|d| d.keyword.cmp(word))
            .ok()
            .map(|i| &table(dialect)[i])?;
        let ahead = || head[..at].iter().filter_map(keyword);
        let applies = match (dialect, word) {
            // `alias A for B`: the aliased element.
            (Dialect::Sysml, "for") => !ahead().any(|w| w == "alias"),
            // `for i in items`: the collection iterated.
            (Dialect::Sysml, "in") => !ahead().any(|w| w == "for"),
            // A metadata body's members redefine features they name.
            (Dialect::Sysml, "ref") | (Dialect::Kerml, "feature") => body != Body::Metadata,
            _ => true,
        };
        applies.then_some(d)
    };
    if literal(head) {
        let visible = !head.is_empty();
        return Some(
            ENUMERATION_MEMBERS
                .iter()
                .copied()
                .filter(|w| !(visible && is_visibility(w)))
                .collect(),
        );
    }
    let (last, ahead) = head.split_last()?;
    match last.kind {
        TokenKind::Ident => {
            // A KerML type's or feature's sufficiency (`class all C`)
            // and an invariant's polarity (`inv true c`) come between
            // its keyword and its name: the name still follows.
            let n = head.len();
            let at = match keyword(last) {
                Some(w @ ("all" | "true" | "false"))
                    if n >= 2
                        && declarer_at(n - 2)
                            .is_some_and(|d| d.instead.iter().any(|g| g.contains(&w))) =>
                {
                    n - 2
                }
                _ => n - 1,
            };
            let d = declarer_at(at)?;
            let definable = body != Body::Enumeration && definition_prefix(src, &head[..at]);
            let skipped = at < n - 1;
            let mut words: Vec<&'static str> = Vec::new();
            for &w in d.instead.iter().flat_map(|group| group.iter()) {
                let spent = skipped && matches!(w, "all" | "true" | "false");
                if (w != "def" || definable) && !spent && !words.contains(&w) {
                    words.push(w);
                }
            }
            Some(words)
        }
        // A short name: `part def <V`.
        TokenKind::Lt => {
            let declares = match ahead.len() {
                0 => false,
                n => declarer_at(n - 1).is_some(),
            };
            (declares || literal(ahead)).then(Vec::new)
        }
        // The name after a short name: `part def <V> Vehicle`.
        TokenKind::Gt => {
            let n = head.len();
            let shaped = n >= 3
                && matches!(
                    head[n - 2].kind,
                    TokenKind::Ident | TokenKind::UnrestrictedName
                )
                && head[n - 3].kind == TokenKind::Lt;
            if !shaped {
                return None;
            }
            let declares = n >= 4 && declarer_at(n - 4).is_some();
            (declares || literal(&head[..n - 3])).then(Vec::new)
        }
        _ => None,
    }
}

/// What completion offers at a position the statement tells apart.
#[derive(Debug, PartialEq, Eq)]
pub(crate) struct Want {
    /// The keywords offered, each with its sort key (see [`sort_text`]).
    pub keywords: Vec<(&'static str, u8)>,
    /// Which names are offered, and how they rank; `None` offers none.
    pub names: Option<Names>,
}

/// Which of its enclosing element's features a position names — the
/// names in scope there that the symbol tables do not hold: members
/// inherited from a specialization or typing, or from the library base
/// every element of its kind implicitly specializes (`Actions::Action`'s
/// `start` and `done` in an action).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Members {
    /// None beyond the symbol tables.
    None,
    /// The features it inherits: what a redefinition names.
    Inherited,
    /// Its own features and those it inherits: what a succession or a
    /// subsetting names.
    Scope,
}

/// Which names a position takes, and in which groups: a lower group
/// ranks first. A name's sort key is its group's tens plus its source
/// — `0` a workspace name, `1` one that needs an import, `2` a library
/// name, `3` one that needs an import — plus `4` for a name of a kind
/// specializing the one a feature position's statement declares (see
/// [`Want::tier`]). A name whose declaration's kind is unknown (see
/// [`Decl::Other`]: an alias whose target another unit declares may
/// name anything) ranks with the namespaces wherever names are taken.
#[derive(Debug, PartialEq, Eq)]
pub(crate) enum Names {
    /// Every name: a position the statement does not tell apart, or one
    /// that takes any element (`expose`, `about`, `alias … for`).
    All,
    /// Types: definitions of the `exact` kinds, then of the
    /// `compatible` ones and of user-defined kinds (`#Service def`),
    /// which may be of any kind, then namespaces, which qualify a
    /// type's name.
    Types {
        exact: Vec<DefKind>,
        compatible: Vec<DefKind>,
        /// Usages too, ranked with the namespaces: a KerML type
        /// operator's operand (`classifier C unions …`) may be a feature,
        /// which is a type as well.
        features: bool,
    },
    /// Features: usages of the `preferred` kinds (of any kind when
    /// empty), those of the statement's own kind ahead of the `specific`
    /// ones, then other usages, then definitions of the `definitions`
    /// kinds, then namespaces and the workspace's other definitions,
    /// which qualify the features they own (`redefines Vehicle::mass`).
    /// A `strict` position takes no usage whose kind keyword names
    /// another kind (`satisfy` takes no attribute), and ranks the
    /// definitions ahead of the usages declared without one.
    Features {
        preferred: Vec<UsageKind>,
        definitions: Vec<DefKind>,
        strict: bool,
        /// Which features of the element the statement is a member of
        /// the position names too, ahead of every other name.
        members: Members,
        /// Of `preferred`, the kinds specializing the kind the statement
        /// declares (parts at an item's redefinition): their names rank
        /// after those of its own kind (see [`Want::tier`]).
        specific: Vec<UsageKind>,
    },
    /// Expression operands: features and the definitions an expression
    /// invokes, then enumerations and namespaces, which qualify a
    /// literal's or a feature's name, then the workspace's other
    /// definitions, which qualify the features they own
    /// (`WheelAssy::wheel`); measurement units last, or first where the
    /// statement's type is a unit type (see [`Want::unit_group`]).
    Operands {
        /// The type the statement declares, last segment only
        /// (`attribute b : Boolean = …`).
        typed: Option<String>,
    },
}

impl Names {
    /// The group of a candidate declared as `decl`, `workspace` when the
    /// workspace declares it; `None` when the position does not take it.
    /// Only the workspace's definitions qualify features: the library's
    /// would double the lists.
    pub(crate) fn group(&self, decl: Decl, workspace: bool) -> Option<u8> {
        match self {
            Names::All => Some(1),
            Names::Types {
                exact,
                compatible,
                features,
            } => match decl {
                Decl::Definition(k) if exact.contains(&k) => Some(1),
                Decl::Definition(k) if compatible.contains(&k) || k == DefKind::Extended => Some(2),
                Decl::Namespace | Decl::Other => Some(3),
                Decl::Usage(_) if *features => Some(3),
                _ => None,
            },
            Names::Features {
                preferred,
                definitions,
                strict,
                ..
            } => match decl {
                Decl::Usage(u) if preferred.is_empty() || preferred.contains(&u) => Some(1),
                Decl::Definition(k) if definitions.contains(&k) => {
                    Some(if *strict { 2 } else { 3 })
                }
                // Declared without a kind keyword: it may be of any kind.
                Decl::Usage(UsageKind::Default | UsageKind::Ref | UsageKind::Feature) => {
                    Some(if *strict { 3 } else { 2 })
                }
                Decl::Usage(_) if !strict => Some(2),
                Decl::Namespace | Decl::Other => Some(4),
                Decl::Definition(_) if workspace => Some(4),
                Decl::Usage(_) | Decl::Definition(_) => None,
            },
            Names::Operands { .. } => match decl {
                Decl::Usage(_) => Some(1),
                Decl::Definition(k) if CALLABLES.contains(&k) => Some(1),
                Decl::Definition(DefKind::Enum) | Decl::Namespace | Decl::Other => Some(3),
                Decl::Definition(_) if workspace => Some(4),
                Decl::Definition(_) => None,
            },
        }
    }
}

impl Want {
    /// `self`, naming the enclosing element's `members` too.
    fn with(mut self, members: Members) -> Want {
        if let Some(Names::Features { members: m, .. }) = &mut self.names {
            *m = members;
        }
        self
    }

    /// Which of the enclosing element's features the position names
    /// ahead of every other name.
    pub(crate) fn members(&self) -> Members {
        match &self.names {
            Some(Names::Features { members, .. }) => *members,
            _ => Members::None,
        }
    }

    /// What a position the statement does not tell apart takes: every
    /// keyword of `dialect`, ranked with the workspace's names, and
    /// every name.
    pub(crate) fn open(dialect: Dialect) -> Want {
        Want {
            keywords: crate::tokens::keywords(dialect)
                .map(|k| (k, WITH_WORKSPACE))
                .collect(),
            names: Some(Names::All),
        }
    }

    /// The group of a name declared as `decl`, `workspace` when the
    /// workspace declares it (see [`Names::group`]); `None` when the
    /// position takes no such name.
    pub(crate) fn group(&self, decl: Decl, workspace: bool) -> Option<u8> {
        self.names.as_ref()?.group(decl, workspace)
    }

    /// The tier within its group of a name declared as `decl`: `1` for
    /// a usage of a kind specializing the one the statement declares
    /// (a part at an item's redefinition), whose names rank after those
    /// of the statement's own kind; `0` otherwise.
    pub(crate) fn tier(&self, decl: Decl) -> u8 {
        match (&self.names, decl) {
            (Some(Names::Features { specific, .. }), Decl::Usage(u)) => {
                u8::from(specific.contains(&u))
            }
            _ => 0,
        }
    }

    /// The group a measurement unit takes at an expression operand,
    /// `unit_types` naming the unit types: first where the statement's
    /// type is one (`attribute <N> newton : ForceUnit = kg*m/s^2`), after
    /// every other name otherwise — units write quantities' values and
    /// other units, rarely anything else. `None` at other positions.
    pub(crate) fn unit_group(&self, unit_types: &HashSet<String>) -> Option<u8> {
        match &self.names {
            Some(Names::Operands { typed }) => {
                Some(if typed.as_ref().is_some_and(|t| unit_types.contains(t)) {
                    0
                } else {
                    UNITS
                })
            }
            _ => None,
        }
    }

    fn new(keywords: &[&'static str], key: u8, names: Option<Names>) -> Want {
        Want {
            keywords: keywords.iter().map(|&k| (k, key)).collect(),
            names,
        }
    }
}

/// Keywords ranked ahead of every name.
const FIRST: u8 = 0;
/// Keywords ranked among the best-fitting workspace names, ahead of the
/// library's.
const WITH_WORKSPACE: u8 = 10;
/// Keywords ranked after the best-fitting names.
const AFTER: u8 = 14;
/// The group measurement units take after every other operand.
const UNITS: u8 = 5;

/// The `sortText` of a candidate labeled `label` with sort key `key`:
/// keys sort as numbers, equal keys by the label's length — the word
/// typed is more of a short name (`Mas` of `MassValue` than of
/// `MassAttenuationCoefficientValue`) — and equal lengths by label.
pub(crate) fn sort_text(key: u8, label: &str) -> String {
    format!("{key:02}{:03}", label.chars().count().min(999))
}

/// The sort key of a name in `group` from `source` (see [`Names`]),
/// of `tier` within its group (see [`Want::tier`]): a more specific
/// kind's names after those of the statement's own kind from every
/// source.
pub(crate) fn name_key(group: u8, source: u8, tier: u8) -> u8 {
    group * 10 + 4 * tier + source
}

fn types(exact: &[DefKind], compatible: &[DefKind]) -> Want {
    Want {
        keywords: Vec::new(),
        names: Some(Names::Types {
            exact: exact.to_vec(),
            compatible: compatible.to_vec(),
            features: false,
        }),
    }
}

/// After a KerML type operator (`unions`, `intersects`, `differences`,
/// `disjoint from`): types, features among them — a feature's operands
/// are features first, a type's types.
fn type_operands(src: &str, stmt: &[Token], dialect: Dialect) -> Want {
    if definition_kind(src, stmt, dialect).is_none() {
        return features(&[], ALL_DEFINITIONS);
    }
    types_then_features()
}

/// Types, then features, which are types too.
fn types_then_features() -> Want {
    Want {
        keywords: Vec::new(),
        names: Some(Names::Types {
            exact: ALL_DEFINITIONS.to_vec(),
            compatible: Vec::new(),
            features: true,
        }),
    }
}

/// Features, those of the `preferred` kinds first.
fn features(preferred: &[UsageKind], definitions: &[DefKind]) -> Want {
    Want {
        keywords: Vec::new(),
        names: Some(Names::Features {
            preferred: preferred.to_vec(),
            definitions: definitions.to_vec(),
            strict: false,
            members: Members::None,
            specific: Vec::new(),
        }),
    }
}

/// Features of the `preferred` kinds only (see [`Names::Features`]).
fn strictly(preferred: &[UsageKind], definitions: &[DefKind]) -> Want {
    Want {
        keywords: Vec::new(),
        names: Some(Names::Features {
            preferred: preferred.to_vec(),
            definitions: definitions.to_vec(),
            strict: true,
            members: Members::None,
            specific: Vec::new(),
        }),
    }
}

/// A reference of a kind, or one of `keywords` declaring one in its
/// place (`perform takePicture`, `perform action a`).
fn reference(preferred: &[UsageKind], definitions: &[DefKind], keywords: &[&'static str]) -> Want {
    Want {
        keywords: keywords.iter().map(|&k| (k, FIRST)).collect(),
        ..strictly(preferred, definitions)
    }
}

fn metadata_types() -> Want {
    types(&[DefKind::Metadata, DefKind::Metaclass], &[])
}

/// Literal and prefix keywords that may start an expression.
const EXPRESSION_START: &[&str] = &["all", "false", "if", "new", "not", "null", "true"];

/// The keywords that may follow an expression's operand.
const INFIX: &[&str] = &[
    "and", "as", "else", "hastype", "implies", "istype", "meta", "or", "xor",
];

/// The usages a succession steps between first: actions, states, and
/// other occurrences, and KerML's steps, expressions, and invariants.
const BEHAVIORS: &[UsageKind] = &[
    UsageKind::Action,
    UsageKind::Perform,
    UsageKind::State,
    UsageKind::Exhibit,
    UsageKind::Accept,
    UsageKind::Send,
    UsageKind::Assign,
    UsageKind::IfNode,
    UsageKind::WhileLoop,
    UsageKind::ForLoop,
    UsageKind::Terminate,
    UsageKind::Merge,
    UsageKind::Decide,
    UsageKind::Join,
    UsageKind::Fork,
    UsageKind::Calc,
    UsageKind::Case,
    UsageKind::Analysis,
    UsageKind::Verification,
    UsageKind::UseCase,
    UsageKind::Include,
    UsageKind::Occurrence,
    UsageKind::Event,
    UsageKind::Step,
    UsageKind::Expr,
    UsageKind::BoolExpr,
    UsageKind::Invariant,
];

/// The usages a `perform` names: actions of every kind.
const PERFORMED: &[UsageKind] = &[
    UsageKind::Action,
    UsageKind::Perform,
    UsageKind::State,
    UsageKind::Exhibit,
    UsageKind::Accept,
    UsageKind::Send,
    UsageKind::Assign,
    UsageKind::IfNode,
    UsageKind::WhileLoop,
    UsageKind::ForLoop,
    UsageKind::Terminate,
    UsageKind::Merge,
    UsageKind::Decide,
    UsageKind::Join,
    UsageKind::Fork,
    UsageKind::Calc,
    UsageKind::Case,
    UsageKind::Analysis,
    UsageKind::Verification,
    UsageKind::UseCase,
    UsageKind::Include,
];

/// The action usages a state's entry, do, and exit actions perform.
const ACTIONS: &[UsageKind] = &[
    UsageKind::Action,
    UsageKind::Perform,
    UsageKind::Accept,
    UsageKind::Send,
    UsageKind::Assign,
    UsageKind::Calc,
];

/// The keywords that declare the successor after `then` in an action
/// body instead of naming it.
const SUCCESSORS: &[&str] = &[
    "accept",
    "action",
    "assign",
    "decide",
    "for",
    "fork",
    "if",
    "join",
    "loop",
    "merge",
    "send",
    "state",
    "terminate",
    "while",
];

/// The position the word being completed fills, as far as the
/// statement's tokens tell; `None` when they do not.
fn position(src: &str, head: &[Token], body: Body, dialect: Dialect) -> Option<Want> {
    let start = past_prefixes(src, head);
    let stmt = &head[start..];
    let Some((&last, ahead)) = stmt.split_last() else {
        return statement_start(body, dialect, start > 0);
    };
    let word = |t: &Token| (t.kind == TokenKind::Ident).then(|| t.text(src));
    let keyword = |t: &Token| word(t).filter(|w| is_reserved(dialect, w));
    let before = ahead.last();
    let has = |w: &str| stmt.iter().any(|t| keyword(t) == Some(w));
    match last.kind {
        TokenKind::Hash => Some(metadata_types()),
        TokenKind::At if ahead.is_empty() => Some(metadata_types()),
        TokenKind::At | TokenKind::AtAt => Some(types(ALL_DEFINITIONS, &[])),
        TokenKind::Colon => Some(typing(src, stmt, dialect)),
        TokenKind::Tilde
            if before.is_some_and(|b| b.kind == TokenKind::Colon || word(b) == Some("by")) =>
        {
            Some(typing(src, stmt, dialect))
        }
        TokenKind::ColonGt => Some(specializing(src, stmt, dialect)),
        TokenKind::ColonGtGt => Some(of_kind(src, stmt, dialect, Members::Inherited)),
        TokenKind::ColonColonGt | TokenKind::FatArrow => {
            Some(of_kind(src, stmt, dialect, Members::None))
        }
        TokenKind::Eq if has("bind") => Some(features(&[], &[])),
        TokenKind::Eq | TokenKind::ColonEq => Some(expression(src, stmt)),
        TokenKind::Comma => continuing(src, ahead, dialect),
        TokenKind::LParen => Some(opened(src, ahead, dialect)),
        TokenKind::Arrow => Some(types(CALLABLES, &[])),
        TokenKind::Plus
        | TokenKind::Minus
        | TokenKind::Star
        | TokenKind::StarStar
        | TokenKind::Slash
        | TokenKind::Percent
        | TokenKind::Caret
        | TokenKind::EqEq
        | TokenKind::EqEqEq
        | TokenKind::BangEq
        | TokenKind::BangEqEq
        | TokenKind::Lt
        | TokenKind::Gt
        | TokenKind::LtEq
        | TokenKind::GtEq
        | TokenKind::Pipe
        | TokenKind::Amp
        | TokenKind::Question
        | TokenKind::QuestionQuestion
        | TokenKind::DotDot => Some(expression(src, stmt)),
        TokenKind::Ident => match keyword(&last) {
            Some(w) => after_keyword(src, stmt, w, dialect),
            // The function an arrow invokes (`->reduce`): a function
            // reference may follow it (`->reduce max`).
            None if before.is_some_and(|b| b.kind == TokenKind::Arrow) => {
                Some(types(CALLABLES, &[]))
            }
            None => after_operand(src, stmt, body, dialect),
        },
        // A connector end's multiplicity: the end's feature follows.
        TokenKind::RBracket if ends_multiplicity(src, stmt, dialect) => Some(features(&[], &[])),
        TokenKind::Decimal
        | TokenKind::Exp
        | TokenKind::String
        | TokenKind::UnrestrictedName
        | TokenKind::RParen
        | TokenKind::RBracket => after_operand(src, stmt, body, dialect),
        _ => None,
    }
}

/// Does the `]` ending `stmt` close a connector end's multiplicity
/// (`bind [1] a = [1] b`, `connect [1] a to [1] b`): a `[` opening
/// where an end starts, after `=`, `to`, `from`, `bind`, `,`, or `(`?
/// A quantity's unit bracket follows its value instead.
fn ends_multiplicity(src: &str, stmt: &[Token], dialect: Dialect) -> bool {
    let mut depth = 0usize;
    for (i, t) in stmt.iter().enumerate().rev() {
        match t.kind {
            TokenKind::RBracket => depth += 1,
            TokenKind::LBracket => {
                depth = depth.saturating_sub(1);
                if depth == 0 {
                    return i.checked_sub(1).is_some_and(|j| {
                        let b = stmt[j];
                        matches!(b.kind, TokenKind::Eq | TokenKind::Comma | TokenKind::LParen)
                            || (b.kind == TokenKind::Ident
                                && is_reserved(dialect, b.text(src))
                                && matches!(b.text(src), "bind" | "from" | "to"))
                    });
                }
            }
            _ => {}
        }
    }
    false
}

/// What may follow the keyword `word` that ends `stmt`.
fn after_keyword(src: &str, stmt: &[Token], word: &str, dialect: Dialect) -> Option<Want> {
    use DefKind as D;
    use UsageKind as U;
    let words: Vec<&str> = stmt
        .iter()
        .filter(|t| t.kind == TokenKind::Ident)
        .map(|t| t.text(src))
        .filter(|w| is_reserved(dialect, w))
        .collect();
    let before = stmt
        .len()
        .checked_sub(2)
        .map(|i| stmt[i])
        .filter(|t| t.kind == TokenKind::Ident)
        .map(|t| t.text(src));
    let requirements = &[U::Requirement, U::Satisfy, U::Concern, U::Viewpoint];
    // Requirements are constraints too.
    let constraints = &[
        U::Constraint,
        U::AssertConstraint,
        U::Requirement,
        U::Satisfy,
        U::Concern,
        U::Viewpoint,
    ];
    Some(match word {
        "perform" => reference(PERFORMED, &[], &["action"]),
        "exhibit" => reference(&[U::State, U::Exhibit], &[], &["state"]),
        "include" => reference(&[U::UseCase, U::Include], &[], &["use"]),
        "satisfy" | "verify" => reference(
            requirements,
            &[D::Requirement, D::Concern, D::Viewpoint],
            &["requirement"],
        ),
        "frame" => reference(&[U::Concern], &[D::Concern], &["concern"]),
        "assert" => reference(
            constraints,
            &[D::Constraint],
            &["constraint", "not", "satisfy"],
        ),
        "not" if before == Some("assert") => {
            reference(constraints, &[D::Constraint], &["constraint", "satisfy"])
        }
        "require" | "assume" => reference(constraints, &[D::Constraint], &["constraint"]),
        "render" => reference(&[U::Rendering], &[], &["rendering"]),
        "event" => Want {
            keywords: vec![("occurrence", FIRST)],
            ..features(&[U::Occurrence, U::Event], &[])
        },
        "entry" | "do" | "exit" => reference(ACTIONS, &[], &["accept", "action", "assign", "send"]),
        // A successor is named more often than declared. A succession
        // steps between occurrences of any kind — parts, messages, and
        // KerML steps as well as actions and states: behaviors first.
        "then" => Want {
            keywords: SUCCESSORS.iter().map(|&k| (k, AFTER)).collect(),
            ..features(BEHAVIORS, &[]).with(Members::Scope)
        },
        "first" => features(BEHAVIORS, &[]).with(Members::Scope),
        // A transition's source: a state, or the entry action a state
        // machine starts from (`transition initial then off`).
        "transition" => Want {
            keywords: vec![("first", AFTER)],
            ..features(&[U::State, U::Exhibit, U::Perform, U::Action], &[])
        },
        // A payload: a type, or the name of a new parameter.
        "accept" => Want {
            keywords: ["after", "at", "when"].map(|k| (k, AFTER)).to_vec(),
            ..types(ALL_DEFINITIONS, &[])
        },
        "redefines" => of_kind(src, stmt, dialect, Members::Inherited),
        "subsets" => of_kind(src, stmt, dialect, Members::Scope),
        "references" | "crosses" => of_kind(src, stmt, dialect, Members::None),
        // `ref` and KerML `feature` reach here only in a metadata body,
        // where they name the feature redefined.
        "feature" | "ref" => features(&[], &[]).with(Members::Inherited),
        "allocate" | "assign" | "bind" | "chains" | "connect" | "featuring" | "inverse"
        | "redefinition" | "subset" | "typing" | "variant" => features(&[], &[]),
        "to" if words.contains(&"dependency") => Want::new(&[], FIRST, Some(Names::All)),
        "to" if words.contains(&"send") => expression(src, stmt),
        "from" if before == Some("disjoint") => type_operands(src, stmt, dialect),
        "from" if words.contains(&"dependency") => Want::new(&[], FIRST, Some(Names::All)),
        "to" | "from" => features(&[], &[]),
        "by" => match before {
            Some("defined" | "typed") => typing(src, stmt, dialect),
            Some("featured") => types(ALL_DEFINITIONS, &[]),
            _ => features(&[], &[]),
        },
        "specializes" => specializing(src, stmt, dialect),
        "differences" | "intersects" | "unions" => type_operands(src, stmt, dialect),
        // A type, usually, but a feature may stand there too (`all
        // engineChoice`, `new testVehicle(…)`, `vehicles as vehicle`).
        "all" | "as" | "new" => types_then_features(),
        "conjugate" | "conjugates" | "disjoint" | "hastype" | "istype" | "meta"
        | "subclassifier" | "subtype" => types(ALL_DEFINITIONS, &[]),
        // An inverse's feature; a KerML binding's first end.
        "of" if before == Some("inverse") || words.contains(&"binding") => features(&[], &[]),
        "of" => types(ALL_DEFINITIONS, &[]),
        "about" | "expose" | "for" => Want::new(&[], FIRST, Some(Names::All)),
        "dependency" => Want::new(&["from"], AFTER, Some(Names::All)),
        "after" | "and" | "at" | "default" | "else" | "filter" | "if" | "implies" | "in"
        | "not" | "or" | "send" | "terminate" | "until" | "via" | "when" | "while" | "xor" => {
            expression(src, stmt)
        }
        "defined" | "featured" | "typed" => Want::new(&["by"], FIRST, None),
        "use" => Want::new(&["case"], FIRST, None),
        "standard" => Want::new(&["library"], FIRST, None),
        "library" => Want::new(&["package"], FIRST, None),
        // A string follows.
        "language" | "locale" => Want::new(&[], FIRST, None),
        "metadata" => Want {
            keywords: vec![("def", FIRST)],
            ..metadata_types()
        },
        // A new name or a connector's end, which names a feature.
        "flow" | "message" => ending(&["def", "from", "of"]),
        "interface" => ending(&["connect", "def"]),
        "connector" => ending(&["all", "from"]),
        "binding" => ending(&["all", "of"]),
        "succession" => ending(&["all", "first"]),
        _ => return None,
    })
}

/// Features, or one of `keywords` continuing the declaration instead.
fn ending(keywords: &[&'static str]) -> Want {
    Want {
        keywords: keywords.iter().map(|&k| (k, AFTER)).collect(),
        ..features(&[], &[])
    }
}

/// After an operand: in an expression, only an operator may follow, so
/// only the keyword operators are offered.
fn after_operand(src: &str, stmt: &[Token], body: Body, dialect: Dialect) -> Option<Want> {
    let keyword = |t: &Token| {
        (t.kind == TokenKind::Ident)
            .then(|| t.text(src))
            .filter(|w| is_reserved(dialect, w))
    };
    let opened = stmt.iter().any(|t| {
        matches!(
            t.kind,
            TokenKind::Eq | TokenKind::ColonEq | TokenKind::Question
        ) || keyword(t).is_some_and(|w| {
            matches!(
                w,
                "after"
                    | "and"
                    | "at"
                    | "default"
                    | "filter"
                    | "if"
                    | "implies"
                    | "not"
                    | "or"
                    | "send"
                    | "terminate"
                    | "until"
                    | "via"
                    | "when"
                    | "while"
                    | "xor"
            )
        })
    });
    // A result expression: the body's statement does not start with a
    // declaration keyword.
    let result = body.results()
        && stmt
            .first()
            .is_some_and(|t| keyword(t).is_none_or(|w| EXPRESSION_START.contains(&w)));
    // Where the grammar goes on with `then`: after an action's `if`
    // condition (`if level > 0 then …`), after an accept's payload or
    // trigger — an action's (`accept Sig then …`, `accept after 5 [s]
    // then …`) or a transition's (`accept after 5 [s] then on`) — after a
    // transition's guard (`if x > 0 then on`) — a state body's transition
    // starts at either — and after a succession's guard (`first a1 if x >
    // 0 then a2`).
    let has = |w: &str| stmt.iter().any(|t| keyword(t) == Some(w));
    let first = stmt.first().and_then(keyword);
    let transition =
        has("transition") || (body == Body::State && matches!(first, Some("accept" | "if")));
    let then = !has("then")
        && ((body == Body::Action && matches!(first, Some("if" | "accept")))
            || (transition && (has("accept") || has("if")))
            || (first == Some("first") && has("if")));
    // After a payload's type no operator follows: the grammar goes on
    // with `then` (`accept Sig then …`), the port the payload arrives
    // through (`accept Sig via port`), and a transition's guard and
    // effect (`accept Sig if ready do …`).
    if !(opened || result) {
        if !then {
            return None;
        }
        let mut keywords = vec!["then"];
        let effect = has("if") || has("do");
        if has("accept") && !has("via") && !effect {
            keywords.push("via");
        }
        if transition && !effect {
            keywords.push("if");
        }
        if transition && !has("do") {
            keywords.push("do");
        }
        return Some(Want::new(&keywords, FIRST, None));
    }
    let mut want = Want::new(INFIX, FIRST, None);
    if then {
        want.keywords.push(("then", FIRST));
    }
    Some(want)
}

/// An expression operand; literal booleans first where the statement
/// declares a `Boolean`.
fn expression(src: &str, stmt: &[Token]) -> Want {
    let typed = declared_type(src, stmt);
    let boolean = typed.as_deref() == Some("Boolean");
    Want {
        keywords: EXPRESSION_START
            .iter()
            .map(|&k| {
                let first = boolean && matches!(k, "true" | "false");
                (k, if first { FIRST } else { WITH_WORKSPACE })
            })
            .collect(),
        names: Some(Names::Operands { typed }),
    }
}

/// The type the statement declares what it declares by, last segment
/// only: `Boolean` for `: Boolean` and `: ScalarValues::Boolean`.
fn declared_type(src: &str, stmt: &[Token]) -> Option<String> {
    let at = stmt.iter().position(|t| t.kind == TokenKind::Colon)?;
    let mut name = None;
    for t in &stmt[at + 1..] {
        match t.kind {
            TokenKind::Ident | TokenKind::UnrestrictedName if name.is_none() => {
                name = Some(sysmlv2_parser::lexer::unescape(t.text(src)));
            }
            TokenKind::ColonColon if name.is_some() => name = None,
            _ => break,
        }
    }
    name
}

/// A typing: the definitions the statement's usage may be typed by.
fn typing(src: &str, stmt: &[Token], dialect: Dialect) -> Want {
    let metadata = stmt.first().is_some_and(|t| {
        t.kind == TokenKind::At || (t.kind == TokenKind::Ident && t.text(src) == "metadata")
    });
    if metadata {
        return metadata_types();
    }
    let kind = usage_kind(src, stmt, dialect).unwrap_or(UsageKind::Default);
    let (exact, compatible) = crate::kinds::typed_by(kind);
    types(exact, compatible)
}

/// After `:>` or `specializes`: a definition's supertypes, a usage's
/// subsetted features.
fn specializing(src: &str, stmt: &[Token], dialect: Dialect) -> Want {
    match definition_kind(src, stmt, dialect) {
        Some(kind) => {
            let (exact, compatible) = crate::kinds::specializes(kind);
            types(&exact, &compatible)
        }
        None => of_kind(src, stmt, dialect, Members::Scope),
    }
}

/// Inside `(`: a connector's ends (`connect (a, b)`) or an expression.
fn opened(src: &str, ahead: &[Token], dialect: Dialect) -> Want {
    let connector = ahead.last().is_some_and(|t| {
        t.kind == TokenKind::Ident
            && is_reserved(dialect, t.text(src))
            && matches!(t.text(src), "allocate" | "connect" | "interface")
    });
    if connector {
        features(&[], &[])
    } else {
        expression(src, ahead)
    }
}

/// After a `,`: the list it continues decides — a typing, a
/// specialization, subsetted or redefined features, arguments, ends.
fn continuing(src: &str, ahead: &[Token], dialect: Dialect) -> Option<Want> {
    let mut depth = 0usize;
    for (i, t) in ahead.iter().enumerate().rev() {
        let upto = &ahead[..=i];
        match t.kind {
            TokenKind::RParen | TokenKind::RBracket => depth += 1,
            TokenKind::LParen | TokenKind::LBracket if depth > 0 => depth -= 1,
            TokenKind::LParen => return Some(opened(src, &ahead[..i], dialect)),
            TokenKind::LBracket => return None,
            _ if depth > 0 => {}
            TokenKind::Colon => return Some(typing(src, upto, dialect)),
            TokenKind::ColonGt => return Some(specializing(src, upto, dialect)),
            TokenKind::ColonGtGt => {
                return Some(of_kind(src, upto, dialect, Members::Inherited));
            }
            TokenKind::ColonColonGt | TokenKind::FatArrow => {
                return Some(of_kind(src, upto, dialect, Members::None));
            }
            TokenKind::Eq | TokenKind::ColonEq => return Some(expression(src, upto)),
            TokenKind::Ident if is_reserved(dialect, t.text(src)) => {
                if matches!(
                    t.text(src),
                    "about"
                        | "by"
                        | "crosses"
                        | "differences"
                        | "disjoint"
                        | "from"
                        | "intersects"
                        | "redefines"
                        | "references"
                        | "specializes"
                        | "subsets"
                        | "to"
                        | "unions"
                ) {
                    return after_keyword(src, upto, t.text(src), dialect);
                }
            }
            _ => {}
        }
    }
    None
}

/// A feature position of `stmt` (`:>>`, `subsets`, `references`, …)
/// naming the enclosing element's `members`: features of the kind of the
/// usage it declares (see [`usage_kind`]) first, then of the kinds
/// specializing it, whose usages are of that kind too — an item
/// redefines the parts it inherits (see [`crate::kinds::usages_of`]) —
/// or of every kind where its keywords name none: a `ref`, a `subject`,
/// and a KerML `feature` may be features of any. A redefinition ranks a
/// compound keyword's kind first among those its kind word takes (see
/// [`declared_kinds`]): a `perform action` redefines the performed
/// actions first, then the others. A subsetting or a reference ranks
/// the kind word's own first, more general than what it declares
/// (`include use case board_a :> board` subsets a plain use case). An
/// individual, a snapshot, or a time slice naming no kind of its own is
/// one of whatever occurrence it names, every kind of occurrence alike
/// (`snapshot crewAtIngress :> crew`).
fn of_kind(src: &str, stmt: &[Token], dialect: Dialect, members: Members) -> Want {
    let occurrence = stmt
        .iter()
        .any(|t| t.kind == TokenKind::Ident && t.text(src) == "occurrence");
    let all = |kind: UsageKind| {
        let (own, under) = crate::kinds::usages_of(kind);
        [own, under].concat()
    };
    let (own, specific) = match declared_kinds(src, stmt, dialect) {
        None | Some((UsageKind::Ref | UsageKind::Feature, _)) => (Vec::new(), Vec::new()),
        Some((UsageKind::Occurrence, _)) if !occurrence => (all(UsageKind::Occurrence), Vec::new()),
        // The kinds its kind word takes, the first one ahead.
        Some((kind, word)) => {
            let first = if members == Members::Inherited {
                kind
            } else {
                word
            };
            let (own, _) = crate::kinds::usages_of(first);
            let specific = all(word).into_iter().filter(|k| !own.contains(k)).collect();
            (own, specific)
        }
    };
    Want {
        keywords: Vec::new(),
        names: Some(Names::Features {
            preferred: [own, specific.clone()].concat(),
            definitions: Vec::new(),
            strict: false,
            members,
            specific,
        }),
    }
}

/// The kind of the usage `stmt` declares, from its kind keywords (`in
/// item fuel` is an item, `perform action a` a performed action); `None`
/// when it has none (`in x`, `ref`-less `x`, a bare `perform`). A payload
/// follows `accept` and a flow's or a message's `of` (`action trigger
/// accept sig : Signal`, `message of cmd : Command`): the statement's
/// kind does not type it.
fn usage_kind(src: &str, stmt: &[Token], dialect: Dialect) -> Option<UsageKind> {
    declared_kinds(src, stmt, dialect).map(|(kind, _)| kind)
}

/// The kind of the usage `stmt` declares (see [`usage_kind`]) and the
/// kind its last kind word names alone: a keyword ahead of that word
/// makes it a more specific kind — `perform action` a performed action,
/// which is an action, `exhibit state` an exhibited state, `include use
/// case` an included use case, `satisfy requirement` a satisfied
/// requirement, `assert constraint` an asserted constraint, and `event
/// occurrence` an event — while `item x` declares an item alone.
fn declared_kinds(src: &str, stmt: &[Token], dialect: Dialect) -> Option<(UsageKind, UsageKind)> {
    use UsageKind as U;
    let mut kinds = None;
    let (mut prev, mut before): (Option<&str>, Option<&str>) = (None, None);
    for t in stmt {
        let Some(w) = (t.kind == TokenKind::Ident)
            .then(|| t.text(src))
            .filter(|w| is_reserved(dialect, w))
        else {
            (prev, before) = (None, None);
            continue;
        };
        if matches!(w, "accept" | "of") {
            kinds = None;
            (prev, before) = (Some(w), prev);
            continue;
        }
        let word = match w {
            "attribute" => Some(U::Attribute),
            "enum" => Some(U::Enum),
            "occurrence" => Some(U::Occurrence),
            "item" => Some(U::Item),
            "part" | "actor" | "stakeholder" => Some(U::Part),
            "port" => Some(U::Port),
            "connection" => Some(U::Connection),
            "interface" => Some(U::Interface),
            "allocation" => Some(U::Allocation),
            "flow" if prev == Some("succession") => Some(U::SuccessionFlow),
            "flow" => Some(U::Flow),
            "message" => Some(U::Message),
            "action" => Some(U::Action),
            "state" => Some(U::State),
            "calc" => Some(U::Calc),
            "constraint" => Some(U::Constraint),
            "requirement" | "objective" => Some(U::Requirement),
            "concern" => Some(U::Concern),
            "case" if prev == Some("use") => Some(U::UseCase),
            "case" => Some(U::Case),
            "analysis" => Some(U::Analysis),
            "verification" => Some(U::Verification),
            "view" => Some(U::View),
            "viewpoint" => Some(U::Viewpoint),
            "rendering" => Some(U::Rendering),
            "metadata" => Some(U::Metadata),
            "ref" | "subject" => Some(U::Ref),
            "event" => Some(U::Event),
            "individual" | "snapshot" | "timeslice" => Some(U::Occurrence),
            "binding" => Some(U::Binding),
            "succession" => Some(U::Succession),
            "feature" => Some(U::Feature),
            "step" => Some(U::Step),
            "expr" => Some(U::Expr),
            "bool" => Some(U::BoolExpr),
            "inv" => Some(U::Invariant),
            "connector" => Some(U::Connector),
            _ => None,
        };
        let declared = match (w, prev, before) {
            ("action", Some("perform"), _) => Some(U::Perform),
            ("state", Some("exhibit"), _) => Some(U::Exhibit),
            ("case", Some("use"), Some("include")) => Some(U::Include),
            ("requirement", Some("satisfy"), _) => Some(U::Satisfy),
            ("constraint", Some("assert"), _) | ("constraint", Some("not"), Some("assert")) => {
                Some(U::AssertConstraint)
            }
            ("occurrence", Some("event"), _) => Some(U::Event),
            _ => word,
        };
        if let (Some(declared), Some(word)) = (declared, word) {
            kinds = Some((declared, word));
        }
        (prev, before) = (Some(w), prev);
    }
    kinds
}

/// The kind of the definition or KerML type `stmt` declares; `None`
/// when it declares a usage or a feature.
fn definition_kind(src: &str, stmt: &[Token], dialect: Dialect) -> Option<DefKind> {
    use DefKind as D;
    let words: Vec<&str> = stmt
        .iter()
        .filter(|t| t.kind == TokenKind::Ident)
        .map(|t| t.text(src))
        .filter(|w| is_reserved(dialect, w))
        .collect();
    if let Some(at) = words.iter().position(|w| *w == "def") {
        let kind = |w: &str| match w {
            "attribute" => D::Attribute,
            "enum" => D::Enum,
            "occurrence" => D::Occurrence,
            "individual" => D::Individual,
            "item" => D::Item,
            "metadata" => D::Metadata,
            "part" => D::Part,
            "port" => D::Port,
            "connection" => D::Connection,
            "interface" => D::Interface,
            "allocation" => D::Allocation,
            "flow" => D::Flow,
            "action" => D::Action,
            "state" => D::State,
            "calc" => D::Calc,
            "constraint" => D::Constraint,
            "requirement" => D::Requirement,
            "concern" => D::Concern,
            "case" if at >= 2 && words[at - 2] == "use" => D::UseCase,
            "case" => D::Case,
            "analysis" => D::Analysis,
            "verification" => D::Verification,
            "view" => D::View,
            "viewpoint" => D::Viewpoint,
            "rendering" => D::Rendering,
            _ => D::Extended,
        };
        return Some(at.checked_sub(1).map_or(D::Extended, |i| kind(words[i])));
    }
    words.iter().enumerate().find_map(|(i, w)| match *w {
        "assoc" if words.get(i + 1) == Some(&"struct") => Some(D::AssocStruct),
        "assoc" => Some(D::Assoc),
        "behavior" => Some(D::Behavior),
        "class" => Some(D::Class),
        "classifier" => Some(D::Classifier),
        "datatype" => Some(D::DataType),
        "function" => Some(D::Function),
        "interaction" => Some(D::Interaction),
        "metaclass" => Some(D::Metaclass),
        "predicate" => Some(D::Predicate),
        "struct" => Some(D::Struct),
        "type" => Some(D::Type),
        _ => None,
    })
}

const VISIBILITY: &[&str] = &["private", "protected", "public"];

/// The annotating members any body takes.
const ANNOTATIONS: &[&str] = &["comment", "doc", "language", "locale", "metadata", "rep"];

/// The SysML keywords starting a definition or a usage, or a namespace
/// member, in any body that declares members.
const MEMBERS: &[&str] = &[
    "abstract",
    "action",
    "alias",
    "allocate",
    "allocation",
    "analysis",
    "assert",
    "attribute",
    "bind",
    "binding",
    "calc",
    "case",
    "concern",
    "connect",
    "connection",
    "constant",
    "constraint",
    "dependency",
    "derived",
    "end",
    "enum",
    "event",
    "exhibit",
    "first",
    "flow",
    "import",
    "in",
    "include",
    "individual",
    "inout",
    "interface",
    "item",
    "library",
    "message",
    "occurrence",
    "out",
    "package",
    "part",
    "perform",
    "port",
    "ref",
    "rendering",
    "requirement",
    "satisfy",
    "snapshot",
    "standard",
    "state",
    "succession",
    "timeslice",
    "use",
    "variation",
    "verification",
    "view",
    "viewpoint",
];

/// The KerML keywords starting a type, a feature, a relationship, or a
/// namespace member.
const KERML_MEMBERS: &[&str] = &[
    "abstract",
    "alias",
    "assoc",
    "behavior",
    "binding",
    "bool",
    "class",
    "classifier",
    "composite",
    "conjugate",
    "conjugation",
    "connector",
    "const",
    "datatype",
    "dependency",
    "derived",
    "disjoining",
    "disjoint",
    "end",
    "expr",
    "feature",
    "featuring",
    "flow",
    "function",
    "import",
    "in",
    "inout",
    "interaction",
    "inv",
    "inverse",
    "inverting",
    "library",
    "metaclass",
    "multiplicity",
    "namespace",
    "out",
    "package",
    "portion",
    "predicate",
    "redefinition",
    "specialization",
    "standard",
    "step",
    "struct",
    "subclassifier",
    "subset",
    "subtype",
    "succession",
    "type",
    "typing",
    "var",
];

/// A statement's first word: the keywords its body takes, and names
/// where the body ends in a result expression (or, in a metadata
/// body, redefines features by name). `after_prefix`: visibility or
/// prefix metadata came first.
fn statement_start(body: Body, dialect: Dialect, after_prefix: bool) -> Option<Want> {
    let action: &[&str] = &[
        "accept",
        "assign",
        "decide",
        "for",
        "fork",
        "if",
        "join",
        "loop",
        "merge",
        "send",
        "terminate",
        "while",
    ];
    let (groups, key, names): (Vec<&[&str]>, u8, Option<Names>) = match (dialect, body) {
        (_, Body::Other | Body::Enumeration) => return None,
        (_, Body::Metadata) => (
            vec![&["alias", "feature", "import", "redefines", "ref"]],
            AFTER,
            features(&[], &[]).with(Members::Inherited).names,
        ),
        (Dialect::Sysml, Body::Namespace) => (vec![MEMBERS, &["filter"]], FIRST, None),
        (Dialect::Sysml, Body::Definition | Body::Type) => {
            (vec![MEMBERS, &["then", "variant"]], FIRST, None)
        }
        (Dialect::Sysml, Body::Action) => {
            (vec![MEMBERS, &["then", "variant"], action], FIRST, None)
        }
        (Dialect::Sysml, Body::State) => (
            vec![
                MEMBERS,
                &["then", "variant"],
                &["accept", "do", "entry", "exit", "if", "transition"],
            ],
            FIRST,
            None,
        ),
        (Dialect::Sysml, Body::Calculation { case }) => (
            vec![
                MEMBERS,
                &["then", "variant", "return"],
                action,
                EXPRESSION_START,
                if case {
                    &["actor", "objective", "subject"]
                } else {
                    &[]
                },
            ],
            WITH_WORKSPACE,
            Some(Names::Operands { typed: None }),
        ),
        (Dialect::Sysml, Body::Function) => (
            vec![
                MEMBERS,
                &["then", "variant", "return"],
                action,
                EXPRESSION_START,
            ],
            WITH_WORKSPACE,
            Some(Names::Operands { typed: None }),
        ),
        (Dialect::Sysml, Body::Requirement) => (
            vec![
                MEMBERS,
                &["then", "variant"],
                &[
                    "actor",
                    "assume",
                    "frame",
                    "require",
                    "stakeholder",
                    "subject",
                    "verify",
                ],
            ],
            FIRST,
            None,
        ),
        (Dialect::Sysml, Body::View) => (
            vec![
                MEMBERS,
                &["then", "variant"],
                &["expose", "filter", "render"],
            ],
            FIRST,
            None,
        ),
        (Dialect::Kerml, Body::Namespace) => (vec![KERML_MEMBERS, &["filter"]], FIRST, None),
        (Dialect::Kerml, Body::Function | Body::Calculation { .. }) => (
            vec![KERML_MEMBERS, &["member", "return"], EXPRESSION_START],
            WITH_WORKSPACE,
            Some(Names::Operands { typed: None }),
        ),
        (Dialect::Kerml, _) => (vec![KERML_MEMBERS, &["member"]], FIRST, None),
    };
    let mut keywords: Vec<(&'static str, u8)> = Vec::new();
    let prefixes: &[&[&str]] = if after_prefix { &[] } else { &[VISIBILITY] };
    for &group in prefixes.iter().chain(&[ANNOTATIONS]).chain(&groups) {
        for &w in group {
            if !keywords.iter().any(|&(k, _)| k == w) {
                keywords.push((w, key));
            }
        }
    }
    Some(Want { keywords, names })
}

#[cfg(test)]
mod tests {
    use super::{Declarer, KERML, SYSML, Slot, scan};
    use crate::position::offset32;
    use sysmlv2_parser::ast::Dialect;
    use sysmlv2_parser::parser::is_reserved;

    /// The slot at the `|` in `marked`, the word being completed being
    /// the identifier run before it.
    fn slot_in(dialect: Dialect, marked: &str) -> Slot {
        let at = marked.find('|').expect("cursor marker");
        let text = marked.replacen('|', "", 1);
        let word_start = text[..at]
            .rfind(|c: char| !(c.is_ascii_alphanumeric() || c == '_'))
            .map_or(0, |i| i + 1);
        scan(&text, offset32(word_start), offset32(at), dialect).slot
    }

    fn slot(marked: &str) -> Slot {
        slot_in(Dialect::Sysml, marked)
    }

    /// Neither quiet nor a declared name: completion is on.
    fn open(slot: &Slot) -> bool {
        matches!(slot, Slot::Want(_) | Slot::Open)
    }

    fn scanned(marked: &str) -> super::Scan {
        let at = marked.find('|').expect("cursor marker");
        let text = marked.replacen('|', "", 1);
        scan(&text, offset32(at), offset32(at), Dialect::Sysml)
    }

    #[test]
    fn tables_are_sorted_reserved_words() {
        for (dialect, table) in [(Dialect::Sysml, SYSML), (Dialect::Kerml, KERML)] {
            assert!(
                table.windows(2).all(|w| w[0].keyword < w[1].keyword),
                "{dialect:?} table must stay sorted for binary search"
            );
            for Declarer { keyword, instead } in table {
                assert!(is_reserved(dialect, keyword), "{dialect:?}: {keyword}");
                for w in instead.iter().flat_map(|g| g.iter()) {
                    assert!(is_reserved(dialect, w), "{dialect:?}: {keyword} → {w}");
                }
            }
        }
    }

    #[test]
    fn prose_is_quiet() {
        for marked in [
            "part def V {\n    /* the wheel|",
            "part def V {\n    doc /* A vehicle part.|",
            "part def V {\n    doc /* A vehicle part.|\n     */\n}",
            "part def V {\n    // TODO:|",
            "part def V {\n    // see Wheel::|",
            "part def V {\n    //* note: |*/\n}",
            "part def V {\n    comment about V /* see V.|",
            "attribute s : String = \"v1.|",
            "attribute s : String = \"v1.|2\";",
            "attribute s = \"a\" + \"b: |",
            "attribute s = \"say \\\"hi|",
        ] {
            assert_eq!(slot(marked), Slot::Quiet, "{marked:?}");
        }
        for marked in [
            // after a closed comment, note, or string
            "part def V {\n    /* done */ part w : W|",
            "part def V {\n    //* done */ part w : W|",
            "part def V {\n    // done\n    part w : W|",
            "attribute s = \"a\" + b|",
            // a quoted name being typed is a name, not prose
            "part w : 'Wheel O|",
            "part w : '|",
        ] {
            assert!(open(&slot(marked)), "{marked:?}: {:?}", slot(marked));
        }
    }

    #[test]
    fn numbers_and_range_bounds_are_quiet() {
        for marked in [
            "attribute x = 5|",
            "attribute x = 12|",
            "attribute x = 5.|",
            "attribute x = 5.4|",
            "attribute x = 1.5e|",
            "attribute x = 1.5e3|",
            "attribute x = 1.5e-|",
            "attribute x = 2E+|",
            "attribute x = .|",
            "attribute x = (.|",
            "part ws : Wheel [0.|",
            "part ws : Wheel [0..|",
            "part ws : Wheel [1..*|",
            "part ws : Wheel [*|",
            "attribute x = *|",
        ] {
            assert_eq!(slot(marked), Slot::Quiet, "{marked:?}");
        }
        for marked in [
            // a feature chain, a product, a bound named by a feature
            "attribute x = vehicle.|",
            "attribute x = vehicle.ma|",
            "attribute x = 2 * |",
            "attribute x = a *|",
            "part ws : Wheel [0..n|",
            "attribute x = e-|",
            "attribute x = v1|",
            "attribute x = 9.8 [|",
            "attribute x = 9.8 [k|",
        ] {
            assert!(open(&slot(marked)), "{marked:?}: {:?}", slot(marked));
        }
    }

    /// Every class of SysML declaration: its name takes no reference.
    #[test]
    fn sysml_declared_names() {
        for marked in [
            // definitions, with their prefixes
            "part def B|",
            "abstract part def B|",
            "variation part def B|",
            "#Safety part def B|",
            "private attribute def M|",
            "use case def U|",
            "individual def I|",
            "individual part def I|",
            "enum def E|",
            "metadata def M|",
            "occurrence def O|",
            "flow def F|",
            "interface def I|",
            // usages of every kind that declares a name
            "part e|",
            "attribute m|",
            "state o|",
            "action a|",
            "port p|",
            "item i|",
            "connection c|",
            "allocation a|",
            "calc c|",
            "constraint c|",
            "requirement r|",
            "concern c|",
            "case c|",
            "use case u|",
            "analysis a|",
            "verification v|",
            "view v|",
            "viewpoint v|",
            "rendering r|",
            "occurrence o|",
            "enum e|",
            "binding b|",
            "succession s|",
            "event occurrence e|",
            // usage prefixes, with or without a kind
            "ref part x|",
            "in item fuel|",
            "out attribute a|",
            "abstract part p|",
            "derived ref r|",
            "in f|",
            "out d|",
            "inout x|",
            "return r|",
            "end e|",
            "ref r|",
            "abstract a|",
            "constant c|",
            "derived d|",
            "variation v|",
            "individual i|",
            "snapshot s|",
            "timeslice t|",
            // behaviors declared with their usage keyword
            "perform action a|",
            "exhibit state s|",
            "include use case u|",
            "assert constraint c|",
            "assert not constraint c|",
            "satisfy requirement r|",
            "require constraint c|",
            "assume constraint c|",
            "frame concern c|",
            "verify requirement r|",
            "render rendering r|",
            "entry action e|",
            "then action a|",
            // annotations, namespaces, aliases
            "comment c|",
            "doc d|",
            "rep r|",
            "package P|",
            "library package L|",
            "standard library package S|",
            "alias A|",
            // requirement and case members
            "subject s|",
            "actor d|",
            "stakeholder s|",
            "objective o|",
            // control nodes and loop variables
            "merge m|",
            "decide d|",
            "join j|",
            "fork f|",
            "for i|",
            // short names, and the name after one
            "part def <V|",
            "part <p|",
            "alias <a|",
            "package <P|",
            "part def <V> Veh|",
            "part def <'V'> Veh|",
            // with nothing typed yet
            "part def |",
            "part |",
        ] {
            assert!(
                matches!(slot(marked), Slot::Declared(_)),
                "{marked:?}: {:?}",
                slot(marked)
            );
        }
    }

    /// A bare member of an enumeration body declares a literal.
    #[test]
    fn enumeration_literals() {
        for marked in [
            "enum def Color {\n    r|",
            "enum def Color {\n    red;\n    g|",
            "enum def Color {\n    enum b|",
            "enum def Color {\n    private g|",
            "enum def Color {\n    doc /* The colors */\n    g|",
            "enum def Color {\n    <r|",
            "enum def Color {\n    <r> re|",
            "#Palette enum def Color {\n    r|",
            "package P {\n    enum def Color {\n        |",
        ] {
            assert!(
                matches!(slot(marked), Slot::Declared(_)),
                "{marked:?}: {:?}",
                slot(marked)
            );
        }
        // Past the body, or in another body, a bare word is no literal.
        for marked in [
            "enum def Color {\n    red;\n}\nr|",
            "enum def Color {\n    red;\n}\npart def P {\n    r|",
            "enum def Color {\n    red = c|",
            "enum def Color {\n    red :> c|",
            "part def P {\n    enum def Color;\n    r|",
            "enum e : Color {\n    r|",
        ] {
            assert!(open(&slot(marked)), "{marked:?}: {:?}", slot(marked));
        }
    }

    /// Keywords whose next word may be a reference keep completion on.
    #[test]
    fn sysml_references_stay_open() {
        for marked in [
            "perform x|",
            "exhibit x|",
            "include x|",
            "assert x|",
            "assert not x|",
            "satisfy R|",
            "satisfy R by v|",
            "satisfy requirement r : R by v|",
            "verify R|",
            "frame C|",
            "require C|",
            "render asTree|",
            "then a|",
            "first o|",
            "first o then a|",
            "entry e|",
            "do d|",
            "exit e|",
            "accept sig : S|",
            "bind a = b|",
            "bind a|",
            "connect a|",
            "connect a to b|",
            "connection c connect a to b|",
            "allocate a|",
            "alias A for B|",
            "event e|",
            "variant v|",
            "for i in c|",
            "import X|",
            "private import X::|",
            "expose x|",
            "send x|",
            "assign x|",
            "if c|",
            "part p : T|",
            "part p defined by T|",
            "part p :> q|",
            "part p subsets q|",
            "part p :>> q|",
            "part def C :> V|",
            "part def C specializes V|",
            "attribute m = x|",
            "attribute m : T = x|",
            "part p : T [0..n|",
            "part p = a.|",
            "part p = a.b|",
            "part p : A::|",
            "part def P :> A::B|",
            // either a name or a reference: only the rest tells
            "transition t|",
            "transition initial then off|",
            "accept s|",
            "flow f|",
            "message m|",
            "interface i|",
            "metadata M|",
            "@M|",
            "dependency d|",
            "succession flow f|",
            // a statement's first word: a keyword, a name, or a reference
            "part def P {\n    x|",
            "part def P {\n    private x|",
            // past the declared name
            "part def Car s|",
            "part engine : E|",
            // a metadata body's members redefine features by name
            "@M {\n    ref r|",
            "metadata m : M {\n    ref r|",
        ] {
            assert!(open(&slot(marked)), "{marked:?}: {:?}", slot(marked));
        }
    }

    /// A `def` continues the head only after definition prefixes.
    #[test]
    fn def_follows_definition_prefixes_only() {
        let declared = |marked: &str| match slot(marked) {
            Slot::Declared(words) => words,
            other => panic!("{marked:?}: {other:?}"),
        };
        for marked in [
            "part |",
            "abstract part |",
            "variation part |",
            "individual part |",
            "private #Safety part |",
            "use case |",
            "individual |",
        ] {
            assert!(declared(marked).contains(&"def"), "{marked:?}");
        }
        for marked in [
            "ref part |",
            "in item |",
            "perform action |",
            "include use case |",
            "event occurrence |",
            "then action |",
            "enum def Color {\n    enum |",
        ] {
            assert!(!declared(marked).contains(&"def"), "{marked:?}");
        }
        assert_eq!(declared("part def |"), Vec::<&str>::new());
        assert_eq!(declared("package |"), Vec::<&str>::new());
        assert_eq!(declared("comment |"), vec!["about", "locale"]);
        assert!(declared("in |").contains(&"item"));
        assert!(declared("ref |").contains(&"part"));
        assert_eq!(declared("part def <V|"), Vec::<&str>::new());
    }

    #[test]
    fn kerml_declared_names() {
        for marked in [
            "class C|",
            "abstract class C|",
            "struct S|",
            "datatype D|",
            "assoc A|",
            "assoc struct A|",
            "behavior B|",
            "function F|",
            "predicate P|",
            "interaction I|",
            "metaclass M|",
            "classifier C|",
            "type T|",
            "feature f|",
            "step s|",
            "expr e|",
            "bool b|",
            "inv i|",
            "in x|",
            "out y|",
            "inout z|",
            "abstract a|",
            "composite c|",
            "portion p|",
            "var v|",
            "const c|",
            "end e|",
            "derived d|",
            "member m|",
            "return r|",
            "multiplicity m|",
            "namespace N|",
            "package P|",
            "specialization s|",
            "conjugation c|",
            "disjoining d|",
            "inverting i|",
            "alias A|",
            "comment c|",
            "doc d|",
            "rep r|",
            "class <C|",
            "class <C> Ca|",
            "function F {\n    in x|",
            // sufficiency and polarity come before the name
            "class all C|",
            "assoc all B|",
            "feature all f|",
            "step all s|",
            "inv true c|",
            "inv false c|",
        ] {
            assert!(
                matches!(slot_in(Dialect::Kerml, marked), Slot::Declared(_)),
                "{marked:?}: {:?}",
                slot_in(Dialect::Kerml, marked)
            );
        }
        for marked in [
            // either a name or a reference
            "connector c|",
            "binding b|",
            "succession s|",
            "flow f|",
            "featuring f|",
            "metadata M|",
            // references
            "subtype a|",
            "subclassifier a|",
            "typing t|",
            "feature f : T|",
            "class C specializes B|",
            "alias A for B|",
            "@M {\n    feature f|",
            "import all X|",
            "connector all a|",
            // SysML words are names in KerML
            "part p|",
            "attribute a|",
        ] {
            let slot = slot_in(Dialect::Kerml, marked);
            assert!(open(&slot), "{marked:?}: {slot:?}");
        }
        // ... and KerML words are names in SysML.
        for marked in ["class C|", "feature f|", "datatype D|"] {
            assert!(open(&slot(marked)), "{marked:?}: {:?}", slot(marked));
        }
    }

    /// Keywords the grammar puts where a declaration's name would be:
    /// `abstract metadata def`, `variation perform`, and a usage
    /// redefining without a name of its own (`part redefines engine`,
    /// `ref redefines x`, KerML `feature redefines f`).
    #[test]
    fn declaration_heads_take_their_grammar_keywords() {
        let declared = |dialect: Dialect, marked: &str| match slot_in(dialect, marked) {
            Slot::Declared(words) => words,
            other => panic!("{marked:?}: {other:?}"),
        };
        for (marked, word) in [
            ("abstract |", "metadata"),
            ("variation |", "perform"),
            ("abstract |", "exhibit"),
            ("part |", "redefines"),
            ("attribute |", "redefines"),
            ("ref |", "redefines"),
            ("in |", "redefines"),
        ] {
            assert!(
                declared(Dialect::Sysml, marked).contains(&word),
                "{marked:?}"
            );
        }
        for (marked, word) in [("feature |", "redefines"), ("in |", "redefines")] {
            assert!(
                declared(Dialect::Kerml, marked).contains(&word),
                "{marked:?}"
            );
        }
        assert!(!declared(Dialect::Kerml, "class all |").contains(&"all"));
        assert!(declared(Dialect::Kerml, "inv true |").is_empty());
    }

    /// The statement starts after the last `;`, `{`, `}`, or comment
    /// body token — never inside a comment, note, string, or quoted
    /// name, nor in an expression's body passed within a `(`, which is
    /// part of the statement around it. Signature help cuts the
    /// statement completion does.
    #[test]
    fn statement_start_on_tokens() {
        for (marked, start) in [
            (
                "package P {\n    attribute e = f({ in z; z }, v.|",
                "attribute e",
            ),
            ("package P {\n    attribute e = f(1, g({ in z; z|", "z"),
            (
                "attribute a; attribute e = f({ in z; z }, (1), [2], |",
                "attribute e",
            ),
            ("part def A { }\n    attribute e = f(1, |", "attribute e"),
            (
                "x\ndoc /* The\n * energy; }\n */ attribute e = f(1, |",
                "attribute e",
            ),
            ("package P {\n    part x : T|", "part x"),
            ("package P {\n    /* a; b { c } */ part x : T|", "part x"),
            // notes are no statements' tokens
            ("package P {\n    // a; b }\n    part x|", "part x"),
            ("package P {\n    //* a;\n b } */ part x|", "part x"),
            (
                "package P {\n    attribute s = \"a;b}\" + c|",
                "attribute s",
            ),
            ("package P {\n    attribute 'a;b' : T|", "attribute 'a;b'"),
            ("package P {\n    doc /* d */\n    part x|", "part x"),
            ("package P {\n    part x;\n    part y|", "part y"),
            // a quoted name, or a string, left open on an earlier line
            // runs no further than it: this line is read on its own
            (
                "package P {\n    attribute s = 'open;\n    part y|",
                "part y",
            ),
            (
                "package P {\n    attribute s = \"open;\n    part y|",
                "part y",
            ),
            ("part x|", "part x"),
        ] {
            let s = scanned(marked);
            let text = marked.replacen('|', "", 1);
            assert!(
                text[s.stmt_start as usize..].starts_with(start),
                "{marked:?}: starts at {:?}",
                &text[s.stmt_start as usize..]
            );
            let prefix = &text[..marked.find('|').expect("cursor")];
            let (tokens, line) = super::tokens_ahead(prefix);
            assert_eq!(
                super::statement_begins(prefix, &tokens, line),
                s.stmt_start,
                "{marked:?}"
            );
        }
        // Nothing typed yet: the cursor.
        let marked = "package P {\n    part x;\n    |";
        assert_eq!(scanned(marked).stmt_start as usize, marked.len() - 1);
    }

    #[test]
    fn import_statements_on_tokens() {
        for (marked, import) in [
            ("package P {\n    private import X|", true),
            ("package P {\n    import A::B::|", true),
            ("package P {\n    public import all X|", true),
            // the word inside a note, a comment, or a string is no keyword
            ("package P {\n    // import note\n    part w : W|", false),
            ("package P {\n    part w : W /* import */|", false),
            ("package P {\n    attribute s = \"import\" + x|", false),
            ("package P {\n    private import X;\n    part w : W|", false),
        ] {
            assert_eq!(scanned(marked).import, import, "{marked:?}");
        }
    }

    /// The `Want` at the `|` in `marked`, which must be one.
    fn want_in(dialect: Dialect, marked: &str) -> super::Want {
        match slot_in(dialect, marked) {
            Slot::Want(want) => want,
            other => panic!("{marked:?}: {other:?}"),
        }
    }

    fn want(marked: &str) -> super::Want {
        want_in(Dialect::Sysml, marked)
    }

    fn keywords(want: &super::Want) -> Vec<&'static str> {
        want.keywords.iter().map(|&(k, _)| k).collect()
    }

    /// After `:` (or `~`, `defined by`), the definitions a usage of the
    /// statement's kind may be typed by — and no keyword.
    #[test]
    fn typing_positions_take_their_kinds_definitions() {
        use super::Names;
        use sysmlv2_parser::ast::DefKind as D;
        for (marked, fits, loose, not) in [
            (
                "part p : |",
                &[D::Part, D::Connection, D::Interface, D::View][..],
                &[D::Item, D::Port][..],
                &[D::Attribute, D::Action][..],
            ),
            (
                "attribute x : Rea|",
                &[D::Attribute, D::Enum, D::DataType],
                &[],
                &[D::Part, D::Item],
            ),
            ("port p : ~|", &[D::Port], &[], &[D::Part]),
            ("port p defined by ~|", &[D::Port], &[], &[D::Part]),
            (
                "action d : Dr|",
                &[D::Action, D::Behavior],
                &[D::Calc],
                &[D::Part],
            ),
            (
                "in item f : F|",
                &[D::Item, D::Part],
                &[D::Port],
                &[D::Attribute],
            ),
            ("state s : |", &[D::State], &[D::Action], &[D::Part]),
            (
                "constraint c : |",
                &[D::Constraint, D::Predicate],
                &[D::Requirement],
                &[],
            ),
            ("calc k : |", &[D::Calc, D::Function], &[D::Case], &[]),
            ("requirement r : |", &[D::Requirement], &[D::Concern], &[]),
            ("exhibit state s : |", &[D::State], &[D::Action], &[D::Part]),
            (
                "perform action a : |",
                &[D::Action],
                &[D::State],
                &[D::Part],
            ),
            ("include use case u : |", &[D::UseCase], &[], &[D::Case]),
            ("frame concern c : |", &[D::Concern], &[], &[]),
            ("actor d : |", &[D::Part], &[D::Item], &[]),
            ("enum e : |", &[D::Enum], &[], &[D::Attribute]),
            (
                "metadata m : |",
                &[D::Metadata, D::Metaclass],
                &[],
                &[D::Part],
            ),
            ("part p : A, |", &[D::Part], &[D::Item], &[D::Attribute]),
            // a reference, a parameter without kind, a payload: any type
            ("ref r : |", &[D::Part, D::Attribute, D::DataType], &[], &[]),
            ("in x : |", &[D::Part, D::Attribute, D::Class], &[], &[]),
            ("accept sig : S|", &[D::Item, D::Attribute], &[], &[]),
        ] {
            let w = want(marked);
            assert!(w.keywords.is_empty(), "{marked:?}: {:?}", w.keywords);
            let Some(Names::Types {
                exact, compatible, ..
            }) = &w.names
            else {
                panic!("{marked:?}: {:?}", w.names);
            };
            for k in fits {
                assert!(exact.contains(k), "{marked:?}: {k:?} in {exact:?}");
            }
            for k in loose {
                assert!(
                    compatible.contains(k),
                    "{marked:?}: {k:?} in {compatible:?}"
                );
            }
            for k in not {
                assert!(
                    !exact.contains(k) && !compatible.contains(k),
                    "{marked:?}: {k:?}"
                );
            }
        }
    }

    /// `:>` on a definition takes supertypes of its kind first, on a
    /// usage the features it subsets; `:>>` the features it redefines,
    /// those of the usage's kind and of the kinds specializing it first
    /// (a part is an item, an interface a connection, and a message a
    /// flow), of every kind after a `ref` or a KerML `feature`, which
    /// name none.
    #[test]
    fn specialization_and_feature_positions() {
        use super::Names;
        use crate::kinds::Decl;
        use sysmlv2_parser::ast::{DefKind as D, UsageKind as U};
        for (marked, exact) in [
            ("part def Sedan :> C|", D::Part),
            ("attribute def Temp :> Therm|", D::Attribute),
            ("port def P2 specializes Fu|", D::Port),
            ("action def A2 :> D|", D::Action),
            ("abstract part def T :> V, |", D::Part),
        ] {
            let Some(Names::Types { exact: e, .. }) = want(marked).names else {
                panic!("{marked:?}");
            };
            assert_eq!(e, vec![exact], "{marked:?}");
        }
        let Some(Names::Types { exact, .. }) =
            want_in(Dialect::Kerml, "classifier C specializes B|").names
        else {
            panic!("classifier");
        };
        assert_eq!(exact, vec![D::Classifier]);
        let parts = vec![
            U::Part,
            U::Connection,
            U::Interface,
            U::Allocation,
            U::View,
            U::Rendering,
        ];
        let items = [&[U::Item, U::Metadata][..], &parts[..]].concat();
        for (marked, preferred) in [
            ("part frontWheels : Wheel [2] :> wh|", parts.clone()),
            ("attribute :>> |", vec![U::Attribute, U::Enum]),
            ("attribute redefines ma|", vec![U::Attribute, U::Enum]),
            ("part :>> e|", parts.clone()),
            ("individual item :>> |", items.clone()),
            (
                "message :>> |",
                vec![U::Flow, U::Message, U::SuccessionFlow],
            ),
            (":>> co|", vec![]),
            ("ref r subsets |", vec![]),
            ("ref :>> st|", vec![]),
            ("ref part p :>> |", parts),
        ] {
            let Some(Names::Features { preferred: p, .. }) = want(marked).names else {
                panic!("{marked:?}");
            };
            assert_eq!(p, preferred, "{marked:?}");
        }
        // The kinds specializing the statement's own rank after it: a
        // part after an item, a succession flow after a message, which
        // is a flow.
        for (marked, specific, kind) in [
            ("individual item :>> |", &items[1..], U::Metadata),
            ("message :>> |", &[U::SuccessionFlow][..], U::SuccessionFlow),
            ("attribute :>> |", &[U::Enum], U::Enum),
        ] {
            let w = want(marked);
            let Some(Names::Features { specific: s, .. }) = &w.names else {
                panic!("{marked:?}");
            };
            assert_eq!(s, specific, "{marked:?}");
            assert_eq!(w.tier(Decl::Usage(kind)), 1, "{marked:?}");
        }
        assert_eq!(want("item :> |").tier(Decl::Usage(U::Item)), 0);
        // An individual, a snapshot, or a time slice naming no kind of its
        // own: every occurrence alike.
        assert_eq!(want("snapshot s :> |").tier(Decl::Usage(U::Part)), 0);
        assert_eq!(want("individual :>> |").tier(Decl::Usage(U::Action)), 0);
        assert_eq!(
            want("snapshot part s :> |").tier(Decl::Usage(U::Connection)),
            1
        );
        assert_eq!(want("occurrence :>> |").tier(Decl::Usage(U::Part)), 1);
        // A compound keyword declares the more specific kind it spells,
        // ranked ahead of the other kinds its kind word takes; a bare
        // `perform` names none.
        for (marked, declared, word) in [
            ("perform action :>> |", U::Perform, U::Action),
            ("exhibit state :>> |", U::Exhibit, U::State),
            ("include use case u :>> |", U::Include, U::UseCase),
            ("satisfy requirement :>> |", U::Satisfy, U::Requirement),
            (
                "assert not constraint :>> |",
                U::AssertConstraint,
                U::Constraint,
            ),
            ("event occurrence :>> |", U::Event, U::Occurrence),
        ] {
            let w = want(marked);
            assert_eq!(w.tier(Decl::Usage(declared)), 0, "{marked:?}");
            assert_eq!(w.tier(Decl::Usage(word)), 1, "{marked:?}");
            assert_eq!(w.group(Decl::Usage(word), true), Some(1), "{marked:?}");
        }
        // A subsetting or a reference ranks its kind word's own first.
        for (marked, declared, word) in [
            ("include use case u :> |", U::Include, U::UseCase),
            ("perform action p ::> |", U::Perform, U::Action),
        ] {
            let w = want(marked);
            assert_eq!(w.tier(Decl::Usage(word)), 0, "{marked:?}");
            assert_eq!(w.tier(Decl::Usage(declared)), 1, "{marked:?}");
        }
        let Some(Names::Features { preferred, .. }) = want("perform :>> |").names else {
            panic!("perform");
        };
        assert!(preferred.is_empty(), "{preferred:?}");
        assert_eq!(want("ref :>> |").tier(Decl::Usage(U::Part)), 0);
        assert_eq!(want("perform |").tier(Decl::Usage(U::State)), 0);
        let Some(Names::Features { preferred, .. }) =
            want_in(Dialect::Kerml, "feature f subsets |").names
        else {
            panic!("feature");
        };
        assert_eq!(preferred, vec![]);
    }

    /// After `=`, `:=`, an operator, `(`, or a condition keyword:
    /// operands and the keywords that start an expression, `true` and
    /// `false` first where the statement declares a `Boolean`; after an
    /// operand, only the keyword operators.
    #[test]
    fn expression_positions() {
        use super::{FIRST, Names, WITH_WORKSPACE};
        for marked in [
            "attribute w = |",
            "attribute w = mass * |",
            "attribute ke = KineticEnergy(|",
            "attribute ke = KineticEnergy(m, |",
            "assign level := |",
            "if lev|",
            "attribute ok = a and |",
            "for i in |",
        ] {
            let w = want(marked);
            assert!(
                matches!(w.names, Some(Names::Operands { .. })),
                "{marked:?}"
            );
            assert!(w.keywords.contains(&("true", WITH_WORKSPACE)), "{marked:?}");
        }
        let w = want("attribute b : Boolean = t|");
        assert!(w.keywords.contains(&("true", FIRST)) && w.keywords.contains(&("false", FIRST)));
        assert!(w.keywords.contains(&("null", WITH_WORKSPACE)));
        let w = want("attribute b : ScalarValues::Boolean = |");
        assert!(w.keywords.contains(&("true", FIRST)));
        for marked in [
            "attribute w = mass |",
            "attribute w = f(x) |",
            "attribute w = 5 [kg] |",
            "constraint def C {\n    mass <= limit |",
            "state def S {\n    attribute w = if c ? 1 else 2 |",
        ] {
            let w = want(marked);
            assert_eq!(w.names, None, "{marked:?}");
            assert!(keywords(&w).contains(&"and"), "{marked:?}");
            assert!(!keywords(&w).contains(&"then"), "{marked:?}");
        }
        // Where the grammar goes on with `then`: after an action's `if`
        // condition, and after a transition's trigger.
        for marked in [
            "action def A {\n    if level > 0 |",
            "state def S {\n    transition first off accept after 5 [s] |",
            "state def S {\n    accept after 5 [s] |",
            "state def S {\n    transition first off if x > 0 |",
            "state def S {\n    if x > 0 |",
            "action def A {\n    first a1 if x > 0 |",
            "action def A {\n    accept after 5 [s] |",
            "action def A {\n    accept at t0 |",
            "action def A {\n    accept when ready |",
        ] {
            let w = want(marked);
            assert!(keywords(&w).contains(&"then"), "{marked:?}");
            assert!(keywords(&w).contains(&"and"), "{marked:?}");
        }
        // After an accept's payload type no operator follows: `then`, the
        // port it arrives through, and a transition's guard and effect.
        for (marked, expected) in [
            ("action def A {\n    accept Sig |", &["then", "via"][..]),
            ("action def A {\n    accept sig : Sig |", &["then", "via"]),
            (
                "state def S {\n    accept Sig |",
                &["then", "via", "if", "do"],
            ),
            (
                "state def S {\n    transition first off accept Sig |",
                &["then", "via", "if", "do"],
            ),
            ("state def S {\n    accept Sig do a |", &["then"]),
        ] {
            assert_eq!(keywords(&want(marked)), expected, "{marked:?}");
        }
        // Past a declaration's name, outside an expression, or inside a
        // bracket the statement leaves open: unclassified.
        for marked in [
            "part def Car |",
            "attribute mass |",
            "attribute g = 9.8 [metre per|",
            "attribute g = 9.8 [m / |",
            "part w : Wheel [|",
        ] {
            assert_eq!(slot(marked), Slot::Open, "{marked:?}");
        }
    }

    /// Which positions name the enclosing element's features besides
    /// the symbol tables': its inherited ones at a redefinition, its own
    /// and inherited ones at a succession or a subsetting.
    #[test]
    fn positions_name_the_enclosing_members() {
        use super::Members;
        for (marked, members) in [
            ("attribute :>> |", Members::Inherited),
            ("attribute :>> m|", Members::Inherited),
            (":>> co|", Members::Inherited),
            ("part :>> e|", Members::Inherited),
            ("attribute redefines ma|", Members::Inherited),
            ("attribute :>> a, |", Members::Inherited),
            ("@Safety {\n    |", Members::Inherited),
            ("@Safety {\n    ref c|", Members::Inherited),
            ("first st|", Members::Scope),
            ("then |", Members::Scope),
            ("part fw : Wheel [2] :> wh|", Members::Scope),
            ("part fw subsets wh|", Members::Scope),
            ("part def Sedan :> C|", Members::None),
            ("part p : |", Members::None),
            ("attribute w = |", Members::None),
            ("perform |", Members::None),
        ] {
            assert_eq!(want(marked).members(), members, "{marked:?}");
        }
    }

    /// An expression position knows the type its statement declares,
    /// and ranks measurement units after every other name — or first
    /// where that type is a unit type.
    #[test]
    fn units_rank_by_the_declared_type() {
        use super::{Names, UNITS};
        let unit_types: std::collections::HashSet<String> =
            ["ForceUnit", "MeasurementUnit"].map(String::from).into();
        for (marked, typed, group) in [
            ("attribute <N> newton : ForceUnit = |", Some("ForceUnit"), 0),
            (
                "attribute f : ISQ::ForceUnit = kg * |",
                Some("ForceUnit"),
                0,
            ),
            ("attribute m : MassValue = |", Some("MassValue"), UNITS),
            ("attribute w = |", None, UNITS),
        ] {
            let w = want(marked);
            let Some(Names::Operands { typed: t }) = &w.names else {
                panic!("{marked:?}: {:?}", w.names);
            };
            assert_eq!(t.as_deref(), typed, "{marked:?}");
            assert_eq!(w.unit_group(&unit_types), Some(group), "{marked:?}");
        }
        // Units rank by kind alone elsewhere.
        assert_eq!(want("part p : |").unit_group(&unit_types), None);
    }

    /// After a keyword that references an element of a kind: that kind
    /// of name, with the keyword declaring one instead ranked first.
    #[test]
    fn reference_keywords() {
        use super::{AFTER, FIRST, Names};
        use sysmlv2_parser::ast::UsageKind as U;
        for (marked, kind, keyword) in [
            ("perform |", U::Perform, "action"),
            ("exhibit st|", U::Exhibit, "state"),
            ("include |", U::Include, "use"),
            ("satisfy Max|", U::Satisfy, "requirement"),
            ("verify |", U::Requirement, "requirement"),
            ("frame |", U::Concern, "concern"),
            ("assert |", U::AssertConstraint, "constraint"),
            ("require |", U::Constraint, "constraint"),
            ("entry |", U::Action, "action"),
            ("render |", U::Rendering, "rendering"),
        ] {
            let w = want(marked);
            let Some(Names::Features { preferred, .. }) = &w.names else {
                panic!("{marked:?}: {:?}", w.names);
            };
            assert!(preferred.contains(&kind), "{marked:?}: {preferred:?}");
            assert!(w.keywords.contains(&(keyword, FIRST)), "{marked:?}");
        }
        // A successor is named more often than declared.
        let w = want("then a|");
        assert!(matches!(w.names, Some(Names::Features { .. })));
        assert!(w.keywords.contains(&("action", AFTER)));
        for marked in ["#Saf|", "@Saf|", "metadata Saf|"] {
            let Some(Names::Types { exact, .. }) = want(marked).names else {
                panic!("{marked:?}");
            };
            assert!(exact.contains(&sysmlv2_parser::ast::DefKind::Metadata));
        }
        for marked in [
            "alias A for B|",
            "expose |",
            "comment about |",
            "dependency d from a to |",
        ] {
            assert_eq!(want(marked).names, Some(Names::All), "{marked:?}");
        }
        for (marked, only) in [
            ("part p defined |", "by"),
            ("use |", "case"),
            ("standard |", "library"),
            ("library |", "package"),
        ] {
            let w = want(marked);
            assert_eq!(keywords(&w), vec![only], "{marked:?}");
            assert_eq!(w.names, None, "{marked:?}");
        }
        for marked in ["new Sig|", "x as |", "accept Sig|"] {
            assert!(
                matches!(want(marked).names, Some(Names::Types { .. })),
                "{marked:?}"
            );
        }
        for marked in [
            "connect a to |",
            "bind a = |",
            "connect (a, |",
            "satisfy R by v|",
        ] {
            assert!(
                matches!(want(marked).names, Some(Names::Features { .. })),
                "{marked:?}"
            );
        }
    }

    /// A statement's first word: the keywords its body takes — and
    /// names only where the body ends in a result expression.
    #[test]
    fn statement_starts_take_their_bodys_keywords() {
        use super::{FIRST, Names};
        for (marked, has, lacks) in [
            (
                "package P {\n    |",
                &["package", "part", "filter", "import"][..],
                &["entry", "fork", "and"][..],
            ),
            (
                "part def P {\n    |",
                &["part", "attribute", "then", "private"],
                &["entry", "fork", "filter"],
            ),
            (
                "action def A {\n    |",
                &["fork", "for", "merge", "first", "then"],
                &["entry", "subject"],
            ),
            (
                "state def S {\n    ent|",
                &["entry", "exit", "do", "transition"],
                &["fork"],
            ),
            (
                "requirement def R {\n    |",
                &["subject", "require", "assume", "frame"],
                &["fork", "entry"],
            ),
            (
                "view def V {\n    |",
                &["expose", "render", "filter"],
                &["entry"],
            ),
            (
                "package P {\n    private |",
                &["import", "part"],
                &["private", "public"],
            ),
            ("|", &["package", "part"], &["fork"]),
        ] {
            let w = want(marked);
            assert_eq!(w.names, None, "{marked:?}");
            let kws = keywords(&w);
            for k in has {
                assert!(kws.contains(k), "{marked:?}: {k}");
            }
            for k in lacks {
                assert!(!kws.contains(k), "{marked:?}: {k}");
            }
            assert!(
                w.keywords.iter().all(|&(_, key)| key == FIRST),
                "{marked:?}"
            );
        }
        // Bodies ending in a result expression also take operands.
        for marked in [
            "constraint def C {\n    |",
            "calc def K {\n    |",
            "part def P {\n    assert constraint {\n        |",
            "use case def U {\n    |",
        ] {
            let w = want(marked);
            assert!(
                matches!(w.names, Some(Names::Operands { .. })),
                "{marked:?}"
            );
            let kws = keywords(&w);
            assert!(
                kws.contains(&"return") && kws.contains(&"true"),
                "{marked:?}"
            );
        }
        assert!(keywords(&want("use case def U {\n    |")).contains(&"objective"));
        // A metadata body redefines features by name.
        assert!(matches!(
            want("@Safety {\n    |").names,
            Some(Names::Features { .. })
        ));
        // KerML bodies take KerML's words.
        let w = want_in(Dialect::Kerml, "package P {\n    |");
        let kws = keywords(&w);
        assert!(kws.contains(&"class") && kws.contains(&"feature") && !kws.contains(&"part"));
        let w = want_in(Dialect::Kerml, "function F {\n    |");
        assert!(matches!(w.names, Some(Names::Operands { .. })));
        assert!(keywords(&w).contains(&"return"));
    }

    /// The keywords offered are the document's dialect's.
    #[test]
    fn keywords_are_the_dialects() {
        let sysml = keywords(&want("part def P {\n    cons|"));
        assert!(sysml.contains(&"constant") && sysml.contains(&"constraint"));
        assert!(!sysml.contains(&"const"));
        let kerml = keywords(&want_in(Dialect::Kerml, "package P {\n    cla|"));
        assert!(kerml.contains(&"class") && !kerml.contains(&"part") && !kerml.contains(&"calc"));
    }
}
