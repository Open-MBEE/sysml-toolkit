//! Hand-written recursive-descent parser for the SysML v2 and KerML textual
//! notations.
//!
//! Follows the normative grammars (`spec-refs/SysML.xtext`,
//! `spec-refs/KerML.xtext`, `spec-refs/KerMLExpressions.xtext`). Keywords are
//! matched contextually against `Ident` tokens; per-dialect reserved-word
//! sets prevent keywords from being taken as names (per Xtext keyword
//! reservation) while leaving the other dialect's keywords usable as
//! ordinary names.
//!
//! Coverage is complete for both dialects: the entire official corpus (345
//! files — standard library, training, examples, validation suites) parses
//! without diagnostics; `tests/corpus.rs` enforces this. Bodies parse a
//! *superset* across contexts (e.g. state members are not rejected inside
//! plain part bodies) — context validation belongs to a later semantic
//! layer, not the parser.

use crate::ast::*;
use crate::diag::Diagnostic;
use crate::lexer::{tokenize, unescape};
use crate::span::Span;
use crate::token::{Token, TokenKind};

/// Result of parsing one source unit. `unit` is always produced; check
/// `diagnostics` for errors (the tree may be partial after recovery).
#[derive(Debug)]
pub struct Parse {
    pub unit: SourceUnit,
    pub diagnostics: Vec<Diagnostic>,
}

impl Parse {
    #[must_use]
    pub fn has_errors(&self) -> bool {
        !self.diagnostics.is_empty()
    }
}

/// Parse a `.sysml` source text (root namespace, SysML dialect).
#[must_use]
pub fn parse_source(src: &str) -> Parse {
    parse_dialect(src, Dialect::Sysml)
}

/// Parse a `.kerml` source text (root namespace, KerML dialect).
#[must_use]
pub fn parse_kerml_source(src: &str) -> Parse {
    parse_dialect(src, Dialect::Kerml)
}

/// Result of parsing one standalone expression (see [`parse_expression`]).
/// `expr` is `None` when the text is not an expression; `diagnostics`
/// carries the errors either way (the tree may be partial).
#[derive(Debug)]
pub struct ExprParse {
    pub expr: Option<Expr>,
    pub diagnostics: Vec<Diagnostic>,
}

/// Parse a standalone KerML expression (KerMLExpressions.xtext
/// `OwnedExpression`) — an ad-hoc query or constraint given outside a
/// model file. The whole text must form one expression; trailing input is
/// an error. Expressions are shared between the dialects; the SysML
/// reserved-word set applies, so reserved names need quoting (`'part'`
/// stays a plain name in KerML but must be quoted here).
#[must_use]
pub fn parse_expression(src: &str) -> ExprParse {
    let (mut tokens, mut diags) = tokenize(src);
    tokens.retain(|t| !t.kind.is_trivia());
    let mut p = Parser {
        src,
        tokens,
        pos: 0,
        dialect: Dialect::Sysml,
        diags: Vec::new(),
        meta_body: false,
        enum_body: false,
        semi_repair: SemiRepair::Off,
        depth: 0,
        expr_frames: 0,
        expr_chain: 0,
    };
    let expr = p.parse_expr();
    if expr.is_some() && !p.at_eof() {
        p.error_here(format!(
            "expected end of input after the expression, found `{}`",
            p.describe_cur()
        ));
    }
    diags.append(&mut p.diags);
    let clean = !diags
        .iter()
        .any(|d| d.severity == crate::diag::Severity::Error);
    ExprParse {
        expr: expr.filter(|_| clean),
        diagnostics: diags,
    }
}

fn parse_dialect(src: &str, dialect: Dialect) -> Parse {
    parse_keeping_notes(src, dialect, None)
}

/// Parse and hand back the note tokens in source order, from the one
/// tokenization the parse already does. The formatter needs the notes the
/// parser drops as trivia, and re-lexing the file to recover them doubles
/// the lexical work.
pub(crate) fn parse_with_notes(src: &str, dialect: Dialect) -> (Parse, Vec<(Span, String)>) {
    let mut notes = Vec::new();
    let parse = parse_keeping_notes(src, dialect, Some(&mut notes));
    (parse, notes)
}

fn parse_keeping_notes(
    src: &str,
    dialect: Dialect,
    notes: Option<&mut Vec<(Span, String)>>,
) -> Parse {
    let (mut tokens, mut diags) = tokenize(src);
    if let Some(notes) = notes {
        notes.extend(
            tokens
                .iter()
                .filter(|t| matches!(t.kind, TokenKind::LineNote | TokenKind::BlockNote))
                .map(|t| (t.span, t.text(src).trim_end().to_string())),
        );
    }
    tokens.retain(|t| !t.kind.is_trivia());
    let mut p = Parser {
        src,
        tokens,
        pos: 0,
        dialect,
        diags: Vec::new(),
        meta_body: false,
        enum_body: false,
        semi_repair: SemiRepair::Off,
        depth: 0,
        expr_frames: 0,
        expr_chain: 0,
    };
    let unit = p.parse_root();
    diags.append(&mut p.diags);
    Parse {
        unit,
        diagnostics: diags,
    }
}

/// How deeply bodies and expressions may nest before the parser reports
/// that the input is too deeply nested and stops descending.
///
/// Nesting is bounded because descending is recursive and running out of
/// stack ends the process outright instead of producing a diagnostic. The
/// number is above every depth the toolkit supports downstream — a name is
/// resolved through at most sixty-four owners, and the published example
/// and library models nest ten levels of braces — so it turns unbounded
/// input into a diagnostic without standing in the way of a real model.
///
/// The bound assumes a stack it fits inside: [`MAX_NESTING_STACK_BYTES`].
pub const MAX_NESTING: u32 = 128;

/// The stack a thread needs to parse input nested to [`MAX_NESTING`].
///
/// A bound on the descent only turns unbounded input into a diagnostic
/// where the stack reaches the bound. On a smaller one the process ends
/// at some shallower depth the parser accepts — a stack overflow, which
/// is an abort, not a diagnostic and not even an unwind — so a thread
/// that parses has to hold the whole of what the parser admits.
///
/// Measured over the deepest input the bound admits: bodies nested to
/// the bound cost the most, and which body is dearest shows only
/// unoptimized — a flow's costs about ten and a half megabytes there,
/// against about nine and three quarters for the part bodies the probes
/// nest, while optimized both come in just under four. Nesting that
/// carries a full operator chain at its deepest level costs a little
/// less again. This is sized above the largest unoptimized figure, so
/// it holds in either build.
///
/// A thread that does not ask for a stack gets two megabytes, which
/// holds about seventy of the levels an optimized build admits and
/// about two dozen unoptimized; [`on_parsing_stack`] is how a thread
/// asks for this instead. Reserved address space only — pages are
/// committed as the recursion touches them.
pub const MAX_NESTING_STACK_BYTES: usize = 16 << 20;

/// Run `work` on a thread holding [`MAX_NESTING_STACK_BYTES`], named
/// `name`.
///
/// The nesting bound only turns unbounded input into a diagnostic on a
/// stack that reaches the bound, and a thread that asks for no stack
/// does not have one. Every entry point of this workspace that parses
/// runs its work through here — the command line and the language
/// server's loop — and the server's workspace worker reserves the same
/// size on the thread it spawns.
///
/// An embedder's thread is not one of those: a library call parses on
/// whichever thread makes it. One that may be handed deeply nested
/// input can call this, or reserve the same size on a thread of its
/// own.
///
/// Where no thread can be had — a target without them, a host that
/// refuses one — `work` runs on the calling thread, which then reaches
/// only as deep as that stack allows: input the bound admits can run the
/// descent out of stack, and that ends the process outright, with no
/// diagnostic and no unwind. A host that refused the thread is told so
/// through `refused`, which is handed what the system said and reports it
/// the way the caller's channel allows, before `work` runs. A target
/// without threads is not a refusal and does not reach it.
pub fn on_parsing_stack<T, F>(name: &str, refused: impl FnOnce(&std::io::Error), work: F) -> T
where
    F: FnOnce() -> T + Send,
    T: Send,
{
    // The work is handed to the thread, so it cannot simply be called
    // again where the thread never starts: the thread takes it from
    // here, and it is still here when nothing took it.
    let mut work = Some(work);
    #[cfg(not(target_family = "wasm"))]
    {
        let spawned = std::thread::scope(|scope| {
            let slot = &mut work;
            std::thread::Builder::new()
                .name(name.to_string())
                .stack_size(MAX_NESTING_STACK_BYTES)
                .spawn_scoped(scope, move || {
                    (slot.take().expect("the work is taken once"))()
                })
                .map(std::thread::ScopedJoinHandle::join)
        });
        match spawned {
            Ok(Ok(value)) => return value,
            Ok(Err(panic)) => std::panic::resume_unwind(panic),
            // No thread to be had: nothing took the work, so it runs
            // here — on a stack that was not reserved, which is what the
            // caller is told before the work starts.
            Err(err) => refused(&err),
        }
    }
    #[cfg(target_family = "wasm")]
    let _ = (name, refused);
    work.take().expect("no thread took the work")()
}

/// The most operators one leaning chain of an expression may spell.
///
/// Operators at one precedence level, feature-chain steps, indexes and
/// `->` applications are all built iteratively, so no descent is charged
/// for them — but the tree each builds leans one node deep per operator,
/// and *walking* that tree recurses: dropping it, printing it, checking
/// it, emitting it. An unbounded chain therefore exhausts the stack
/// outside the parser, where there is no diagnostic to report.
///
/// The budget measures the longest chain of operators leaning on one
/// another, not the number of nodes in the expression: a branch hanging
/// off the chain — an operand on the right, one item of a sequence, one
/// argument of an invocation, one member of a body — spells a chain of
/// its own, and what an operator leans on is the longer of the two. So a
/// thousand short operands cost what one of them costs, while a thousand
/// operators stacked on one another are refused however they are spelled.
/// The bound is far above the chain any written expression spells and far
/// below the depth those walks can hold on the smallest stack the toolkit
/// ships against.
pub const MAX_EXPR_OPERATORS: u32 = 1024;

thread_local! {
    static ACCEPT_LOOKAHEAD_TOKENS: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
}

/// Tokens the accept-member lookahead has read on this thread since this
/// was last called, and reset the count to zero.
///
/// Classifying a member that begins with `accept` needs a look ahead for
/// the transition shorthand's `then`. The scan is meant to stop within
/// the member it classifies, whether or not that member is well formed;
/// this reports what it actually read, so the cost can be pinned without
/// timing the machine it runs on.
pub fn take_accept_lookahead_tokens() -> u64 {
    ACCEPT_LOOKAHEAD_TOKENS.with(|n| n.replace(0))
}

/// Words reserved by the SysML dialect (SysML.xtext ∪ KerMLExpressions.xtext).
/// Must stay sorted: looked up by binary search.
const RESERVED: &[&str] = &[
    "about",
    "abstract",
    "accept",
    "action",
    "actor",
    "after",
    "alias",
    "all",
    "allocate",
    "allocation",
    "analysis",
    "and",
    "as",
    "assert",
    "assign",
    "assume",
    "at",
    "attribute",
    "bind",
    "binding",
    "by",
    "calc",
    "case",
    "comment",
    "concern",
    "connect",
    "connection",
    "constant",
    "constraint",
    "crosses",
    "decide",
    "def",
    "default",
    "defined",
    "dependency",
    "derived",
    "do",
    "doc",
    "else",
    "end",
    "entry",
    "enum",
    "event",
    "exhibit",
    "exit",
    "expose",
    "false",
    "filter",
    "first",
    "flow",
    "for",
    "fork",
    "frame",
    "from",
    "hastype",
    "if",
    "implies",
    "import",
    "in",
    "include",
    "individual",
    "inout",
    "interface",
    "istype",
    "item",
    "join",
    "language",
    "library",
    "locale",
    "loop",
    "merge",
    "message",
    "meta",
    "metadata",
    "new",
    "nonunique",
    "not",
    "null",
    "objective",
    "occurrence",
    "of",
    "or",
    "ordered",
    "out",
    "package",
    "parallel",
    "part",
    "perform",
    "port",
    "private",
    "protected",
    "public",
    "redefines",
    "ref",
    "references",
    "render",
    "rendering",
    "rep",
    "require",
    "requirement",
    "return",
    "satisfy",
    "send",
    "snapshot",
    "specializes",
    "stakeholder",
    "standard",
    "state",
    "subject",
    "subsets",
    "succession",
    "terminate",
    "then",
    "timeslice",
    "to",
    "transition",
    "true",
    "until",
    "use",
    "variant",
    "variation",
    "verification",
    "verify",
    "via",
    "view",
    "viewpoint",
    "when",
    "while",
    "xor",
];

/// Words reserved by the KerML dialect (KerML.xtext ∪ KerMLExpressions.xtext).
/// Must stay sorted: looked up by binary search.
const KERML_RESERVED: &[&str] = &[
    "about",
    "abstract",
    "alias",
    "all",
    "and",
    "as",
    "assoc",
    "behavior",
    "binding",
    "bool",
    "by",
    "chains",
    "class",
    "classifier",
    "comment",
    "composite",
    "conjugate",
    "conjugates",
    "conjugation",
    "connector",
    "const",
    "crosses",
    "datatype",
    "default",
    "dependency",
    "derived",
    "differences",
    "disjoining",
    "disjoint",
    "doc",
    "else",
    "end",
    "expr",
    "false",
    "feature",
    "featured",
    "featuring",
    "filter",
    "first",
    "flow",
    "for",
    "from",
    "function",
    "hastype",
    "if",
    "implies",
    "import",
    "in",
    "inout",
    "interaction",
    "intersects",
    "inv",
    "inverse",
    "inverting",
    "istype",
    "language",
    "library",
    "locale",
    "member",
    "meta",
    "metaclass",
    "metadata",
    "multiplicity",
    "namespace",
    "new",
    "nonunique",
    "not",
    "null",
    "of",
    "or",
    "ordered",
    "out",
    "package",
    "portion",
    "predicate",
    "private",
    "protected",
    "public",
    "redefines",
    "redefinition",
    "references",
    "rep",
    "return",
    "specialization",
    "specializes",
    "standard",
    "step",
    "struct",
    "subclassifier",
    "subset",
    "subsets",
    "subtype",
    "succession",
    "then",
    "to",
    "true",
    "type",
    "typed",
    "typing",
    "unions",
    "var",
    "xor",
];

/// State of the missing-`;` repair (see [`Parser::repair_missing_semi`]).
#[derive(Clone, Copy, PartialEq, Eq)]
enum SemiRepair {
    Off,
    /// A `;`-or-`{` expectation failed at a `}` in repair shape, but the
    /// trailing-result-expression form has priority there; the member
    /// loop may re-parse with the repair armed once that form fails.
    Eligible,
    /// Re-parse pass: apply the repair even at a `}`.
    Armed,
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum PayloadContext {
    Flow,
    Accept,
}

struct Parser<'s> {
    src: &'s str,
    tokens: Vec<Token>,
    pos: usize,
    dialect: Dialect,
    diags: Vec<Diagnostic>,
    /// Inside a `MetadataBody`: a keyword-less member's leading qualified
    /// name is an implicit redefinition target (`@M { M::kind = 1; }` ≡
    /// `@M { :>> M::kind = 1; }`), never a declared name.
    meta_body: bool,
    /// Inside an enumeration body, where an `EnumeratedValue` may reduce to
    /// an entirely empty usage followed by its terminating semicolon.
    enum_body: bool,
    semi_repair: SemiRepair,
    /// How many bodies and expressions are open above the current one.
    /// Both recurse, so both count against the same budget.
    depth: u32,
    /// How many expression frames are open above the current one. Zero at
    /// the start of a member's outermost expression, which is where the
    /// chain budget below is refilled.
    expr_frames: u32,
    /// How deep the expression completed at this position leans — the
    /// longest chain of operators in it (see [`MAX_EXPR_OPERATORS`]).
    expr_chain: u32,
}

/// Is `word` reserved in `dialect` (and thus unusable as a bare name)?
#[must_use]
pub fn is_reserved(dialect: Dialect, word: &str) -> bool {
    let table = match dialect {
        Dialect::Sysml => RESERVED,
        Dialect::Kerml => KERML_RESERVED,
    };
    table.binary_search(&word).is_ok()
}

impl<'s> Parser<'s> {
    // ---- cursor primitives ----

    fn is_reserved_word(&self, word: &str) -> bool {
        is_reserved(self.dialect, word)
    }

    fn cur(&self) -> Token {
        self.tokens[self.pos.min(self.tokens.len() - 1)]
    }

    fn nth(&self, n: usize) -> Token {
        self.tokens[(self.pos + n).min(self.tokens.len() - 1)]
    }

    fn cur_text(&self) -> &'s str {
        self.cur().text(self.src)
    }

    fn at(&self, kind: TokenKind) -> bool {
        self.cur().kind == kind
    }

    fn at_kw(&self, kw: &str) -> bool {
        self.cur().is_kw(self.src, kw)
    }

    fn nth_kw(&self, n: usize, kw: &str) -> bool {
        self.nth(n).is_kw(self.src, kw)
    }

    fn at_eof(&self) -> bool {
        self.at(TokenKind::Eof)
    }

    fn bump(&mut self) -> Token {
        let t = self.cur();
        if self.pos < self.tokens.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn eat(&mut self, kind: TokenKind) -> bool {
        if self.at(kind) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.at_kw(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn expect(&mut self, kind: TokenKind, what: &str) -> Option<Token> {
        if self.at(kind) {
            Some(self.bump())
        } else {
            self.error_here(format!("expected {what}, found `{}`", self.describe_cur()));
            None
        }
    }

    fn expect_kw(&mut self, kw: &str) -> bool {
        if self.eat_kw(kw) {
            true
        } else {
            self.error_here(format!("expected `{kw}`, found `{}`", self.describe_cur()));
            false
        }
    }

    fn describe_cur(&self) -> String {
        if self.at_eof() {
            return "end of input".to_string();
        }
        // Echo at most one line of the offending token: a runaway token
        // (an unterminated string swallowing the rest of the file) must
        // not be reproduced verbatim in the message.
        let text = self.cur_text();
        let line = text.lines().next().unwrap_or("");
        let mut out: String = line.chars().take(40).collect();
        if out.len() < text.len() {
            out.push('…');
        }
        out
    }

    fn error_here(&mut self, message: String) {
        // A lexer `Error` token was already diagnosed at its source
        // (unterminated literal, invalid escape, stray character) — a
        // second "expected …, found …" at the same token is cascade noise.
        if !self.at_eof() && self.cur().kind == TokenKind::Error {
            return;
        }
        self.diags.push(Diagnostic::error(self.cur().span, message));
    }

    /// Skip tokens until a likely member boundary: past a `;`, or before a
    /// `}` at the current nesting level. Keeps brace/bracket/paren balance.
    fn recover(&mut self) {
        let mut depth = 0i32;
        while !self.at_eof() {
            match self.cur().kind {
                TokenKind::Semi if depth == 0 => {
                    self.bump();
                    return;
                }
                TokenKind::LBrace | TokenKind::LBracket | TokenKind::LParen => depth += 1,
                TokenKind::RBrace | TokenKind::RBracket | TokenKind::RParen => {
                    if depth == 0 {
                        return;
                    }
                    depth -= 1;
                }
                _ => {}
            }
            self.bump();
        }
    }

    /// Is there a line break in the source between the end of the previous
    /// token and the start of the current one? This is the
    /// missing-terminator signature: the construct's last token ends one
    /// line and the unexpected token starts a later one.
    fn cur_starts_new_line(&self) -> bool {
        let from = self.prev_end_span().end as usize;
        let to = self.cur().span.start as usize;
        from <= to && self.src[from..to].contains('\n')
    }

    /// Could the current token begin a member? Gates the missing-`;`
    /// repair: pretending the terminator was present is only sound where
    /// parsing can resume cleanly, and an expression-continuation token
    /// (an operator, `(`, …) means the line break was mid-construct.
    /// The keyword connectives lex as plain identifiers but continue an
    /// expression too — an operator-leading continuation line
    /// (`… \n and more`) must fall through to the result-expression
    /// interpretation, not repair into a phantom member boundary.
    fn at_member_start_token(&self) -> bool {
        if self.cur().kind == TokenKind::Ident
            && matches!(self.cur_text(), "and" | "or" | "xor" | "implies")
        {
            return false;
        }
        matches!(
            self.cur().kind,
            TokenKind::Ident
                | TokenKind::RegularComment
                | TokenKind::At
                | TokenKind::Hash
                | TokenKind::RBrace
                | TokenKind::Eof
        )
    }

    /// The expected `;` terminator is absent. If the current token starts
    /// a later line and could begin a member, report the `;` missing at
    /// the end of the previous line (a zero-width span at the insertion
    /// point) and continue as if it were present. Returns whether that
    /// repair applied; the caller falls back to its usual "expected …,
    /// found …" diagnostic otherwise.
    fn repair_missing_semi(&mut self, what: &str) -> bool {
        if !self.cur_starts_new_line() || !self.at_member_start_token() {
            return false;
        }
        let at = self.prev_end_span().end;
        self.diags.push(Diagnostic::error(
            Span::new(at, at),
            format!("missing `;` {what}"),
        ));
        self.semi_repair = SemiRepair::Off;
        true
    }

    /// A required `;` member terminator, with missing-terminator repair.
    /// `what` continues both messages: "expected `;` {what}" /
    /// "missing `;` {what}".
    fn expect_semi(&mut self, what: &str) {
        if self.eat(TokenKind::Semi) || self.repair_missing_semi(what) {
            return;
        }
        self.error_here(format!(
            "expected `;` {what}, found `{}`",
            self.describe_cur()
        ));
    }

    // ---- names ----

    fn at_name(&self) -> bool {
        match self.cur().kind {
            TokenKind::UnrestrictedName => true,
            TokenKind::Ident => !self.is_reserved_word(self.cur_text()),
            _ => false,
        }
    }

    fn parse_name(&mut self) -> Option<Name> {
        if !self.at_name() {
            self.error_here(format!("expected a name, found `{}`", self.describe_cur()));
            return None;
        }
        let tok = self.bump();
        let value = match tok.kind {
            TokenKind::UnrestrictedName => unescape(tok.text(self.src)),
            _ => tok.text(self.src).to_string(),
        };
        Some(Name {
            value,
            span: tok.span,
        })
    }

    /// `($::)? Name (:: Name)*` — stops before `::*` / `::**`.
    fn parse_qualified_name(&mut self) -> Option<QualifiedName> {
        let start = self.cur().span;
        let is_global = if self.at(TokenKind::Dollar) {
            self.bump();
            self.expect(TokenKind::ColonColon, "`::` after `$`");
            true
        } else {
            false
        };
        let mut segments = vec![self.parse_name()?];
        while self.at(TokenKind::ColonColon)
            && matches!(
                self.nth(1).kind,
                TokenKind::Ident | TokenKind::UnrestrictedName
            )
            && (self.nth(1).kind == TokenKind::UnrestrictedName
                || !self.is_reserved_word(self.nth(1).text(self.src)))
        {
            self.bump(); // ::
            segments.push(self.parse_name()?);
        }
        let span = start.join(segments.last().unwrap().span);
        Some(QualifiedName {
            is_global,
            segments,
            span,
        })
    }

    /// True if `nth(n)` can start a name (non-reserved ident or `'...'`).
    fn nth_is_name(&self, n: usize) -> bool {
        let t = self.nth(n);
        match t.kind {
            TokenKind::UnrestrictedName => true,
            TokenKind::Ident => !self.is_reserved_word(t.text(self.src)),
            _ => false,
        }
    }

    /// Qualified name or feature chain `a.b.c` (each link a qualified name).
    /// A `.` is only taken when a name follows, so expression suffixes such
    /// as `.{...}` and `.metadata` are left for the caller.
    fn parse_target_ref(&mut self) -> Option<TargetRef> {
        let chain_continues = |p: &Self| {
            p.at(TokenKind::Dot) && (p.nth_is_name(1) || p.nth(1).kind == TokenKind::Dollar)
        };
        let first = self.parse_qualified_name()?;
        if !chain_continues(self) {
            return Some(TargetRef::Name(first));
        }
        let mut links = vec![first];
        while chain_continues(self) {
            self.bump();
            links.push(self.parse_qualified_name()?);
        }
        Some(TargetRef::Chain(links))
    }

    /// `<short> name?` | `name`
    fn parse_identification(&mut self) -> Identification {
        let mut id = Identification::default();
        if self.at(TokenKind::Lt) {
            self.bump();
            id.short_name = self.parse_name();
            self.expect(TokenKind::Gt, "`>` closing short name");
        }
        if self.at_name() {
            id.name = self.parse_name();
        }
        id
    }

    // ---- root & members ----

    fn parse_root(&mut self) -> SourceUnit {
        let mut members = Vec::new();
        while !self.at_eof() {
            let before = self.pos;
            match self.parse_member() {
                Some(m) => members.push(m),
                None => {
                    // Repair eligibility is only actionable in body member
                    // loops (result-expression priority); drop it here.
                    self.semi_repair = SemiRepair::Off;
                    self.recover();
                    // Guarantee progress even if recovery stopped immediately
                    // (e.g. stray `}` at top level).
                    if self.pos == before && !self.at_eof() {
                        self.bump();
                    }
                }
            }
        }
        SourceUnit {
            dialect: self.dialect,
            members,
        }
    }

    fn parse_body_members(&mut self) -> Vec<Member> {
        if self.depth >= MAX_NESTING {
            self.error_here(format!(
                "nesting is too deep (more than {MAX_NESTING} levels of bodies and expressions)"
            ));
            self.skip_to_body_close();
            return Vec::new();
        }
        self.depth += 1;
        let members = self.parse_body_members_inner();
        self.depth -= 1;
        members
    }

    /// Consume the rest of the current body, leaving its closing brace for
    /// the caller. Used when the parser refuses to descend any further, so
    /// that one diagnostic is reported instead of a cascade.
    fn skip_to_body_close(&mut self) {
        let mut depth = 0i32;
        while !self.at_eof() {
            match self.cur().kind {
                TokenKind::LBrace => depth += 1,
                TokenKind::RBrace => {
                    if depth == 0 {
                        return;
                    }
                    depth -= 1;
                }
                _ => {}
            }
            self.bump();
        }
    }

    fn parse_body_members_inner(&mut self) -> Vec<Member> {
        let mut members = Vec::new();
        // Members of a body are siblings: each spells a chain of its own
        // rather than continuing the one its predecessor spelled, and the
        // body leans as deep as its deepest member (see [`Self::branch`]).
        let mut deepest = self.expr_chain;
        while !self.at(TokenKind::RBrace) && !self.at_eof() {
            deepest = deepest.max(self.expr_chain);
            self.expr_chain = 0;
            let before = self.pos;
            let diags_before = self.diags.len();
            match self.parse_member() {
                Some(m) => members.push(m),
                None => {
                    // The member parse failed. Before recovering, try the
                    // trailing-result-expression form (calc/case/constraint
                    // bodies): rewind and parse an expression that must end
                    // the body.
                    let repair_eligible = self.semi_repair == SemiRepair::Eligible;
                    self.semi_repair = SemiRepair::Off;
                    let failed_pos = self.pos;
                    let failed_diags = self.diags.split_off(diags_before);
                    self.pos = before;
                    let start = self.cur().span;
                    // The result member is prefixed like any member: an
                    // optional visibility marker may precede the expression.
                    let visibility = if self.eat_kw("public") {
                        Some(Visibility::Public)
                    } else if self.eat_kw("private") {
                        Some(Visibility::Private)
                    } else if self.eat_kw("protected") {
                        Some(Visibility::Protected)
                    } else {
                        None
                    };
                    let expr_diags_before = self.diags.len();
                    if let Some(expr) = self.parse_expr() {
                        if self.at(TokenKind::RBrace) && self.diags.len() == expr_diags_before {
                            let span = start.join(self.prev_end_span());
                            members.push(Member {
                                visibility,
                                leading_then: false,
                                leading_then_multiplicity: None,
                                kind: MemberKind::Result(expr),
                                span,
                            });
                            continue;
                        }
                    }
                    // The expression attempt failed (or left trailing
                    // tokens): keep its position and diagnostics for the
                    // furthest-failure comparison below.
                    let expr_failed_pos = self.pos;
                    let expr_diags = self.diags.split_off(expr_diags_before);
                    // The result-expression form lost. If the failure was a
                    // missing `;` before the closing `}`, re-parse the
                    // member with the repair armed: the member is kept and
                    // the diagnostic lands at the end of its own line.
                    if repair_eligible {
                        self.pos = before;
                        self.diags.truncate(diags_before);
                        self.semi_repair = SemiRepair::Armed;
                        let repaired = self.parse_member();
                        self.semi_repair = SemiRepair::Off;
                        if let Some(m) = repaired {
                            members.push(m);
                            continue;
                        }
                        self.diags.truncate(diags_before);
                    }
                    // Restore whichever failure reached further: the
                    // interpretation that consumed more input almost
                    // always names the real problem (a trailing `and`
                    // fails the expression at the closing `}`, far past
                    // where the member parse tripped over the first
                    // operator).
                    if expr_failed_pos > failed_pos && !expr_diags.is_empty() {
                        self.pos = expr_failed_pos;
                        self.diags.extend(expr_diags);
                    } else {
                        self.pos = failed_pos;
                        self.diags.extend(failed_diags);
                    }
                    self.recover();
                    if self.pos == before && !self.at_eof() && !self.at(TokenKind::RBrace) {
                        self.bump();
                    }
                }
            }
        }
        self.expr_chain = deepest.max(self.expr_chain);
        members
    }

    fn parse_member(&mut self) -> Option<Member> {
        let start = self.cur().span;
        let visibility = if self.eat_kw("public") {
            Some(Visibility::Public)
        } else if self.eat_kw("private") {
            Some(Visibility::Private)
        } else if self.eat_kw("protected") {
            Some(Visibility::Protected)
        } else {
            None
        };

        // A `then` plus an optional source-end multiplicity directly before
        // a full member is the declaration-less source-succession shorthand.
        let mut leading_then = false;
        let mut leading_then_multiplicity = None;
        let mut visibility = visibility;
        if self.at_kw("then") {
            let checkpoint = self.pos;
            self.bump();
            if self.at(TokenKind::LBracket) {
                leading_then_multiplicity = self.parse_multiplicity();
            }
            let starts_full_member = self.at(TokenKind::Hash)
                || self.at_kw("public")
                || self.at_kw("private")
                || self.at_kw("protected")
                || (self.cur().kind == TokenKind::Ident && self.is_reserved_word(self.cur_text()));
            if starts_full_member {
                leading_then = true;
            } else {
                self.pos = checkpoint;
                leading_then_multiplicity = None;
            }
        }
        if leading_then {
            // The member's own visibility prefix follows the `then`.
            if visibility.is_none() {
                visibility = if self.eat_kw("public") {
                    Some(Visibility::Public)
                } else if self.eat_kw("private") {
                    Some(Visibility::Private)
                } else if self.eat_kw("protected") {
                    Some(Visibility::Protected)
                } else {
                    None
                };
            }
        }

        // `ActionTargetSuccessionMember` carries its `MemberPrefix` before
        // the optional multiplicity-only source end. Recognize that narrow
        // shape before a leading `[` is committed to an ordinary usage.
        let kind = if self.at(TokenKind::LBracket) {
            let checkpoint = self.pos;
            let diags = self.diags.len();
            let source = self.parse_optional_end_multiplicity();
            if source.is_some() && self.eat_kw("then") {
                let target = self.parse_connector_end()?;
                let body = self.parse_body_or_semi()?;
                MemberKind::Usage(Usage {
                    prefix: UsagePrefix::default(),
                    kind: UsageKind::Succession,
                    declaration: FeatureDeclaration::default(),
                    detail: UsageDetail::Succession {
                        source: source.map(Box::new),
                        target: Box::new(target),
                    },
                    value: None,
                    is_parallel: false,
                    body,
                })
            } else {
                self.pos = checkpoint;
                self.diags.truncate(diags);
                self.parse_member_kind()?
            }
        } else {
            self.parse_member_kind()?
        };
        let span = start.join(self.prev_end_span());
        Some(Member {
            visibility,
            leading_then,
            leading_then_multiplicity,
            kind,
            span,
        })
    }

    fn prev_end_span(&self) -> Span {
        if self.pos == 0 {
            self.cur().span
        } else {
            self.tokens[self.pos - 1].span
        }
    }

    fn parse_member_kind(&mut self) -> Option<MemberKind> {
        // Namespace-level constructs.
        if self.at_kw("package")
            || (self.at_kw("library") && !self.nth_kw(1, "def"))
            || self.at_kw("standard")
        {
            return self.parse_package(Vec::new()).map(MemberKind::Package);
        }
        if self.at_kw("import") {
            return self.parse_import().map(MemberKind::Import);
        }
        if self.at_kw("alias") {
            return self.parse_alias().map(MemberKind::Alias);
        }
        if self.at_kw("filter") {
            self.bump();
            let expr = self.parse_expr()?;
            self.expect_semi("after filter expression");
            return Some(MemberKind::Filter(expr));
        }
        if self.at_kw("dependency") {
            return self
                .parse_dependency(Vec::new())
                .map(MemberKind::Dependency);
        }

        // `#Meta` prefix metadata: may precede packages, dependencies,
        // namespaces, metadata features, definitions and usages (including
        // user-keyword extensions).
        if self.at(TokenKind::Hash) {
            let metadata = self.parse_prefix_metadata();
            if self.at_kw("package")
                || (self.at_kw("library") && !self.nth_kw(1, "def"))
                || self.at_kw("standard")
            {
                return self.parse_package(metadata).map(MemberKind::Package);
            }
            if self.at_kw("dependency") {
                return self.parse_dependency(metadata).map(MemberKind::Dependency);
            }
            if self.at(TokenKind::At)
                || (self.at_kw("metadata")
                    && (self.dialect == Dialect::Kerml || !self.nth_kw(1, "def")))
            {
                return self.parse_metadata_usage(metadata).map(MemberKind::Usage);
            }
            if self.dialect == Dialect::Kerml {
                if self.at_kw("namespace") {
                    return self.parse_namespace(metadata).map(MemberKind::Package);
                }
                return self.parse_kerml_def_or_usage(metadata);
            }
            return self.parse_definition_or_usage_with(metadata);
        }

        // Annotating elements.
        if self.at_kw("comment") || self.at_kw("locale") || self.at(TokenKind::RegularComment) {
            return self.parse_comment().map(MemberKind::Comment);
        }
        if self.at_kw("doc") {
            return self.parse_doc().map(MemberKind::Doc);
        }
        if self.at_kw("rep") || self.at_kw("language") {
            return self.parse_textual_rep().map(MemberKind::TextualRep);
        }
        if self.at(TokenKind::At)
            || (self.at_kw("metadata") && !self.nth_kw(1, "def") && self.dialect == Dialect::Sysml)
            || (self.at_kw("metadata") && self.dialect == Dialect::Kerml)
        {
            return self.parse_metadata_usage(Vec::new()).map(MemberKind::Usage);
        }

        if self.dialect == Dialect::Kerml {
            return self.parse_kerml_member_kind();
        }

        // Requirement / case body members.
        if self.at_kw("subject") {
            self.bump();
            return self
                .parse_plain_usage(UsageKind::Ref)
                .map(MemberKind::Subject);
        }
        if self.at_kw("actor") {
            self.bump();
            return self
                .parse_plain_usage(UsageKind::Part)
                .map(MemberKind::Actor);
        }
        if self.at_kw("stakeholder") {
            self.bump();
            return self
                .parse_plain_usage(UsageKind::Part)
                .map(MemberKind::Stakeholder);
        }
        if self.at_kw("objective") {
            self.bump();
            return self
                .parse_plain_usage(UsageKind::Requirement)
                .map(MemberKind::Objective);
        }
        if self.at_kw("require") || self.at_kw("assume") {
            let kind = if self.at_kw("assume") {
                RequirementConstraintKind::Assumption
            } else {
                RequirementConstraintKind::Requirement
            };
            self.bump();
            let usage = self.parse_ref_or_kind_usage(UsageKind::Constraint, "constraint")?;
            return Some(MemberKind::RequirementConstraint { kind, usage });
        }
        if self.at_kw("frame") {
            self.bump();
            let usage = self.parse_ref_or_kind_usage(UsageKind::Concern, "concern")?;
            return Some(MemberKind::FramedConcern(usage));
        }
        if self.at_kw("verify") {
            self.bump();
            let usage = self.parse_ref_or_kind_usage(UsageKind::Requirement, "requirement")?;
            return Some(MemberKind::RequirementVerification(usage));
        }

        // A `do` whose effect is followed by `then` is a target-transition
        // tail, not a state `do` subaction. Delay the state-subaction commit
        // until this bounded lookahead has ruled that form out.
        if self.at_kw("do") && self.transition_tail_ahead() {
            return self.parse_transition_tail(None).map(MemberKind::Usage);
        }

        // State body members.
        if self.at_kw("entry") || self.at_kw("do") || self.at_kw("exit") {
            return self.parse_state_subaction();
        }

        // View body members.
        if self.at_kw("expose") {
            return self.parse_expose().map(MemberKind::Expose);
        }
        if self.at_kw("render") {
            self.bump();
            let usage = self.parse_ref_or_kind_usage(UsageKind::Rendering, "rendering")?;
            return Some(MemberKind::Render(usage));
        }

        // Calculation body members.
        if self.at_kw("return") {
            self.bump();
            match self.parse_definition_or_usage()? {
                MemberKind::Usage(u) => return Some(MemberKind::Return(u)),
                _ => {
                    self.error_here("`return` must be followed by a usage".to_string());
                    return None;
                }
            }
        }

        // Action / state body successions and transitions.
        if self.at_kw("first") {
            return self.parse_first_member();
        }
        if self.at_kw("then") {
            // Target succession: `then [mult]? target ;`
            self.bump();
            let source = self.parse_optional_end_multiplicity();
            let target = self.parse_connector_end()?;
            let body = self.parse_body_or_semi()?;
            return Some(MemberKind::Usage(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Succession,
                declaration: FeatureDeclaration::default(),
                detail: UsageDetail::Succession {
                    source: source.map(Box::new),
                    target: Box::new(target),
                },
                value: None,
                is_parallel: false,
                body,
            }));
        }
        if self.at_kw("else") {
            // Default target transition: `else target ;`
            self.bump();
            let target = self.parse_connector_end()?;
            let body = self.parse_body_or_semi()?;
            return Some(MemberKind::Usage(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Transition,
                declaration: FeatureDeclaration::default(),
                detail: UsageDetail::Transition {
                    source: None,
                    trigger: None,
                    guard: None,
                    effect: None,
                    target: Some(Box::new(target)),
                    is_default: true,
                },
                value: None,
                is_parallel: false,
                body,
            }));
        }
        if self.at_kw("if") {
            return self.parse_if_member();
        }
        if self.at_kw("transition") {
            return self.parse_transition(true).map(MemberKind::Usage);
        }
        if self.at_kw("accept") && !self.accept_is_node() {
            // Target-transition shorthand starting at the trigger.
            return self.parse_transition_tail(None).map(MemberKind::Usage);
        }

        self.parse_definition_or_usage()
    }

    /// `('#' Metaclass)+`
    fn parse_prefix_metadata(&mut self) -> Vec<QualifiedName> {
        let mut metadata = Vec::new();
        while self.eat(TokenKind::Hash) {
            if let Some(qn) = self.parse_qualified_name() {
                metadata.push(qn);
            } else {
                break;
            }
        }
        metadata
    }

    /// A plain usage continuation: metadata-extension? declaration? value?
    /// body. Used for members that wrap a usage (`subject`, `actor`,
    /// `objective`, …), whose keyword may be followed by `#Meta` extensions.
    fn parse_plain_usage(&mut self, kind: UsageKind) -> Option<Usage> {
        let mut prefix = UsagePrefix::default();
        if self.at(TokenKind::Hash) {
            prefix.metadata = self.parse_prefix_metadata();
        }
        let declaration = self.parse_feature_declaration();
        let value = self.parse_value_part();
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind,
            declaration,
            detail: UsageDetail::None,
            value,
            is_parallel: false,
            body,
        })
    }

    /// `<ref-target> spec* body` or `<kind-kw> decl? value? body` — the shape
    /// shared by `require`/`frame`/`verify`/`render` members: either a
    /// reference to an existing element or an inline declaration.
    fn parse_ref_or_kind_usage(&mut self, kind: UsageKind, kind_kw: &str) -> Option<Usage> {
        let mut prefix = UsagePrefix::default();
        if self.at(TokenKind::Hash) {
            prefix.metadata = self.parse_prefix_metadata();
        }
        let mut declaration = FeatureDeclaration::default();
        if self.eat_kw(kind_kw) || !prefix.metadata.is_empty() {
            // Kind keyword or extension-keyword form: an inline declaration.
            declaration = self.parse_feature_declaration();
        } else {
            let target = self.parse_target_ref()?;
            declaration
                .specializations
                .push(FeatureSpecialization::References(target));
            self.parse_feature_specializations(&mut declaration);
        }
        let value = self.parse_value_part();
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind,
            declaration,
            detail: UsageDetail::None,
            value,
            is_parallel: false,
            body,
        })
    }

    /// `entry`/`do`/`exit` state sub-action member.
    fn parse_state_subaction(&mut self) -> Option<MemberKind> {
        let kind = if self.at_kw("entry") {
            StateSubactionKind::Entry
        } else if self.at_kw("do") {
            StateSubactionKind::Do
        } else {
            StateSubactionKind::Exit
        };
        self.bump();
        if self.eat(TokenKind::Semi) {
            return Some(MemberKind::StateSubaction { kind, action: None });
        }
        let action = self.parse_performed_action()?;
        Some(MemberKind::StateSubaction {
            kind,
            action: Some(action),
        })
    }

    /// PerformedActionUsage: perform-style reference/declaration, or an
    /// accept/send/assign node declaration, with an action body.
    fn parse_performed_action(&mut self) -> Option<Usage> {
        if self.at_kw("accept") {
            self.bump();
            let detail = self.parse_accept_detail()?;
            let body = self.parse_body_or_semi()?;
            return Some(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Accept,
                declaration: FeatureDeclaration::default(),
                detail,
                value: None,
                is_parallel: false,
                body,
            });
        }
        if self.at_kw("send") {
            self.bump();
            return self.parse_send_rest(UsagePrefix::default(), FeatureDeclaration::default());
        }
        if self.at_kw("assign") {
            self.bump();
            return self.parse_assign_rest(UsagePrefix::default(), FeatureDeclaration::default());
        }
        // Perform-style: `action decl?` or reference target.
        let mut declaration = FeatureDeclaration::default();
        if self.eat_kw("action") {
            declaration = self.parse_feature_declaration();
            // ActionNodeUsageDeclaration is an optional common prefix of the
            // accept/send/assign node declarations. Do not commit it to the
            // perform alternative before inspecting the following keyword.
            if self.eat_kw("accept") {
                let detail = self.parse_accept_detail()?;
                let body = self.parse_body_or_semi()?;
                return Some(Usage {
                    prefix: UsagePrefix::default(),
                    kind: UsageKind::Accept,
                    declaration,
                    detail,
                    value: None,
                    is_parallel: false,
                    body,
                });
            }
            if self.eat_kw("send") {
                return self.parse_send_rest(UsagePrefix::default(), declaration);
            }
            if self.eat_kw("assign") {
                return self.parse_assign_rest(UsagePrefix::default(), declaration);
            }
        } else {
            let target = self.parse_target_ref()?;
            declaration
                .specializations
                .push(FeatureSpecialization::References(target));
            self.parse_feature_specializations(&mut declaration);
        }
        let value = self.parse_value_part();
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix: UsagePrefix::default(),
            kind: UsageKind::Perform,
            declaration,
            detail: UsageDetail::None,
            value,
            is_parallel: false,
            body,
        })
    }

    /// `expose` — same shape as an import, in view bodies.
    fn parse_expose(&mut self) -> Option<Import> {
        self.expect_kw("expose");
        let target = self.parse_qualified_name()?;
        let mut is_namespace = false;
        let mut is_recursive = false;
        while self.at(TokenKind::ColonColon) {
            match self.nth(1).kind {
                TokenKind::Star => {
                    self.bump();
                    self.bump();
                    is_namespace = true;
                }
                TokenKind::StarStar => {
                    self.bump();
                    self.bump();
                    is_recursive = true;
                    break;
                }
                _ => break,
            }
        }
        let mut filters = Vec::new();
        while self.eat(TokenKind::LBracket) {
            if let Some(e) = self.parse_expr() {
                filters.push(e);
            }
            self.expect(TokenKind::RBracket, "`]` closing expose filter");
        }
        if self.eat(TokenKind::LBrace) {
            self.parse_body_members();
            self.expect(TokenKind::RBrace, "`}` closing expose body");
        } else {
            self.expect_semi("after expose");
        }
        Some(Import {
            is_import_all: false,
            target,
            is_namespace,
            is_recursive,
            filters,
        })
    }

    /// `first X ;` (initial node) or `first a then b` / `first a if g then b`
    /// (succession / guarded succession).
    fn parse_first_member(&mut self) -> Option<MemberKind> {
        self.expect_kw("first");
        let source = self.parse_connector_end()?;
        if self.eat_kw("then") {
            let target = self.parse_connector_end()?;
            let body = self.parse_body_or_semi()?;
            return Some(MemberKind::Usage(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Succession,
                declaration: FeatureDeclaration::default(),
                detail: UsageDetail::Succession {
                    source: Some(Box::new(source)),
                    target: Box::new(target),
                },
                value: None,
                is_parallel: false,
                body,
            }));
        }
        if self.eat_kw("if") {
            let guard = self.parse_expr()?;
            self.expect_kw("then");
            let target = self.parse_connector_end()?;
            let body = self.parse_body_or_semi()?;
            return Some(MemberKind::Usage(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Transition,
                declaration: FeatureDeclaration::default(),
                detail: UsageDetail::Transition {
                    source: Some(source.target),
                    trigger: None,
                    guard: Some(Box::new(guard)),
                    effect: None,
                    target: Some(Box::new(target)),
                    is_default: false,
                },
                value: None,
                is_parallel: false,
                body,
            }));
        }
        // Initial node member: `first X ;` (relationship body allowed).
        let TargetRef::Name(qn) = source.target else {
            self.error_here("an initial node target must be a qualified name".to_string());
            return None;
        };
        if self.eat(TokenKind::LBrace) {
            self.parse_body_members();
            self.expect(TokenKind::RBrace, "`}`");
        } else {
            self.expect_semi("after initial node");
        }
        Some(MemberKind::InitialNode(qn))
    }

    /// Member starting with `if`: an if-node (`if g { … }`), a guarded target
    /// succession (`if g then t;`), or a conditional result expression.
    fn parse_if_member(&mut self) -> Option<MemberKind> {
        let start = self.cur().span;
        self.expect_kw("if");
        let cond = self.parse_null_coalescing()?;
        if self.at(TokenKind::Question) {
            // Conditional *expression* — this is a result expression member.
            self.bump();
            let then_branch = self.parse_expr()?;
            self.expect_kw("else");
            let else_branch = self.parse_expr()?;
            let span = start.join(else_branch.span);
            return Some(MemberKind::Result(Expr {
                kind: ExprKind::Conditional {
                    cond: Box::new(cond),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                },
                span,
            }));
        }
        if self.at_kw("then") || self.at_kw("do") {
            // Guard-first target transition; an effect may sit between the
            // guard and `then`: `if g do <effect> then t;`.
            let effect = if self.eat_kw("do") {
                Some(Box::new(self.parse_performed_action_no_body()?))
            } else {
                None
            };
            self.expect_kw("then");
            let target = self.parse_connector_end()?;
            let body = self.parse_body_or_semi()?;
            return Some(MemberKind::Usage(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Transition,
                declaration: FeatureDeclaration::default(),
                detail: UsageDetail::Transition {
                    source: None,
                    trigger: None,
                    guard: Some(Box::new(cond)),
                    effect,
                    target: Some(Box::new(target)),
                    is_default: false,
                },
                value: None,
                is_parallel: false,
                body,
            }));
        }
        // If-node.
        self.parse_if_node_rest(UsagePrefix::default(), FeatureDeclaration::default(), cond)
            .map(MemberKind::Usage)
    }

    /// After `accept` at member start: is this an accept *node* (ends with
    /// `;`/`{` after the payload) rather than a transition shorthand
    /// (`accept … then …`)? Scan ahead for `then`/`if`/`do` before the
    /// terminator.
    ///
    /// A brace only nests where an expression may spell one: the
    /// body-expression argument of an operator applied through `->`
    /// (`xs->exists { in x; x > 0 }`), or an operand position inside a
    /// trigger or value expression. A brace anywhere a complete expression
    /// has just ended — after a name, a literal or a closing bracket —
    /// opens the node's own body and ends the scan.
    ///
    /// Only a brace can hold a `;`, so an unclosed `(` or `[` never
    /// carries the scan past the member's own terminator, and a run of
    /// members that each leave a bracket open costs time linear in the
    /// body rather than quadratic. Unclosed braces are bounded instead by
    /// the nesting the parser will descend at all: past that the input is
    /// refused whichever way this classifies it. Within those bounds the
    /// scan is not truncated by a token count — an arbitrarily long
    /// trigger is still classified from its own tokens.
    fn accept_is_node(&self) -> bool {
        let mut scanned = 1;
        let is_node = self.accept_node_scan(&mut scanned);
        ACCEPT_LOOKAHEAD_TOKENS.with(|n| n.set(n.get().saturating_add(scanned as u64)));
        is_node
    }

    /// The scan itself, leaving the token it stopped at in `i` so its cost
    /// can be observed (see [`take_accept_lookahead_tokens`]).
    fn accept_node_scan(&self, i: &mut usize) -> bool {
        #[derive(PartialEq, Eq, Clone, Copy)]
        enum ArrowRef {
            /// Not in the target reference of `->`.
            No,
            /// A name is expected next: just after `->`, `::`, `.` or the
            /// global-scope root `$`.
            Expect,
            /// The last token was one of the reference's names.
            InName,
        }

        // Expression braces the scan has entered, and parentheses and
        // brackets within them. They are counted apart because a `;` ends
        // the member wherever a brace is not holding it.
        let mut braces = 0i32;
        let mut groups = 0i32;
        // Whether a `{` at this point would open an expression rather than
        // the node's own body.
        let mut expr_brace = false;
        // Where in the target reference of `->` the scan stands. The
        // reference names the operator whose argument may be a body
        // expression, and its own words are not member keywords.
        let mut arrow = ArrowRef::No;
        loop {
            let t = self.nth(*i);
            match t.kind {
                TokenKind::Eof => return true,
                TokenKind::Semi if braces == 0 => return true,
                TokenKind::LBrace if braces == 0 && groups == 0 && !expr_brace => return true,
                TokenKind::RBrace if braces == 0 => return true,
                TokenKind::LBrace => {
                    braces += 1;
                    if braces > MAX_NESTING as i32 {
                        return true;
                    }
                }
                TokenKind::RBrace => braces -= 1,
                TokenKind::LParen | TokenKind::LBracket => groups += 1,
                TokenKind::RParen | TokenKind::RBracket if groups > 0 => groups -= 1,
                TokenKind::Ident if braces == 0 && groups == 0 && arrow != ArrowRef::Expect => {
                    let text = t.text(self.src);
                    // `if` is the shorthand's guard only where a complete
                    // expression has just ended. Where an operand is
                    // expected instead it opens a conditional expression
                    // — the trigger, the `via` expression and a payload's
                    // value are all parsed as full expressions, and each
                    // admits one — so the same state that says whether a
                    // brace would open an expression says whether this
                    // `if` does.
                    if text == "then" || text == "do" || (text == "if" && !expr_brace) {
                        return false;
                    }
                }
                _ => {}
            }
            // What a `{` would mean *after* this token.
            match t.kind {
                TokenKind::Arrow => {
                    arrow = ArrowRef::Expect;
                    expr_brace = false;
                }
                // A target reference continues through a qualification, a
                // feature-chain step, and the global-scope root it may
                // start from: `->f.g { … }`, `->$::Q::exists { … }`.
                TokenKind::ColonColon | TokenKind::Dot if arrow == ArrowRef::InName => {
                    arrow = ArrowRef::Expect;
                    expr_brace = false;
                }
                TokenKind::Dollar if arrow == ArrowRef::Expect => {
                    arrow = ArrowRef::InName;
                    expr_brace = true;
                }
                TokenKind::Ident | TokenKind::UnrestrictedName => {
                    expr_brace = if arrow == ArrowRef::Expect {
                        arrow = ArrowRef::InName;
                        true
                    } else {
                        arrow = ArrowRef::No;
                        // Words an operand follows: the trigger and `via`
                        // clauses introduce one, `else` continues a
                        // conditional expression with one, and the
                        // word-spelled operators take one the way their
                        // symbolic spellings do. The classification words
                        // (`as`, `istype`, `hastype`, `meta`) and `all`
                        // take a type name instead, where a brace cannot
                        // stand, so they are not here.
                        matches!(
                            t.text(self.src),
                            "at" | "after"
                                | "when"
                                | "via"
                                | "else"
                                | "and"
                                | "or"
                                | "xor"
                                | "implies"
                                | "not"
                        )
                    };
                }
                TokenKind::String
                | TokenKind::Decimal
                | TokenKind::Exp
                | TokenKind::RParen
                | TokenKind::RBracket
                | TokenKind::RBrace
                | TokenKind::LBrace => {
                    arrow = ArrowRef::No;
                    expr_brace = false;
                }
                // Operators, separators and openers all leave an operand
                // expected, and an expression may spell that operand as a
                // body.
                _ => {
                    arrow = ArrowRef::No;
                    expr_brace = true;
                }
            }
            *i += 1;
        }
    }

    /// Whether a member beginning with `do` reaches a top-level `then`
    /// before its own terminator. Nested optional effect bodies are skipped.
    fn transition_tail_ahead(&self) -> bool {
        let mut i = 1;
        let mut depth = 0i32;
        loop {
            let t = self.nth(i);
            match t.kind {
                TokenKind::Eof => return false,
                TokenKind::LParen | TokenKind::LBracket | TokenKind::LBrace => depth += 1,
                TokenKind::RParen | TokenKind::RBracket if depth > 0 => depth -= 1,
                TokenKind::RBrace if depth > 0 => {
                    depth -= 1;
                    // An effect's optional braced body is its final part. If
                    // `then` is not immediately next, this was a complete
                    // state `do` subaction and later members must not make it
                    // look like a transition tail.
                    if depth == 0 {
                        return self.nth(i + 1).is_kw(self.src, "then");
                    }
                }
                TokenKind::RBrace if depth == 0 => return false,
                TokenKind::Semi if depth == 0 => return false,
                TokenKind::Ident if depth == 0 && t.is_kw(self.src, "then") => return true,
                _ => {}
            }
            i += 1;
            if i > 256 {
                return false;
            }
        }
    }

    /// Target-transition shorthand: `[transition] trigger? guard? effect?
    /// then target body` (source is the preceding member).
    fn parse_transition_tail(&mut self, source: Option<TargetRef>) -> Option<Usage> {
        let trigger = if self.eat_kw("accept") {
            Some(Box::new(self.parse_accept_detail()?))
        } else {
            None
        };
        let guard = if self.eat_kw("if") {
            Some(self.parse_expr()?)
        } else {
            None
        };
        let effect = if self.eat_kw("do") {
            Some(Box::new(self.parse_performed_action_no_body()?))
        } else {
            None
        };
        self.expect_kw("then");
        let target = self.parse_connector_end()?;
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix: UsagePrefix::default(),
            kind: UsageKind::Transition,
            declaration: FeatureDeclaration::default(),
            detail: UsageDetail::Transition {
                source,
                trigger,
                guard: guard.map(Box::new),
                effect,
                target: Some(Box::new(target)),
                is_default: false,
            },
            value: None,
            is_parallel: false,
            body,
        })
    }

    /// Full `transition` usage: `transition (decl? first)? source trigger?
    /// guard? effect? then target body`, or the keyword form of the
    /// target-transition shorthand.
    fn parse_transition(&mut self, _member: bool) -> Option<Usage> {
        self.expect_kw("transition");
        // Shorthand form: straight to trigger/guard/effect/then.
        if self.at_kw("accept") || self.at_kw("if") || self.at_kw("do") || self.at_kw("then") {
            return self.parse_transition_tail(None);
        }
        // `decl? 'first'` or the source directly.
        let checkpoint = self.pos;
        let diags = self.diags.len();
        let mut declaration = FeatureDeclaration::default();
        let source;
        let decl = self.parse_feature_declaration();
        if self.eat_kw("first") {
            declaration = decl;
            source = Some(self.parse_target_ref()?);
        } else {
            // What we parsed was actually the source reference.
            self.pos = checkpoint;
            self.diags.truncate(diags);
            source = Some(self.parse_target_ref()?);
        }
        let trigger = if self.eat_kw("accept") {
            Some(Box::new(self.parse_accept_detail()?))
        } else {
            None
        };
        let guard = if self.eat_kw("if") {
            Some(self.parse_expr()?)
        } else {
            None
        };
        let effect = if self.eat_kw("do") {
            Some(Box::new(self.parse_performed_action_no_body()?))
        } else {
            None
        };
        self.expect_kw("then");
        let target = self.parse_connector_end()?;
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix: UsagePrefix::default(),
            kind: UsageKind::Transition,
            declaration,
            detail: UsageDetail::Transition {
                source,
                trigger,
                guard: guard.map(Box::new),
                effect,
                target: Some(Box::new(target)),
                is_default: false,
            },
            value: None,
            is_parallel: false,
            body,
        })
    }

    /// A performed action as a transition effect (`do …`): no trailing body
    /// terminator of its own (optional `{…}` per grammar).
    fn parse_performed_action_no_body(&mut self) -> Option<Usage> {
        // The empty EffectBehaviorUsage alternative consumes no action text;
        // the caller's `then` remains untouched.
        if self.at_kw("then") {
            return Some(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Action,
                declaration: FeatureDeclaration::default(),
                detail: UsageDetail::None,
                value: None,
                is_parallel: false,
                body: None,
            });
        }
        if self.at_kw("send") {
            self.bump();
            let (payload, via, to) = self.parse_send_parts()?;
            let body = if self.at(TokenKind::LBrace) {
                self.parse_brace_body()
            } else {
                None
            };
            return Some(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Send,
                declaration: FeatureDeclaration::default(),
                detail: UsageDetail::Send {
                    payload: payload.map(Box::new),
                    via: via.map(Box::new),
                    to: to.map(Box::new),
                },
                value: None,
                is_parallel: false,
                body,
            });
        }
        if self.at_kw("accept") {
            self.bump();
            let detail = self.parse_accept_detail()?;
            let body = if self.at(TokenKind::LBrace) {
                self.parse_brace_body()
            } else {
                None
            };
            return Some(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Accept,
                declaration: FeatureDeclaration::default(),
                detail,
                value: None,
                is_parallel: false,
                body,
            });
        }
        if self.at_kw("assign") {
            self.bump();
            let target = self.parse_primary()?;
            self.expect(TokenKind::ColonEq, "`:=` in assignment");
            let value = self.parse_expr()?;
            let body = if self.at(TokenKind::LBrace) {
                self.parse_brace_body()
            } else {
                None
            };
            return Some(Usage {
                prefix: UsagePrefix::default(),
                kind: UsageKind::Assign,
                declaration: FeatureDeclaration::default(),
                detail: UsageDetail::Assign {
                    target: Box::new(target),
                    value: Box::new(value),
                },
                value: None,
                is_parallel: false,
                body,
            });
        }
        let mut declaration = FeatureDeclaration::default();
        if self.eat_kw("action") {
            declaration = self.parse_feature_declaration();
            if self.eat_kw("send") {
                let (payload, via, to) = self.parse_send_parts()?;
                let body = if self.at(TokenKind::LBrace) {
                    self.parse_brace_body()
                } else {
                    None
                };
                return Some(Usage {
                    prefix: UsagePrefix::default(),
                    kind: UsageKind::Send,
                    declaration,
                    detail: UsageDetail::Send {
                        payload: payload.map(Box::new),
                        via: via.map(Box::new),
                        to: to.map(Box::new),
                    },
                    value: None,
                    is_parallel: false,
                    body,
                });
            }
            if self.eat_kw("accept") {
                let detail = self.parse_accept_detail()?;
                let body = if self.at(TokenKind::LBrace) {
                    self.parse_brace_body()
                } else {
                    None
                };
                return Some(Usage {
                    prefix: UsagePrefix::default(),
                    kind: UsageKind::Accept,
                    declaration,
                    detail,
                    value: None,
                    is_parallel: false,
                    body,
                });
            }
            if self.eat_kw("assign") {
                let target = self.parse_primary()?;
                self.expect(TokenKind::ColonEq, "`:=` in assignment");
                let assigned = self.parse_expr()?;
                let body = if self.at(TokenKind::LBrace) {
                    self.parse_brace_body()
                } else {
                    None
                };
                return Some(Usage {
                    prefix: UsagePrefix::default(),
                    kind: UsageKind::Assign,
                    declaration,
                    detail: UsageDetail::Assign {
                        target: Box::new(target),
                        value: Box::new(assigned),
                    },
                    value: None,
                    is_parallel: false,
                    body,
                });
            }
        } else {
            let target = self.parse_target_ref()?;
            declaration
                .specializations
                .push(FeatureSpecialization::References(target));
        }
        let value = self.parse_value_part();
        let body = if self.at(TokenKind::LBrace) {
            self.parse_brace_body()
        } else {
            None
        };
        Some(Usage {
            prefix: UsagePrefix::default(),
            kind: UsageKind::Perform,
            declaration,
            detail: UsageDetail::None,
            value,
            is_parallel: false,
            body,
        })
    }

    /// `{ members }` when a brace is known to be present.
    fn parse_brace_body(&mut self) -> Option<Vec<Member>> {
        self.expect(TokenKind::LBrace, "`{`")?;
        let members = self.parse_body_members();
        self.expect(TokenKind::RBrace, "`}` closing body");
        Some(members)
    }

    /// Optional `[mult]` before a succession target (multiplicity source end).
    fn parse_optional_end_multiplicity(&mut self) -> Option<ConnectorEnd> {
        if self.at(TokenKind::LBracket) {
            let multiplicity = self.parse_multiplicity();
            Some(ConnectorEnd {
                multiplicity,
                name: None,
                target: TargetRef::unspelled(),
            })
        } else {
            None
        }
    }

    fn parse_package(&mut self, mut metadata: Vec<QualifiedName>) -> Option<Package> {
        let is_standard = self.eat_kw("standard");
        let is_library = self.eat_kw("library");
        if is_standard && !is_library {
            self.error_here("expected `library` after `standard`".to_string());
        }
        if self.at(TokenKind::Hash) {
            metadata.extend(self.parse_prefix_metadata());
        }
        self.expect_kw("package");
        let id = self.parse_identification();
        let body = if self.eat(TokenKind::Semi) {
            None
        } else if self.eat(TokenKind::LBrace) {
            let members = self.parse_body_members();
            self.expect(TokenKind::RBrace, "`}` closing package body");
            Some(members)
        } else if self.repair_missing_semi("after package declaration") {
            None
        } else {
            self.error_here(format!(
                "expected `;` or `{{` after package declaration, found `{}`",
                self.describe_cur()
            ));
            return None;
        };
        Some(Package {
            is_library,
            is_standard,
            is_namespace: false,
            metadata,
            id,
            body,
        })
    }

    /// KerML `namespace N? ( ; | { members } )`
    fn parse_namespace(&mut self, metadata: Vec<QualifiedName>) -> Option<Package> {
        self.expect_kw("namespace");
        let id = self.parse_identification();
        let body = self.parse_body_or_semi()?;
        Some(Package {
            is_library: false,
            is_standard: false,
            is_namespace: true,
            metadata,
            id,
            body,
        })
    }

    // ---- KerML dialect members ----

    fn parse_kerml_member_kind(&mut self) -> Option<MemberKind> {
        if self.at_kw("namespace") {
            return self.parse_namespace(Vec::new()).map(MemberKind::Package);
        }
        if self.at_kw("return") {
            self.bump();
            match self.parse_kerml_def_or_usage(Vec::new())? {
                MemberKind::Usage(u) => return Some(MemberKind::Return(u)),
                _ => {
                    self.error_here("`return` must be followed by a feature".to_string());
                    return None;
                }
            }
        }
        // Standalone relationship declarations.
        if self.at_kw("specialization")
            || self.at_kw("subtype")
            || self.at_kw("subclassifier")
            || self.at_kw("typing")
            || self.at_kw("subset")
            || self.at_kw("redefinition")
            || self.at_kw("conjugation")
            || self.at_kw("conjugate")
            || self.at_kw("disjoining")
            || self.at_kw("disjoint")
            || self.at_kw("inverting")
            || self.at_kw("inverse")
            || self.at_kw("featuring")
        {
            return self
                .parse_kerml_relationship()
                .map(MemberKind::Relationship);
        }
        if self.at_kw("multiplicity") {
            return self
                .parse_multiplicity_decl()
                .map(MemberKind::MultiplicityDecl);
        }
        self.parse_kerml_def_or_usage(Vec::new())
    }

    /// A KerML standalone relationship declaration.
    fn parse_kerml_relationship(&mut self) -> Option<RelationshipDecl> {
        use RelationshipDeclKind::*;
        let mut id = Identification::default();
        if self.eat_kw("specialization")
            || self.eat_kw("conjugation")
            || self.eat_kw("disjoining")
            || self.eat_kw("inverting")
        {
            id = self.parse_identification();
        }

        // `featuring (Id? of)? f by T` — the identification may be empty,
        // so a bare `of` can directly follow the keyword.
        if self.eat_kw("featuring") {
            if self.eat_kw("of") {
                let source = self.parse_target_ref()?;
                self.expect_kw("by");
                let target = self.parse_target_ref()?;
                self.parse_relationship_body();
                return Some(RelationshipDecl {
                    kind: TypeFeaturing,
                    id,
                    source,
                    target,
                });
            }
            let first = self.parse_target_ref()?;
            let source = if self.eat_kw("of") {
                if let TargetRef::Name(qn) = &first {
                    if qn.segments.len() == 1 {
                        id.name = Some(qn.segments[0].clone());
                    }
                }
                self.parse_target_ref()?
            } else {
                first
            };
            self.expect_kw("by");
            let target = self.parse_target_ref()?;
            self.parse_relationship_body();
            return Some(RelationshipDecl {
                kind: TypeFeaturing,
                id,
                source,
                target,
            });
        }

        let kind = if self.eat_kw("subtype") {
            Specialization
        } else if self.eat_kw("subclassifier") {
            Subclassification
        } else if self.eat_kw("typing") {
            FeatureTyping
        } else if self.eat_kw("subset") {
            Subsetting
        } else if self.eat_kw("redefinition") {
            Redefinition
        } else if self.eat_kw("conjugate") {
            Conjugation
        } else if self.eat_kw("disjoint") {
            Disjoining
        } else if self.eat_kw("inverse") {
            FeatureInverting
        } else {
            self.error_here(format!(
                "expected a relationship keyword, found `{}`",
                self.describe_cur()
            ));
            return None;
        };
        let source = self.parse_target_ref()?;
        // Separator per relationship kind.
        match kind {
            Specialization | Subclassification => {
                if !self.eat(TokenKind::ColonGt) {
                    self.expect_kw("specializes");
                }
            }
            FeatureTyping => {
                if !self.eat(TokenKind::Colon) {
                    self.expect_kw("typed");
                    self.expect_kw("by");
                }
            }
            Subsetting => {
                if !self.eat(TokenKind::ColonGt) {
                    self.expect_kw("subsets");
                }
            }
            Redefinition => {
                if !self.eat(TokenKind::ColonGtGt) {
                    self.expect_kw("redefines");
                }
            }
            Conjugation => {
                if !self.eat(TokenKind::Tilde) {
                    self.expect_kw("conjugates");
                }
            }
            Disjoining => {
                self.expect_kw("from");
            }
            FeatureInverting => {
                self.expect_kw("of");
            }
            TypeFeaturing => unreachable!(),
        }
        let target = self.parse_target_ref()?;
        self.parse_relationship_body();
        Some(RelationshipDecl {
            kind,
            id,
            source,
            target,
        })
    }

    /// `;` or `{ annotations }` closing a relationship declaration.
    fn parse_relationship_body(&mut self) {
        if self.eat(TokenKind::LBrace) {
            self.parse_body_members();
            self.expect(TokenKind::RBrace, "`}` closing relationship body");
        } else {
            self.expect_semi("after relationship");
        }
    }

    /// `multiplicity M (subsets N | [bounds]) body`
    fn parse_multiplicity_decl(&mut self) -> Option<MultiplicityDecl> {
        self.expect_kw("multiplicity");
        let id = self.parse_identification();
        let (subsets, range) = if self.at(TokenKind::LBracket) {
            (None, self.parse_multiplicity().map(|m| *m))
        } else {
            if !self.eat(TokenKind::ColonGt) {
                self.expect_kw("subsets");
            }
            (self.parse_target_ref(), None)
        };
        let body = self.parse_body_or_semi()?;
        Some(MultiplicityDecl {
            id,
            subsets,
            range,
            body,
        })
    }

    /// KerML definitions (type-like) and usages (feature-like).
    fn parse_kerml_def_or_usage(&mut self, mut metadata: Vec<QualifiedName>) -> Option<MemberKind> {
        let mut def_prefix = DefPrefix::default();
        let mut prefix = UsagePrefix::default();
        let mut saw_prefix = !metadata.is_empty();

        if self.eat_kw("member") {
            prefix.is_type_member = true;
            saw_prefix = true;
        }
        if self.eat_kw("in") {
            prefix.direction = Some(FeatureDirection::In);
            saw_prefix = true;
        } else if self.eat_kw("out") {
            prefix.direction = Some(FeatureDirection::Out);
            saw_prefix = true;
        } else if self.eat_kw("inout") {
            prefix.direction = Some(FeatureDirection::InOut);
            saw_prefix = true;
        }
        if self.eat_kw("derived") {
            prefix.is_derived = true;
            saw_prefix = true;
        }
        if self.eat_kw("abstract") {
            def_prefix.is_abstract = true;
            prefix.is_abstract = true;
            saw_prefix = true;
        }
        if self.eat_kw("composite") {
            prefix.is_composite = true;
            saw_prefix = true;
        } else if self.eat_kw("portion") {
            prefix.is_portion = true;
            saw_prefix = true;
        }
        if self.eat_kw("var") {
            prefix.is_variable = true;
            saw_prefix = true;
        } else if self.eat_kw("const") {
            prefix.is_constant = true;
            saw_prefix = true;
        }
        if self.eat_kw("end") {
            prefix.is_end = true;
            saw_prefix = true;
            // Optional cross feature — its own basic prefix plus a
            // declaration, valid only before a feature-introducing keyword:
            // `end [1] feature transferSource …;`,
            // `end self2 [1] feature sameThing …;`,
            // `end in x : T feature thatOccurrence …;`
            if self.at(TokenKind::LBracket)
                || self.at(TokenKind::Lt)
                || self.at_name()
                || self.at_kw("in")
                || self.at_kw("out")
                || self.at_kw("inout")
                || self.at_kw("derived")
                || self.at_kw("abstract")
                || self.at_kw("composite")
                || self.at_kw("portion")
                || self.at_kw("var")
                || self.at_kw("const")
                || self.at_kw("ordered")
                || self.at_kw("nonunique")
            {
                let checkpoint = self.pos;
                let diags = self.diags.len();
                let mut cross = CrossFeature::default();
                if self.eat_kw("in") {
                    cross.direction = Some(FeatureDirection::In);
                } else if self.eat_kw("out") {
                    cross.direction = Some(FeatureDirection::Out);
                } else if self.eat_kw("inout") {
                    cross.direction = Some(FeatureDirection::InOut);
                }
                if self.eat_kw("derived") {
                    cross.is_derived = true;
                }
                if self.eat_kw("abstract") {
                    cross.is_abstract = true;
                }
                if self.eat_kw("composite") {
                    cross.is_composite = true;
                } else if self.eat_kw("portion") {
                    cross.is_portion = true;
                }
                if self.eat_kw("var") {
                    cross.is_variable = true;
                } else if self.eat_kw("const") {
                    cross.is_constant = true;
                }
                cross.decl = self.parse_feature_declaration();
                let at_feature_kw = self.at_kw("feature")
                    || self.at_kw("connector")
                    || self.at_kw("binding")
                    || self.at_kw("succession")
                    || self.at_kw("flow")
                    || self.at_kw("step")
                    || self.at_kw("expr")
                    || self.at_kw("bool")
                    || self.at_kw("inv")
                    || self.at(TokenKind::Hash)
                    || self.at_feature_declaration_start();
                if !cross.decl.is_empty() && at_feature_kw {
                    prefix.end_cross = Some(Box::new(cross));
                } else {
                    self.pos = checkpoint;
                    self.diags.truncate(diags);
                }
            }
        }
        if self.at(TokenKind::Hash) {
            metadata.extend(self.parse_prefix_metadata());
            saw_prefix = true;
        }
        def_prefix.metadata = metadata.clone();
        prefix.metadata = metadata.clone();

        // Type-like kinds.
        if self.at_kw("assoc") {
            self.bump();
            let kind = if self.eat_kw("struct") {
                DefKind::AssocStruct
            } else {
                DefKind::Assoc
            };
            return self
                .parse_definition_rest(def_prefix, kind)
                .map(MemberKind::Definition);
        }
        let type_kind = if self.at_kw("type") {
            Some(DefKind::Type)
        } else if self.at_kw("classifier") {
            Some(DefKind::Classifier)
        } else if self.at_kw("class") {
            Some(DefKind::Class)
        } else if self.at_kw("struct") {
            Some(DefKind::Struct)
        } else if self.at_kw("datatype") {
            Some(DefKind::DataType)
        } else if self.at_kw("behavior") {
            Some(DefKind::Behavior)
        } else if self.at_kw("interaction") {
            Some(DefKind::Interaction)
        } else if self.at_kw("function") {
            Some(DefKind::Function)
        } else if self.at_kw("predicate") {
            Some(DefKind::Predicate)
        } else if self.at_kw("metaclass") {
            Some(DefKind::Metaclass)
        } else {
            None
        };
        if let Some(kind) = type_kind {
            self.bump();
            return self
                .parse_definition_rest(def_prefix, kind)
                .map(MemberKind::Definition);
        }

        // Feature-like kinds.
        if self.eat_kw("feature") {
            if self.meta_body {
                // `MetadataBodyFeature`: `'feature'? (':>>'|'redefines')? …`
                return self
                    .parse_metadata_body_usage(prefix, UsageKind::Feature)
                    .map(MemberKind::Usage);
            }
            return self
                .parse_usage_rest(prefix, UsageKind::Feature)
                .map(MemberKind::Usage);
        }
        if self.eat_kw("step") {
            return self
                .parse_usage_rest(prefix, UsageKind::Step)
                .map(MemberKind::Usage);
        }
        if self.eat_kw("expr") {
            return self
                .parse_usage_rest(prefix, UsageKind::Expr)
                .map(MemberKind::Usage);
        }
        if self.eat_kw("bool") {
            return self
                .parse_usage_rest(prefix, UsageKind::BoolExpr)
                .map(MemberKind::Usage);
        }
        if self.eat_kw("inv") {
            // `inv` / `inv true` / `inv false` (negated).
            let negated = if self.eat_kw("false") {
                true
            } else {
                self.eat_kw("true");
                false
            };
            let declaration = self.parse_feature_declaration();
            return self
                .finish_usage(
                    prefix,
                    UsageKind::Invariant,
                    declaration,
                    UsageDetail::Assert { negated },
                )
                .map(MemberKind::Usage);
        }
        if self.eat_kw("connector") {
            return self.parse_kerml_connector(prefix).map(MemberKind::Usage);
        }
        if self.at_kw("binding") {
            self.bump();
            return self.parse_kerml_binding(prefix).map(MemberKind::Usage);
        }
        if self.at_kw("succession") {
            self.bump();
            if self.eat_kw("flow") {
                return self
                    .parse_flow_usage(prefix, UsageKind::SuccessionFlow)
                    .map(MemberKind::Usage);
            }
            return self.parse_kerml_succession(prefix).map(MemberKind::Usage);
        }
        if self.eat_kw("flow") {
            return self
                .parse_flow_usage(prefix, UsageKind::Flow)
                .map(MemberKind::Usage);
        }

        // Keyword-less feature.
        if self.at_name()
            || self.at(TokenKind::Lt)
            || self.at(TokenKind::Colon)
            || self.at(TokenKind::ColonGt)
            || self.at(TokenKind::ColonGtGt)
            || self.at(TokenKind::ColonColonGt)
            || self.at(TokenKind::FatArrow)
            || self.at(TokenKind::LBracket)
            || self.at_kw("all")
            || self.at_kw("redefines")
            || self.at_kw("subsets")
            || self.at_kw("references")
            || self.at_kw("crosses")
            || self.at_kw("typed")
            || self.at_kw("ordered")
            || self.at_kw("nonunique")
            || self.at(TokenKind::Eq)
            || self.at(TokenKind::ColonEq)
            || (self.at(TokenKind::Semi) && !metadata.is_empty())
        {
            let kind = if !metadata.is_empty() {
                UsageKind::Extended
            } else {
                UsageKind::Default
            };
            if self.meta_body && kind == UsageKind::Default {
                return self
                    .parse_metadata_body_usage(prefix, kind)
                    .map(MemberKind::Usage);
            }
            return self.parse_usage_rest(prefix, kind).map(MemberKind::Usage);
        }

        if saw_prefix {
            self.error_here(format!(
                "expected a KerML element after prefix, found `{}`",
                self.describe_cur()
            ));
        } else {
            self.error_here(format!(
                "unsupported or unexpected construct at `{}`",
                self.describe_cur()
            ));
        }
        None
    }

    /// KerML `connector` declaration forms.
    fn parse_kerml_connector(&mut self, prefix: UsagePrefix) -> Option<Usage> {
        // A leading sufficiency marker may carry a declaration-less form
        // with the relational keyword optional: `connector all a.x to b.y;`,
        // `connector all from a.x to b.y;`.
        let is_sufficient = self.eat_kw("all");
        let checkpoint = self.pos;
        let diags = self.diags.len();
        let mut declaration = self.parse_feature_declaration();
        declaration.is_sufficient |= is_sufficient;
        let declared = self.at_kw("from")
            || self.at(TokenKind::LParen)
            || self.at(TokenKind::Eq)
            || self.at(TokenKind::ColonEq)
            || self.at_kw("default")
            || self.at(TokenKind::Semi)
            || self.at(TokenKind::LBrace);
        if !declared {
            self.pos = checkpoint;
            self.diags.truncate(diags);
        }
        // Declaration-less binary forms: `connector a.x to b.y;`,
        // `connector [0..1] a to [1..*] b;`
        if !declared {
            self.eat_kw("from");
            let ends = self.parse_connector_part()?;
            return self.finish_usage(
                prefix,
                UsageKind::Connector,
                FeatureDeclaration {
                    is_sufficient,
                    ..Default::default()
                },
                UsageDetail::Connector { ends },
            );
        }
        let value = self.parse_value_part();
        let detail = if self.eat_kw("from") {
            let a = self.parse_connector_end()?;
            self.expect_kw("to");
            let b = self.parse_connector_end()?;
            UsageDetail::Connector { ends: vec![a, b] }
        } else if self.at(TokenKind::LParen) {
            UsageDetail::Connector {
                ends: self.parse_connector_part()?,
            }
        } else {
            UsageDetail::None
        };
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind: UsageKind::Connector,
            declaration,
            detail,
            value,
            is_parallel: false,
            body,
        })
    }

    /// KerML `binding all? b? (of? a = b)?`.
    fn parse_kerml_binding(&mut self, prefix: UsagePrefix) -> Option<Usage> {
        // The sufficiency-marked alternative makes `of` optional:
        // `binding all x = y;`, `binding all of x = y;`.
        let is_sufficient = self.eat_kw("all");
        let checkpoint = self.pos;
        let diags = self.diags.len();
        let mut declaration = self.parse_feature_declaration();
        declaration.is_sufficient |= is_sufficient;
        let declared = self.at_kw("of") || self.at(TokenKind::Semi) || self.at(TokenKind::LBrace);
        if !declared {
            self.pos = checkpoint;
            self.diags.truncate(diags);
            declaration = FeatureDeclaration {
                is_sufficient,
                ..Default::default()
            };
        }
        // A declared binding takes ends only behind `of`; an undeclared
        // one is bare ends. Short-circuit keeps `of` unprobed when
        // undeclared.
        let detail = if !declared || self.eat_kw("of") {
            let a = self.parse_connector_end()?;
            self.expect(TokenKind::Eq, "`=` in binding");
            let b = self.parse_connector_end()?;
            UsageDetail::Binding { ends: vec![a, b] }
        } else {
            UsageDetail::None
        };
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind: UsageKind::Binding,
            declaration,
            detail,
            value: None,
            is_parallel: false,
            body,
        })
    }

    /// KerML `succession s? (all? first? a then b)?`.
    fn parse_kerml_succession(&mut self, prefix: UsagePrefix) -> Option<Usage> {
        let is_sufficient = self.eat_kw("all");
        let checkpoint = self.pos;
        let diags = self.diags.len();
        let mut declaration = self.parse_feature_declaration();
        declaration.is_sufficient |= is_sufficient;
        let declared =
            self.at_kw("first") || self.at(TokenKind::Semi) || self.at(TokenKind::LBrace);
        if !declared {
            self.pos = checkpoint;
            self.diags.truncate(diags);
            declaration = FeatureDeclaration {
                is_sufficient,
                ..Default::default()
            };
        }
        // A declared succession takes ends only behind `first`; an
        // undeclared one is bare ends. Short-circuit keeps `first`
        // unprobed when undeclared.
        let detail = if !declared || self.eat_kw("first") {
            let source = self.parse_connector_end()?;
            self.expect_kw("then");
            let target = self.parse_connector_end()?;
            UsageDetail::Succession {
                source: Some(Box::new(source)),
                target: Box::new(target),
            }
        } else {
            UsageDetail::None
        };
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind: UsageKind::Succession,
            declaration,
            detail,
            value: None,
            is_parallel: false,
            body,
        })
    }

    /// `dependency <id>? from? a, b to c, d ;`
    fn parse_dependency(&mut self, metadata: Vec<QualifiedName>) -> Option<Dependency> {
        self.expect_kw("dependency");
        // `Identification? 'from'` — needs lookahead: a name here is either
        // the dependency's name (if `from` follows) or the first client.
        let mut id = Identification::default();
        if self.at(TokenKind::Lt) {
            id = self.parse_identification();
            self.expect_kw("from");
        } else if self.at_name() {
            let checkpoint = self.pos;
            let name = self.parse_name();
            if self.eat_kw("from") {
                id.name = name;
            } else {
                self.pos = checkpoint;
            }
        } else {
            self.eat_kw("from");
        }
        let mut clients = vec![self.parse_qualified_name()?];
        while self.eat(TokenKind::Comma) {
            clients.push(self.parse_qualified_name()?);
        }
        self.expect_kw("to");
        let mut suppliers = vec![self.parse_qualified_name()?];
        while self.eat(TokenKind::Comma) {
            suppliers.push(self.parse_qualified_name()?);
        }
        if self.eat(TokenKind::LBrace) {
            self.parse_body_members();
            self.expect(TokenKind::RBrace, "`}` closing dependency body");
        } else {
            self.expect_semi("after dependency");
        }
        Some(Dependency {
            metadata,
            id,
            clients,
            suppliers,
        })
    }

    /// `('@' | 'metadata') (<id> :)? Metaclass ('about' e1, e2)? body`,
    /// optionally preceded by `#Meta` prefix metadata (passed in).
    fn parse_metadata_usage(&mut self, metadata: Vec<QualifiedName>) -> Option<Usage> {
        if !self.eat(TokenKind::At) {
            self.expect_kw("metadata");
        }
        let mut declaration = FeatureDeclaration::default();
        // `(Identification (':' | 'defined by'))?` before the metaclass.
        // The identification itself may be empty: `@ : M;`, `@ typed by M;`.
        if (self.at_name()
            && (self.nth(1).kind == TokenKind::Colon
                || self.nth(1).is_kw(self.src, "defined")
                || self.nth(1).is_kw(self.src, "typed")))
            || self.at(TokenKind::Lt)
            || self.at(TokenKind::Colon)
            || (self.at_kw("defined") && self.nth_kw(1, "by"))
            || (self.at_kw("typed") && self.nth_kw(1, "by"))
        {
            declaration.id = self.parse_identification();
            if !self.eat(TokenKind::Colon) {
                if !self.eat_kw("defined") {
                    self.expect_kw("typed");
                }
                self.expect_kw("by");
            }
        }
        let metaclass = self.parse_qualified_name()?;
        declaration
            .specializations
            .push(FeatureSpecialization::TypedBy(vec![TypeRef {
                is_conjugated: false,
                target: TargetRef::Name(metaclass),
            }]));
        let mut about = Vec::new();
        if self.eat_kw("about") {
            loop {
                about.push(self.parse_qualified_name()?);
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
        }
        let body = self.parse_metadata_body_or_semi()?;
        Some(Usage {
            prefix: UsagePrefix {
                metadata,
                ..UsagePrefix::default()
            },
            kind: UsageKind::Metadata,
            declaration,
            detail: UsageDetail::Metadata { about },
            value: None,
            is_parallel: false,
            body,
        })
    }

    /// A `MetadataBodyUsage` / `MetadataBodyFeature` after its optional
    /// keywords: the leading name is an `OwnedRedefinition` target — a
    /// *qualified* name is an implicit redefinition even without a
    /// `:>>`/`redefines` token (both are optional in the grammar). Lowers
    /// identically to the explicit `:>>` spelling. Bare simple names keep
    /// parsing as declarations (existing behavior). The nested body is
    /// itself a `MetadataBody`.
    fn parse_metadata_body_usage(&mut self, prefix: UsagePrefix, kind: UsageKind) -> Option<Usage> {
        let mut declaration = FeatureDeclaration::default();
        if self.at_name() && matches!(self.nth(1).kind, TokenKind::ColonColon | TokenKind::Dot) {
            let target = self.parse_target_ref()?;
            declaration
                .specializations
                .push(FeatureSpecialization::Redefines(vec![target]));
            self.parse_feature_specializations(&mut declaration);
        } else {
            declaration = self.parse_feature_declaration();
        }
        let value = self.parse_value_part();
        let body = self.parse_metadata_body_or_semi()?;
        Some(Usage {
            prefix,
            kind,
            declaration,
            detail: UsageDetail::None,
            value,
            is_parallel: false,
            body,
        })
    }

    fn parse_import(&mut self) -> Option<Import> {
        self.expect_kw("import");
        let is_import_all = self.eat_kw("all");
        let target = self.parse_qualified_name()?;
        let mut is_namespace = false;
        let mut is_recursive = false;
        // `::*` and/or `::**`
        while self.at(TokenKind::ColonColon) {
            match self.nth(1).kind {
                TokenKind::Star => {
                    self.bump();
                    self.bump();
                    is_namespace = true;
                }
                TokenKind::StarStar => {
                    self.bump();
                    self.bump();
                    is_recursive = true;
                    break;
                }
                _ => break,
            }
        }
        // Filter conditions: `[expr]` pairs.
        let mut filters = Vec::new();
        while self.eat(TokenKind::LBracket) {
            if let Some(e) = self.parse_expr() {
                filters.push(e);
            }
            self.expect(TokenKind::RBracket, "`]` closing import filter");
        }
        // Relationship body: `;` or `{ annotations }`.
        if self.eat(TokenKind::LBrace) {
            // Not yet modeled; accept and skip annotations.
            self.parse_body_members();
            self.expect(TokenKind::RBrace, "`}` closing import body");
        } else {
            self.expect_semi("after import");
        }
        Some(Import {
            is_import_all,
            target,
            is_namespace,
            is_recursive,
            filters,
        })
    }

    fn parse_alias(&mut self) -> Option<Alias> {
        self.expect_kw("alias");
        let id = self.parse_identification();
        self.expect_kw("for");
        let target = self.parse_qualified_name()?;
        if self.eat(TokenKind::LBrace) {
            self.parse_body_members();
            self.expect(TokenKind::RBrace, "`}` closing alias body");
        } else {
            self.expect_semi("after alias");
        }
        Some(Alias { id, target })
    }

    fn comment_body(&mut self) -> Option<String> {
        let tok = self.expect(TokenKind::RegularComment, "a `/* ... */` comment body")?;
        let raw = tok.text(self.src);
        let inner = raw
            .strip_prefix("/*")
            .and_then(|s| s.strip_suffix("*/"))
            .unwrap_or(raw);
        Some(inner.to_string())
    }

    fn parse_locale(&mut self) -> Option<String> {
        if self.eat_kw("locale") {
            let tok = self.expect(TokenKind::String, "a locale string")?;
            Some(unescape(tok.text(self.src)))
        } else {
            None
        }
    }

    fn parse_comment(&mut self) -> Option<Comment> {
        let mut id = Identification::default();
        let mut about = Vec::new();
        if self.eat_kw("comment") {
            id = self.parse_identification();
            if self.eat_kw("about") {
                loop {
                    if let Some(qn) = self.parse_qualified_name() {
                        about.push(qn);
                    }
                    if !self.eat(TokenKind::Comma) {
                        break;
                    }
                }
            }
        }
        let locale = self.parse_locale();
        let body = self.comment_body()?;
        Some(Comment {
            id,
            about,
            locale,
            body,
        })
    }

    fn parse_doc(&mut self) -> Option<Doc> {
        self.expect_kw("doc");
        let id = self.parse_identification();
        let locale = self.parse_locale();
        let body = self.comment_body()?;
        Some(Doc { id, locale, body })
    }

    fn parse_textual_rep(&mut self) -> Option<TextualRep> {
        let mut id = Identification::default();
        if self.eat_kw("rep") {
            id = self.parse_identification();
        }
        self.expect_kw("language");
        let lang_tok = self.expect(TokenKind::String, "a language string")?;
        let language = unescape(lang_tok.text(self.src));
        let body = self.comment_body()?;
        Some(TextualRep { id, language, body })
    }

    // ---- definitions and usages ----

    /// Map a keyword to its (definition, usage) kinds. `use case` and
    /// `succession flow` are handled by the caller.
    fn simple_kind(word: &str) -> Option<(Option<DefKind>, Option<UsageKind>)> {
        Some(match word {
            "attribute" => (Some(DefKind::Attribute), Some(UsageKind::Attribute)),
            "enum" => (Some(DefKind::Enum), Some(UsageKind::Enum)),
            "occurrence" => (Some(DefKind::Occurrence), Some(UsageKind::Occurrence)),
            "item" => (Some(DefKind::Item), Some(UsageKind::Item)),
            "metadata" => (Some(DefKind::Metadata), Some(UsageKind::Metadata)),
            "part" => (Some(DefKind::Part), Some(UsageKind::Part)),
            "port" => (Some(DefKind::Port), Some(UsageKind::Port)),
            "connection" => (Some(DefKind::Connection), Some(UsageKind::Connection)),
            "interface" => (Some(DefKind::Interface), Some(UsageKind::Interface)),
            "allocation" => (Some(DefKind::Allocation), Some(UsageKind::Allocation)),
            "flow" => (Some(DefKind::Flow), Some(UsageKind::Flow)),
            "action" => (Some(DefKind::Action), Some(UsageKind::Action)),
            "state" => (Some(DefKind::State), Some(UsageKind::State)),
            "calc" => (Some(DefKind::Calc), Some(UsageKind::Calc)),
            "constraint" => (Some(DefKind::Constraint), Some(UsageKind::Constraint)),
            "requirement" => (Some(DefKind::Requirement), Some(UsageKind::Requirement)),
            "concern" => (Some(DefKind::Concern), Some(UsageKind::Concern)),
            "case" => (Some(DefKind::Case), Some(UsageKind::Case)),
            "analysis" => (Some(DefKind::Analysis), Some(UsageKind::Analysis)),
            "verification" => (Some(DefKind::Verification), Some(UsageKind::Verification)),
            "view" => (Some(DefKind::View), Some(UsageKind::View)),
            "viewpoint" => (Some(DefKind::Viewpoint), Some(UsageKind::Viewpoint)),
            "rendering" => (Some(DefKind::Rendering), Some(UsageKind::Rendering)),
            _ => return None,
        })
    }

    fn at_feature_declaration_start(&self) -> bool {
        self.at_name()
            || self.at(TokenKind::Lt)
            || self.at(TokenKind::LBracket)
            || self.at(TokenKind::Colon)
            || self.at(TokenKind::ColonGt)
            || self.at(TokenKind::ColonGtGt)
            || self.at(TokenKind::ColonColonGt)
            || self.at(TokenKind::FatArrow)
            || self.at(TokenKind::Tilde)
            || self.at_kw("all")
            || self.at_kw("typed")
            || self.at_kw("defined")
            || self.at_kw("specializes")
            || self.at_kw("subsets")
            || self.at_kw("references")
            || self.at_kw("crosses")
            || self.at_kw("redefines")
            || self.at_kw("conjugates")
            || self.at_kw("ordered")
            || self.at_kw("nonunique")
    }

    fn at_sysml_usage_continuation(&self) -> bool {
        self.at(TokenKind::Hash)
            || self.at_feature_declaration_start()
            || (self.at(TokenKind::Ident)
                && (Self::simple_kind(self.cur_text()).is_some()
                    || matches!(
                        self.cur_text(),
                        "ref"
                            | "connect"
                            | "allocate"
                            | "binding"
                            | "bind"
                            | "succession"
                            | "first"
                            | "perform"
                            | "exhibit"
                            | "include"
                            | "event"
                            | "assert"
                            | "satisfy"
                            | "use"
                    )))
    }

    fn parse_definition_or_usage(&mut self) -> Option<MemberKind> {
        self.parse_definition_or_usage_with(Vec::new())
    }

    fn parse_definition_or_usage_with(
        &mut self,
        mut metadata: Vec<QualifiedName>,
    ) -> Option<MemberKind> {
        let mut def_prefix = DefPrefix::default();
        let mut usage_prefix = UsagePrefix::default();
        let mut saw_prefix = !metadata.is_empty();

        // `variant` member prefix (inside variation bodies).
        if self.at_kw("variant") {
            self.bump();
            usage_prefix.is_variant = true;
            saw_prefix = true;
        }

        // Usage prefix chain (order per grammar; each at most once).
        if self.at_kw("in") && !self.nth(1).is_kw(self.src, "def") {
            // NB: `in` is also an expression body parameter intro; here it is
            // only reachable at member start.
            self.bump();
            usage_prefix.direction = Some(FeatureDirection::In);
            saw_prefix = true;
        } else if self.eat_kw("out") {
            usage_prefix.direction = Some(FeatureDirection::Out);
            saw_prefix = true;
        } else if self.eat_kw("inout") {
            usage_prefix.direction = Some(FeatureDirection::InOut);
            saw_prefix = true;
        }
        if self.eat_kw("derived") {
            usage_prefix.is_derived = true;
            saw_prefix = true;
        }
        if self.eat_kw("abstract") {
            def_prefix.is_abstract = true;
            usage_prefix.is_abstract = true;
            saw_prefix = true;
        } else if self.eat_kw("variation") {
            def_prefix.is_variation = true;
            usage_prefix.is_variation = true;
            saw_prefix = true;
        }
        if self.eat_kw("constant") {
            usage_prefix.is_constant = true;
            saw_prefix = true;
        }
        if self.eat_kw("end") {
            usage_prefix.is_end = true;
            saw_prefix = true;
            // Optional cross feature — its own basic prefix plus a
            // declaration, only valid when a kind keyword follows it:
            // `end [0..1] item cart : C;`, `end inCart[0..1] item cart : C;`,
            // `end derived c : Cart part x : X;`.
            if self.at(TokenKind::LBracket)
                || self.at(TokenKind::Lt)
                || self.at_name()
                || self.at_kw("in")
                || self.at_kw("out")
                || self.at_kw("inout")
                || self.at_kw("derived")
                || self.at_kw("abstract")
                || self.at_kw("variation")
                || self.at_kw("constant")
                || self.at_kw("ref")
                || self.at_kw("ordered")
                || self.at_kw("nonunique")
            {
                let checkpoint = self.pos;
                let diags = self.diags.len();
                let mut cross = CrossFeature::default();
                if self.eat_kw("in") {
                    cross.direction = Some(FeatureDirection::In);
                } else if self.eat_kw("out") {
                    cross.direction = Some(FeatureDirection::Out);
                } else if self.eat_kw("inout") {
                    cross.direction = Some(FeatureDirection::InOut);
                }
                if self.eat_kw("derived") {
                    cross.is_derived = true;
                }
                if self.eat_kw("abstract") {
                    cross.is_abstract = true;
                } else if self.eat_kw("variation") {
                    cross.is_variation = true;
                }
                if self.eat_kw("constant") {
                    cross.is_constant = true;
                }
                if self.eat_kw("ref") {
                    cross.is_ref = true;
                }
                cross.decl = self.parse_feature_declaration();
                if !cross.decl.is_empty() && self.at_sysml_usage_continuation() {
                    usage_prefix.end_cross = Some(Box::new(cross));
                } else {
                    self.pos = checkpoint;
                    self.diags.truncate(diags);
                }
            }
        }
        if self.eat_kw("ref") {
            usage_prefix.is_ref = true;
            saw_prefix = true;
        }
        if self.eat_kw("individual") {
            def_prefix.is_individual = true;
            usage_prefix.is_individual = true;
            saw_prefix = true;
        }
        if self.eat_kw("snapshot") {
            usage_prefix.portion = Some(PortionKind::Snapshot);
            saw_prefix = true;
        } else if self.eat_kw("timeslice") {
            usage_prefix.portion = Some(PortionKind::Timeslice);
            saw_prefix = true;
        }

        // `#Meta` extension keywords come after the basic prefixes.
        if self.at(TokenKind::Hash) {
            metadata.extend(self.parse_prefix_metadata());
            saw_prefix = true;
        }
        def_prefix.metadata = metadata.clone();
        usage_prefix.metadata = metadata.clone();

        // `individual def X { ... }` / `#UserKw def X` — definitions with no
        // kind keyword.
        if (def_prefix.is_individual || !metadata.is_empty()) && self.at_kw("def") {
            self.bump();
            let kind = if def_prefix.is_individual {
                DefKind::Individual
            } else {
                DefKind::Extended
            };
            return self
                .parse_definition_rest(def_prefix, kind)
                .map(MemberKind::Definition);
        }

        // `use case [def]`
        if self.at_kw("use") {
            self.bump();
            self.expect_kw("case");
            if self.eat_kw("def") {
                return self
                    .parse_definition_rest(def_prefix, DefKind::UseCase)
                    .map(MemberKind::Definition);
            }
            return self
                .parse_usage_rest(usage_prefix, UsageKind::UseCase)
                .map(MemberKind::Usage);
        }

        // `succession [flow]` / `first a then b` successions.
        if self.at_kw("succession") {
            self.bump();
            if self.eat_kw("flow") {
                return self
                    .parse_flow_usage(usage_prefix, UsageKind::SuccessionFlow)
                    .map(MemberKind::Usage);
            }
            return self
                .parse_succession_rest(usage_prefix)
                .map(MemberKind::Usage);
        }
        if self.at_kw("first") {
            return self
                .parse_succession_rest(usage_prefix)
                .map(MemberKind::Usage);
        }

        // Connector-family standalone keywords.
        if self.at_kw("connect") {
            self.bump();
            let ends = self.parse_connector_part()?;
            return self
                .finish_usage(
                    usage_prefix,
                    UsageKind::Connection,
                    FeatureDeclaration::default(),
                    UsageDetail::Connector { ends },
                )
                .map(MemberKind::Usage);
        }
        if self.at_kw("allocate") {
            self.bump();
            let ends = self.parse_connector_part()?;
            return self
                .finish_usage(
                    usage_prefix,
                    UsageKind::Allocation,
                    FeatureDeclaration::default(),
                    UsageDetail::Connector { ends },
                )
                .map(MemberKind::Usage);
        }
        if self.at_kw("binding") || self.at_kw("bind") {
            let mut declaration = FeatureDeclaration::default();
            if self.eat_kw("binding") {
                declaration = self.parse_feature_declaration();
            }
            self.expect_kw("bind");
            let a = self.parse_connector_end()?;
            self.expect(TokenKind::Eq, "`=` in bind");
            let b = self.parse_connector_end()?;
            return self
                .finish_usage(
                    usage_prefix,
                    UsageKind::Binding,
                    declaration,
                    UsageDetail::Binding { ends: vec![a, b] },
                )
                .map(MemberKind::Usage);
        }
        if self.at_kw("message") {
            self.bump();
            return self
                .parse_flow_usage(usage_prefix, UsageKind::Message)
                .map(MemberKind::Usage);
        }

        // Behavioral composite usages.
        if self.at_kw("perform") {
            self.bump();
            return self
                .parse_ref_or_kind_usage_prefixed(usage_prefix, UsageKind::Perform, "action")
                .map(MemberKind::Usage);
        }
        if self.at_kw("exhibit") {
            self.bump();
            return self
                .parse_ref_or_kind_usage_prefixed(usage_prefix, UsageKind::Exhibit, "state")
                .map(MemberKind::Usage);
        }
        if self.at_kw("include") {
            self.bump();
            let mut declaration = FeatureDeclaration::default();
            if self.eat_kw("use") {
                self.expect_kw("case");
                declaration = self.parse_feature_declaration();
            } else {
                let target = self.parse_target_ref()?;
                declaration
                    .specializations
                    .push(FeatureSpecialization::References(target));
                self.parse_feature_specializations(&mut declaration);
            }
            return self
                .finish_usage(
                    usage_prefix,
                    UsageKind::Include,
                    declaration,
                    UsageDetail::None,
                )
                .map(MemberKind::Usage);
        }
        if self.at_kw("event") {
            self.bump();
            let mut declaration = FeatureDeclaration::default();
            if self.eat_kw("occurrence") {
                declaration = self.parse_feature_declaration();
            } else {
                let target = self.parse_target_ref()?;
                declaration
                    .specializations
                    .push(FeatureSpecialization::References(target));
                self.parse_feature_specializations(&mut declaration);
            }
            return self
                .finish_usage(
                    usage_prefix,
                    UsageKind::Event,
                    declaration,
                    UsageDetail::None,
                )
                .map(MemberKind::Usage);
        }
        if self.at_kw("assert")
            || self.at_kw("satisfy")
            || (self.at_kw("not") && self.nth_kw(1, "satisfy"))
        {
            let asserted = self.eat_kw("assert");
            let negated = self.eat_kw("not");
            if self.eat_kw("satisfy") {
                let mut declaration = FeatureDeclaration::default();
                if self.eat_kw("requirement") {
                    declaration = self.parse_feature_declaration();
                } else {
                    let target = self.parse_target_ref()?;
                    declaration
                        .specializations
                        .push(FeatureSpecialization::References(target));
                    self.parse_feature_specializations(&mut declaration);
                }
                let value = self.parse_value_part();
                let by = if self.eat_kw("by") {
                    Some(self.parse_target_ref()?)
                } else {
                    None
                };
                let body = self.parse_body_or_semi()?;
                return Some(MemberKind::Usage(Usage {
                    prefix: usage_prefix,
                    kind: UsageKind::Satisfy,
                    declaration,
                    detail: UsageDetail::Satisfy {
                        asserted,
                        negated,
                        by,
                    },
                    value,
                    is_parallel: false,
                    body,
                }));
            }
            // `assert [not] [constraint] …`
            let mut declaration = FeatureDeclaration::default();
            if self.eat_kw("constraint") {
                declaration = self.parse_feature_declaration();
            } else {
                let target = self.parse_target_ref()?;
                declaration
                    .specializations
                    .push(FeatureSpecialization::References(target));
                self.parse_feature_specializations(&mut declaration);
            }
            return self
                .finish_usage(
                    usage_prefix,
                    UsageKind::AssertConstraint,
                    declaration,
                    UsageDetail::Assert { negated },
                )
                .map(MemberKind::Usage);
        }

        // Action nodes.
        if self.at_kw("accept") {
            self.bump();
            let detail = self.parse_accept_detail()?;
            return self
                .finish_usage(
                    usage_prefix,
                    UsageKind::Accept,
                    FeatureDeclaration::default(),
                    detail,
                )
                .map(MemberKind::Usage);
        }
        if self.at_kw("send") {
            self.bump();
            return self
                .parse_send_rest(usage_prefix, FeatureDeclaration::default())
                .map(MemberKind::Usage);
        }
        if self.at_kw("assign") {
            self.bump();
            return self
                .parse_assign_rest(usage_prefix, FeatureDeclaration::default())
                .map(MemberKind::Usage);
        }
        if self.at_kw("terminate") {
            self.bump();
            let target = if self.at(TokenKind::Semi) || self.at(TokenKind::LBrace) {
                None
            } else {
                Some(self.parse_expr()?)
            };
            return self
                .finish_usage(
                    usage_prefix,
                    UsageKind::Terminate,
                    FeatureDeclaration::default(),
                    UsageDetail::Terminate {
                        target: target.map(Box::new),
                    },
                )
                .map(MemberKind::Usage);
        }
        if self.at_kw("if") {
            self.bump();
            let cond = self.parse_expr()?;
            return self
                .parse_if_node_rest(usage_prefix, FeatureDeclaration::default(), cond)
                .map(MemberKind::Usage);
        }
        if self.at_kw("while") || self.at_kw("loop") {
            let cond = if self.eat_kw("while") {
                Some(self.parse_expr()?)
            } else {
                self.bump();
                None
            };
            return self
                .parse_while_rest(usage_prefix, FeatureDeclaration::default(), cond)
                .map(MemberKind::Usage);
        }
        if self.at_kw("for") {
            self.bump();
            return self
                .parse_for_rest(usage_prefix, FeatureDeclaration::default())
                .map(MemberKind::Usage);
        }
        for (kw, kind) in [
            ("merge", UsageKind::Merge),
            ("decide", UsageKind::Decide),
            ("join", UsageKind::Join),
            ("fork", UsageKind::Fork),
        ] {
            if self.at_kw(kw) {
                self.bump();
                return self
                    .parse_usage_rest(usage_prefix, kind)
                    .map(MemberKind::Usage);
            }
        }

        // Metadata usage with prefixes (rare; usually caught at member level).
        if self.at(TokenKind::At) || (self.at_kw("metadata") && !self.nth_kw(1, "def")) {
            let mut usage = self.parse_metadata_usage(Vec::new())?;
            usage.prefix = usage_prefix;
            return Some(MemberKind::Usage(usage));
        }

        // Single-keyword kinds.
        if self.at(TokenKind::Ident) {
            if let Some((dk, uk)) = Self::simple_kind(self.cur_text()) {
                self.bump();
                if self.at_kw("def") {
                    self.bump();
                    let dk = dk?;
                    return self
                        .parse_definition_rest(def_prefix, dk)
                        .map(MemberKind::Definition);
                }
                let uk = uk?;
                return self
                    .parse_usage_rest(usage_prefix, uk)
                    .map(MemberKind::Usage);
            }
        }

        // Keyword-less usage: `x : T = v;`, `:>> m = v;`, `ref x;`, or a
        // user-keyword extended usage (`#UserKw x;`).
        if self.at_name()
            || self.at(TokenKind::Lt)
            || self.at(TokenKind::Colon)
            || self.at(TokenKind::ColonGt)
            || self.at(TokenKind::ColonGtGt)
            || self.at(TokenKind::ColonColonGt)
            || self.at(TokenKind::FatArrow)
            || self.at(TokenKind::LBracket)
            || self.at_kw("redefines")
            || self.at_kw("subsets")
            || self.at_kw("references")
            || self.at_kw("crosses")
            || self.at_kw("defined")
            || self.at_kw("default")
            || self.at_kw("ordered")
            || self.at_kw("nonunique")
            || self.at(TokenKind::Eq)
            || self.at(TokenKind::ColonEq)
            || (self.at(TokenKind::Semi) && !metadata.is_empty())
            // After the `ref` keyword the whole usage may be empty:
            // `ref;`, `ref { }`.
            || (usage_prefix.is_ref
                && (self.at(TokenKind::Semi) || self.at(TokenKind::LBrace)))
            // The grammar's empty-reducing Identification permits a usage
            // with no declaration after these prefixes, and an enumerated
            // value may omit both its `enum` keyword and declaration.
            || ((usage_prefix.is_end
                || usage_prefix.is_individual
                || usage_prefix.portion.is_some()
                || usage_prefix.is_variant
                || self.enum_body)
                && (self.at(TokenKind::Semi) || self.at(TokenKind::LBrace)))
        {
            let kind = if !metadata.is_empty() {
                UsageKind::Extended
            } else if usage_prefix.is_individual || usage_prefix.portion.is_some() {
                UsageKind::Occurrence
            } else if usage_prefix.is_ref {
                UsageKind::Ref
            } else {
                UsageKind::Default
            };
            if self.meta_body && matches!(kind, UsageKind::Default | UsageKind::Ref) {
                return self
                    .parse_metadata_body_usage(usage_prefix, kind)
                    .map(MemberKind::Usage);
            }
            return self
                .parse_usage_rest(usage_prefix, kind)
                .map(MemberKind::Usage);
        }

        if saw_prefix {
            self.error_here(format!(
                "expected a definition or usage after prefix, found `{}`",
                self.describe_cur()
            ));
        } else {
            self.error_here(format!(
                "unsupported or unexpected construct at `{}`",
                self.describe_cur()
            ));
        }
        None
    }

    fn parse_target_list(&mut self) -> Vec<TargetRef> {
        let mut targets = Vec::new();
        loop {
            if let Some(t) = self.parse_target_ref() {
                targets.push(t);
            }
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        targets
    }

    fn parse_definition_rest(&mut self, prefix: DefPrefix, kind: DefKind) -> Option<Definition> {
        let kerml = self.dialect == Dialect::Kerml;
        let is_sufficient = kerml && self.eat_kw("all");
        let id = self.parse_identification();
        let multiplicity = if kerml && self.at(TokenKind::LBracket) {
            self.parse_multiplicity()
        } else {
            None
        };
        let mut specializes = Vec::new();
        let mut conjugates = Vec::new();
        if self.eat(TokenKind::ColonGt) || self.eat_kw("specializes") {
            specializes = self.parse_target_list();
        } else if kerml && (self.eat(TokenKind::Tilde) || self.eat_kw("conjugates")) {
            conjugates = self.parse_target_list();
        }
        // KerML type-relationship parts.
        let mut disjoint_from = Vec::new();
        let mut unions = Vec::new();
        let mut intersects = Vec::new();
        let mut differences = Vec::new();
        if kerml {
            loop {
                if self.at_kw("disjoint") {
                    self.bump();
                    self.expect_kw("from");
                    disjoint_from.extend(self.parse_target_list());
                } else if self.eat_kw("unions") {
                    unions.extend(self.parse_target_list());
                } else if self.eat_kw("intersects") {
                    intersects.extend(self.parse_target_list());
                } else if self.eat_kw("differences") {
                    differences.extend(self.parse_target_list());
                } else {
                    break;
                }
            }
        }
        let is_parallel = kind == DefKind::State && self.eat_kw("parallel");
        let body = if kind == DefKind::Enum {
            self.parse_body_or_semi_ctx(false, true)?
        } else {
            self.parse_body_or_semi()?
        };
        Some(Definition {
            prefix,
            kind,
            id,
            specializes,
            is_parallel,
            is_sufficient,
            multiplicity,
            conjugates,
            disjoint_from,
            unions,
            intersects,
            differences,
            body,
        })
    }

    /// Like [`Parser::parse_brace_body`] but distinguishes `None` (a `;`
    /// body) from a parse failure.
    fn parse_body_or_semi(&mut self) -> Option<Option<Vec<Member>>> {
        self.parse_body_or_semi_ctx(false, false)
    }

    /// `MetadataBody`: same surface shape, but members parse in metadata
    /// context (implicit qualified-name redefinitions).
    fn parse_metadata_body_or_semi(&mut self) -> Option<Option<Vec<Member>>> {
        self.parse_body_or_semi_ctx(true, false)
    }

    fn parse_body_or_semi_ctx(
        &mut self,
        meta: bool,
        enum_body: bool,
    ) -> Option<Option<Vec<Member>>> {
        if self.eat(TokenKind::Semi) {
            return Some(None);
        }
        if self.eat(TokenKind::LBrace) {
            let saved = self.meta_body;
            let saved_enum = self.enum_body;
            self.meta_body = meta;
            self.enum_body = enum_body;
            let members = self.parse_body_members();
            self.meta_body = saved;
            self.enum_body = saved_enum;
            self.expect(TokenKind::RBrace, "`}` closing body");
            return Some(Some(members));
        }
        if self.cur_starts_new_line() && self.at_member_start_token() {
            // A missing `;` before a `}` is also the shape of a trailing
            // result expression (`calc c { x }`), which must get first
            // try; fail with eligibility recorded so the member loop can
            // re-parse with the repair armed once that form loses.
            if self.at(TokenKind::RBrace) && self.semi_repair != SemiRepair::Armed {
                self.semi_repair = SemiRepair::Eligible;
                return None;
            }
            if self.repair_missing_semi("at end of declaration") {
                return Some(None);
            }
        }
        self.error_here(format!(
            "expected `;` or `{{`, found `{}`",
            self.describe_cur()
        ));
        None
    }

    fn parse_usage_rest(&mut self, prefix: UsagePrefix, kind: UsageKind) -> Option<Usage> {
        // Flow usages have their own declaration shape.
        if kind == UsageKind::Flow {
            return self.parse_flow_usage(prefix, kind);
        }
        // Interfaces allow a bare end-to-end part (`interface a.x to b.y`).
        if kind == UsageKind::Interface
            && (self.connector_target_ahead() || self.at(TokenKind::LParen))
        {
            let ends = self.parse_connector_part()?;
            return self.finish_usage(
                prefix,
                kind,
                FeatureDeclaration::default(),
                UsageDetail::Connector { ends },
            );
        }

        let declaration = self.parse_feature_declaration();

        // Action nodes may follow a declared action head:
        // `action a1 accept sig : S;`, `action a2 send X() to y;` etc.
        if kind == UsageKind::Action {
            if self.at_kw("accept") {
                self.bump();
                let detail = self.parse_accept_detail()?;
                return self.finish_usage(prefix, UsageKind::Accept, declaration, detail);
            }
            if self.at_kw("send") {
                self.bump();
                return self.parse_send_rest(prefix, declaration);
            }
            if self.at_kw("assign") {
                self.bump();
                return self.parse_assign_rest(prefix, declaration);
            }
            if self.at_kw("if") {
                self.bump();
                let cond = self.parse_expr()?;
                return self.parse_if_node_rest(prefix, declaration, cond);
            }
            if self.at_kw("while") || self.at_kw("loop") {
                let cond = if self.eat_kw("while") {
                    Some(self.parse_expr()?)
                } else {
                    self.bump();
                    None
                };
                return self.parse_while_rest(prefix, declaration, cond);
            }
            if self.at_kw("for") {
                self.bump();
                return self.parse_for_rest(prefix, declaration);
            }
            if self.at_kw("terminate") {
                self.bump();
                let target = if self.at(TokenKind::Semi) || self.at(TokenKind::LBrace) {
                    None
                } else {
                    Some(self.parse_expr()?)
                };
                return self.finish_usage(
                    prefix,
                    UsageKind::Terminate,
                    declaration,
                    UsageDetail::Terminate {
                        target: target.map(Box::new),
                    },
                );
            }
        }

        let value = self.parse_value_part();

        // Connector parts after the declaration (and value).
        let connect_kw = match kind {
            UsageKind::Connection | UsageKind::Interface => "connect",
            UsageKind::Allocation => "allocate",
            _ => "",
        };
        let mut detail = UsageDetail::None;
        if !connect_kw.is_empty() && self.eat_kw(connect_kw) {
            detail = UsageDetail::Connector {
                ends: self.parse_connector_part()?,
            };
        }

        let is_parallel = kind == UsageKind::State && self.eat_kw("parallel");
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind,
            declaration,
            detail,
            value,
            is_parallel,
            body,
        })
    }

    /// Parse `value? body` and build the usage (shared tail).
    fn finish_usage(
        &mut self,
        prefix: UsagePrefix,
        kind: UsageKind,
        declaration: FeatureDeclaration,
        detail: UsageDetail,
    ) -> Option<Usage> {
        let value = self.parse_value_part();
        let is_parallel =
            matches!(kind, UsageKind::State | UsageKind::Exhibit) && self.eat_kw("parallel");
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind,
            declaration,
            detail,
            value,
            is_parallel,
            body,
        })
    }

    /// Reference form (`perform a.b spec*`) or kind form (`perform action x`),
    /// with usage prefixes.
    fn parse_ref_or_kind_usage_prefixed(
        &mut self,
        prefix: UsagePrefix,
        kind: UsageKind,
        kind_kw: &str,
    ) -> Option<Usage> {
        let mut declaration = FeatureDeclaration::default();
        if self.eat_kw(kind_kw) {
            declaration = self.parse_feature_declaration();
        } else {
            let target = self.parse_target_ref()?;
            declaration
                .specializations
                .push(FeatureSpecialization::References(target));
            self.parse_feature_specializations(&mut declaration);
        }
        self.finish_usage(prefix, kind, declaration, UsageDetail::None)
    }

    /// `('succession' already consumed) decl? 'first' src ('if' g)? 'then'
    /// tgt body` — a succession or guarded succession.
    fn parse_succession_rest(&mut self, prefix: UsagePrefix) -> Option<Usage> {
        let declaration = self.parse_feature_declaration();
        self.expect_kw("first");
        let source = self.parse_connector_end()?;
        if self.eat_kw("if") {
            let guard = self.parse_expr()?;
            self.expect_kw("then");
            let target = self.parse_connector_end()?;
            let body = self.parse_body_or_semi()?;
            return Some(Usage {
                prefix,
                kind: UsageKind::Transition,
                declaration,
                detail: UsageDetail::Transition {
                    source: Some(source.target),
                    trigger: None,
                    guard: Some(Box::new(guard)),
                    effect: None,
                    target: Some(Box::new(target)),
                    is_default: false,
                },
                value: None,
                is_parallel: false,
                body,
            });
        }
        self.expect_kw("then");
        let target = self.parse_connector_end()?;
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind: UsageKind::Succession,
            declaration,
            detail: UsageDetail::Succession {
                source: Some(Box::new(source)),
                target: Box::new(target),
            },
            value: None,
            is_parallel: false,
            body,
        })
    }

    /// Flow / succession-flow / message declaration and body.
    fn parse_flow_usage(&mut self, prefix: UsagePrefix, kind: UsageKind) -> Option<Usage> {
        // KerML sufficiency-marked declaration-less form: `flow all a.x to b.y;`
        let is_sufficient = self.dialect == Dialect::Kerml && self.eat_kw("all");
        // End-to-end shorthand: `flow a.x to b.y;`
        if self.connector_target_ahead() {
            let source = FlowEnd {
                target: self.parse_target_ref()?,
            };
            self.expect_kw("to");
            let target = FlowEnd {
                target: self.parse_target_ref()?,
            };
            let body = self.parse_body_or_semi()?;
            return Some(Usage {
                prefix,
                kind,
                declaration: FeatureDeclaration {
                    is_sufficient,
                    ..Default::default()
                },
                detail: UsageDetail::Flow {
                    payload: None,
                    source: Some(source),
                    target: Some(target),
                },
                value: None,
                is_parallel: false,
                body,
            });
        }
        let mut declaration = self.parse_feature_declaration();
        declaration.is_sufficient |= is_sufficient;
        let value = self.parse_value_part();
        let payload = if self.eat_kw("of") {
            Some(self.parse_payload_part(PayloadContext::Flow)?)
        } else {
            None
        };
        let (source, target) = if self.eat_kw("from") {
            let s = FlowEnd {
                target: self.parse_target_ref()?,
            };
            self.expect_kw("to");
            let t = FlowEnd {
                target: self.parse_target_ref()?,
            };
            (Some(s), Some(t))
        } else {
            (None, None)
        };
        let detail = if payload.is_some() || source.is_some() {
            UsageDetail::Flow {
                payload: payload.map(Box::new),
                source,
                target,
            }
        } else {
            UsageDetail::None
        };
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind,
            declaration,
            detail,
            value,
            is_parallel: false,
            body,
        })
    }

    /// Does a `<qualified-or-chained-name> to` sequence start here (the
    /// end-to-end shorthand of flows/interfaces/messages)?
    fn connector_target_ahead(&self) -> bool {
        let mut i = 0;
        // Interface parts may begin with an owned cross multiplicity on the
        // first end: `interface [1] a to b;`. Skip that group before looking
        // for the target and separating `to` keyword.
        if self.nth(i).kind == TokenKind::LBracket {
            let mut depth = 0i32;
            loop {
                match self.nth(i).kind {
                    TokenKind::LBracket => depth += 1,
                    TokenKind::RBracket => {
                        depth -= 1;
                        if depth == 0 {
                            i += 1;
                            break;
                        }
                    }
                    TokenKind::Eof => return false,
                    _ => {}
                }
                i += 1;
                if i > 64 {
                    return false;
                }
            }
        }
        let mut saw_name = false;
        loop {
            let t = self.nth(i);
            match t.kind {
                TokenKind::Ident => {
                    let text = t.text(self.src);
                    if self.is_reserved_word(text) {
                        return saw_name && text == "to";
                    }
                    saw_name = true;
                }
                TokenKind::UnrestrictedName => saw_name = true,
                TokenKind::Dot | TokenKind::ColonColon | TokenKind::Dollar => {}
                _ => return false,
            }
            i += 1;
            if i > 64 {
                return false;
            }
        }
    }

    /// One connector end: `([mult])? (name ::>)? target`
    fn parse_connector_end(&mut self) -> Option<ConnectorEnd> {
        let multiplicity = if self.at(TokenKind::LBracket) {
            self.parse_multiplicity()
        } else {
            None
        };
        let name = if self.at_name()
            && (self.nth(1).kind == TokenKind::ColonColonGt
                || self.nth(1).is_kw(self.src, "references"))
        {
            let n = self.parse_name();
            self.bump(); // ::> / references
            n
        } else {
            None
        };
        let target = self.parse_target_ref()?;
        Some(ConnectorEnd {
            multiplicity,
            name,
            target,
        })
    }

    /// Binary (`a to b`) or n-ary (`(a, b, c)`) connector part.
    fn parse_connector_part(&mut self) -> Option<Vec<ConnectorEnd>> {
        if self.eat(TokenKind::LParen) {
            let mut ends = vec![self.parse_connector_end()?];
            self.expect(TokenKind::Comma, "`,` between connector ends")?;
            ends.push(self.parse_connector_end()?);
            while self.eat(TokenKind::Comma) {
                ends.push(self.parse_connector_end()?);
            }
            self.expect(TokenKind::RParen, "`)` closing connector ends");
            return Some(ends);
        }
        let a = self.parse_connector_end()?;
        self.expect_kw("to");
        let b = self.parse_connector_end()?;
        Some(vec![a, b])
    }

    /// Payload of `of` clauses and accept actions: either a bare type
    /// reference or a declared feature (`name : Type [mult] = value`).
    /// At a `[` following a payload identification: does a
    /// specialization or value part follow the bracket group? Only then
    /// does the multiplicity belong to the declared name (see the
    /// comment at the call site).
    fn payload_mult_then_declaration(&self) -> bool {
        let mut i = 0usize;
        let mut depth = 0i32;
        loop {
            match self.nth(i).kind {
                TokenKind::LBracket => depth += 1,
                TokenKind::RBracket => {
                    depth -= 1;
                    if depth == 0 {
                        break;
                    }
                }
                TokenKind::Eof => return false,
                _ => {}
            }
            i += 1;
            if i > 64 {
                return false;
            }
        }
        let next = self.nth(i + 1);
        matches!(
            next.kind,
            TokenKind::Colon
                | TokenKind::ColonGt
                | TokenKind::ColonGtGt
                | TokenKind::ColonColonGt
                | TokenKind::FatArrow
                | TokenKind::Eq
                | TokenKind::ColonEq
        ) || next.is_kw(self.src, "defined")
            || next.is_kw(self.src, "default")
    }

    fn parse_payload_part(&mut self, context: PayloadContext) -> Option<PayloadPart> {
        let payload = self.parse_payload_part_inner()?;
        if context == PayloadContext::Flow
            && !payload.specializations.iter().any(
                |spec| matches!(spec, FeatureSpecialization::TypedBy(types) if !types.is_empty()),
            )
        {
            self.error_here("a flow payload requires a type".to_string());
            return None;
        }
        Some(payload)
    }

    fn parse_payload_part_inner(&mut self) -> Option<PayloadPart> {
        let mut payload = PayloadPart::default();
        if self.at(TokenKind::LBracket) {
            // `[mult] Type`, or a multiplicity part followed by declaration
            // markers/specializations (`[1] ordered : T`).
            payload.multiplicity = self.parse_multiplicity();
            if self.at_kw("ordered")
                || self.at_kw("nonunique")
                || self.at(TokenKind::Colon)
                || self.at(TokenKind::ColonGt)
                || self.at(TokenKind::ColonGtGt)
                || self.at(TokenKind::ColonColonGt)
                || self.at(TokenKind::FatArrow)
                || self.at_kw("typed")
                || self.at_kw("subsets")
                || self.at_kw("redefines")
                || self.at_kw("references")
                || self.at_kw("crosses")
            {
                let mut decl = FeatureDeclaration {
                    multiplicity: payload.multiplicity.take(),
                    ..Default::default()
                };
                self.parse_feature_specializations(&mut decl);
                if decl.specializations.is_empty() {
                    self.error_here(
                        "a payload multiplicity part must be followed by a specialization"
                            .to_string(),
                    );
                    return None;
                }
                payload.specializations = decl.specializations;
                payload.multiplicity = decl.multiplicity;
                payload.is_ordered = decl.is_ordered;
                payload.is_nonunique = decl.is_nonunique;
                payload.value = self.parse_value_part();
                return Some(payload);
            }
            let target = self.parse_target_ref()?;
            payload
                .specializations
                .push(FeatureSpecialization::TypedBy(vec![TypeRef {
                    is_conjugated: false,
                    target,
                }]));
            return Some(payload);
        }
        if self.at_name() || self.at(TokenKind::Lt) {
            let checkpoint = self.pos;
            let id = self.parse_identification();
            // A `[` after the name is *not* declaration evidence by
            // itself: the grammar's `Payload` fragment allows a bare
            // `Type [mult]` (OwnedFeatureTyping OwnedMultiplicity?),
            // while a declared name takes a multiplicity only with
            // specializations or a value after it (`Identification?
            // MultiplicityPart FeatureSpecialization+`). `of Publish[1]`
            // is a typing, `of p [1] : Publish` a declaration.
            let declared = self.at(TokenKind::Colon)
                || self.at(TokenKind::ColonGt)
                || self.at(TokenKind::ColonGtGt)
                || self.at(TokenKind::ColonColonGt)
                || self.at(TokenKind::FatArrow)
                || (self.at(TokenKind::LBracket) && self.payload_mult_then_declaration())
                || self.at(TokenKind::Eq)
                || self.at(TokenKind::ColonEq)
                || self.at_kw("defined")
                || self.at_kw("default");
            if !declared {
                // Bare type reference: `of Fuel`.
                self.pos = checkpoint;
                let target = self.parse_target_ref()?;
                payload
                    .specializations
                    .push(FeatureSpecialization::TypedBy(vec![TypeRef {
                        is_conjugated: false,
                        target,
                    }]));
                if self.at(TokenKind::LBracket) {
                    payload.multiplicity = self.parse_multiplicity();
                }
                return Some(payload);
            }
            payload.id = id;
        }
        let mut decl = FeatureDeclaration::default();
        self.parse_feature_specializations(&mut decl);
        payload.specializations = decl.specializations;
        payload.multiplicity = payload.multiplicity.take().or(decl.multiplicity);
        payload.is_ordered = decl.is_ordered;
        payload.is_nonunique = decl.is_nonunique;
        if (payload.is_ordered || payload.is_nonunique) && payload.specializations.is_empty() {
            self.error_here(
                "a payload multiplicity part must be followed by a specialization".to_string(),
            );
            return None;
        }
        payload.value = self.parse_value_part();
        if payload.id.is_empty()
            && payload.specializations.is_empty()
            && payload.multiplicity.is_none()
            && payload.value.is_none()
        {
            self.error_here("a payload requires a type, specialization, or value".to_string());
            return None;
        }
        Some(payload)
    }

    /// After `accept`: `payload? trigger? ('via' expr)?`
    fn parse_accept_detail(&mut self) -> Option<UsageDetail> {
        let mut payload = PayloadPart::default();
        if !(self.at_kw("at") || self.at_kw("after") || self.at_kw("when")) {
            // A following TriggerValuePart selects PayloadParameter's
            // identification-first alternative. Without this contextual
            // evidence the same bare name is PayloadFeature typing.
            let checkpoint = self.pos;
            let diags = self.diags.len();
            let mut declaration = FeatureDeclaration {
                id: self.parse_identification(),
                ..Default::default()
            };
            self.parse_feature_specializations(&mut declaration);
            if self.at_kw("at") || self.at_kw("after") || self.at_kw("when") {
                payload.id = declaration.id;
                payload.specializations = declaration.specializations;
                payload.multiplicity = declaration.multiplicity;
                payload.is_ordered = declaration.is_ordered;
                payload.is_nonunique = declaration.is_nonunique;
            } else {
                self.pos = checkpoint;
                self.diags.truncate(diags);
                payload = self.parse_payload_part(PayloadContext::Accept)?;
            }
        }
        let trigger = if self.at_kw("at") || self.at_kw("after") || self.at_kw("when") {
            let kind = if self.at_kw("at") {
                TriggerKind::At
            } else if self.at_kw("after") {
                TriggerKind::After
            } else {
                TriggerKind::When
            };
            self.bump();
            let expr = self.parse_expr()?;
            Some(Trigger { kind, expr })
        } else {
            None
        };
        let via = if self.eat_kw("via") {
            Some(self.parse_expr()?)
        } else {
            None
        };
        Some(UsageDetail::Accept {
            payload: Box::new(payload),
            trigger: trigger.map(Box::new),
            via: via.map(Box::new),
        })
    }

    /// After `send`: `expr? ('via' expr)? ('to' expr)?`
    fn parse_send_parts(&mut self) -> Option<(Option<Expr>, Option<Expr>, Option<Expr>)> {
        let payload = if self.at(TokenKind::Semi)
            || self.at(TokenKind::LBrace)
            || self.at_kw("via")
            || self.at_kw("to")
        {
            None
        } else {
            Some(self.parse_expr()?)
        };
        let via = if self.eat_kw("via") {
            Some(self.parse_expr()?)
        } else {
            None
        };
        let to = if self.eat_kw("to") {
            Some(self.parse_expr()?)
        } else {
            None
        };
        Some((payload, via, to))
    }

    fn parse_send_rest(
        &mut self,
        prefix: UsagePrefix,
        declaration: FeatureDeclaration,
    ) -> Option<Usage> {
        let (payload, via, to) = self.parse_send_parts()?;
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind: UsageKind::Send,
            declaration,
            detail: UsageDetail::Send {
                payload: payload.map(Box::new),
                via: via.map(Box::new),
                to: to.map(Box::new),
            },
            value: None,
            is_parallel: false,
            body,
        })
    }

    fn parse_assign_rest(
        &mut self,
        prefix: UsagePrefix,
        declaration: FeatureDeclaration,
    ) -> Option<Usage> {
        let target = self.parse_primary()?;
        self.expect(TokenKind::ColonEq, "`:=` in assignment");
        let value = self.parse_expr()?;
        let body = self.parse_body_or_semi()?;
        Some(Usage {
            prefix,
            kind: UsageKind::Assign,
            declaration,
            detail: UsageDetail::Assign {
                target: Box::new(target),
                value: Box::new(value),
            },
            value: None,
            is_parallel: false,
            body,
        })
    }

    /// `('action' decl?)? '{' items '}'` — an anonymous action body used by
    /// if/while/for nodes.
    fn parse_action_body_parameter(&mut self) -> Option<Usage> {
        let mut declaration = FeatureDeclaration::default();
        if self.eat_kw("action") {
            declaration = self.parse_feature_declaration();
        }
        let body = self.parse_brace_body()?;
        Some(Usage {
            prefix: UsagePrefix::default(),
            kind: UsageKind::Action,
            declaration,
            detail: UsageDetail::None,
            value: None,
            is_parallel: false,
            body: Some(body),
        })
    }

    /// Just after `else`: does a nested if-node follow rather than an
    /// anonymous action body? An if-node reaches its `if` keyword before any
    /// body brace, however it is prefixed (`else if`, `else action a if`,
    /// `else #Meta if`); an action-body parameter reaches the brace first.
    /// Type arguments are balanced so an `if` inside a declaration's
    /// parenthesised or bracketed parts does not count.
    fn else_starts_if_node(&self) -> bool {
        let mut i = 0;
        let mut depth = 0i32;
        loop {
            let t = self.nth(i);
            match t.kind {
                TokenKind::Eof => return false,
                TokenKind::LBrace | TokenKind::RBrace | TokenKind::Semi if depth == 0 => {
                    return false;
                }
                TokenKind::LParen | TokenKind::LBracket => depth += 1,
                TokenKind::RParen | TokenKind::RBracket if depth > 0 => depth -= 1,
                TokenKind::Ident if depth == 0 && t.is_kw(self.src, "if") => return true,
                _ => {}
            }
            i += 1;
        }
    }

    /// After `if <cond>` where an action body follows.
    fn parse_if_node_rest(
        &mut self,
        prefix: UsagePrefix,
        declaration: FeatureDeclaration,
        cond: Expr,
    ) -> Option<Usage> {
        let then_body = Box::new(self.parse_action_body_parameter()?);
        let else_body = if self.eat_kw("else") {
            // Both alternatives may start with `action`: an action-body
            // parameter, or a nested if-node carrying its full action node
            // prefix. The `if` keyword that a nested node must reach before
            // its body brace decides between them, so the alternative is
            // chosen before parsing — parsing the branch speculatively and
            // rolling back would re-parse every nested `else action { … }`
            // level once per level.
            if self.else_starts_if_node() {
                let checkpoint = self.pos;
                let diags = self.diags.len();
                // An else-if nests an action without an enclosing body.
                // Charge this edge too, before entering its parser frames.
                if self.depth >= MAX_NESTING {
                    self.refuse_deeper(format!(
                        "nesting is too deep (more than {MAX_NESTING} levels of bodies and expressions)"
                    ));
                    return None;
                }
                self.depth += 1;
                let nested = self.parse_definition_or_usage();
                self.depth -= 1;
                match nested {
                    None => return None,
                    Some(MemberKind::Usage(u)) if u.kind == UsageKind::IfNode => Some(Box::new(u)),
                    _ => {
                        self.pos = checkpoint;
                        self.diags.truncate(diags);
                        Some(Box::new(self.parse_action_body_parameter()?))
                    }
                }
            } else {
                Some(Box::new(self.parse_action_body_parameter()?))
            }
        } else {
            None
        };
        // If-nodes terminate with their closing brace (no `;`), but accept a
        // stray one for robustness.
        self.eat(TokenKind::Semi);
        Some(Usage {
            prefix,
            kind: UsageKind::IfNode,
            declaration,
            detail: UsageDetail::IfNode {
                cond: Box::new(cond),
                then_body,
                else_body,
            },
            value: None,
            is_parallel: false,
            body: None,
        })
    }

    fn parse_while_rest(
        &mut self,
        prefix: UsagePrefix,
        declaration: FeatureDeclaration,
        cond: Option<Expr>,
    ) -> Option<Usage> {
        let body = Box::new(self.parse_action_body_parameter()?);
        let until = if self.eat_kw("until") {
            let e = self.parse_expr()?;
            self.expect_semi("after `until` condition");
            Some(e)
        } else {
            self.eat(TokenKind::Semi);
            None
        };
        Some(Usage {
            prefix,
            kind: UsageKind::WhileLoop,
            declaration,
            detail: UsageDetail::WhileLoop {
                cond: cond.map(Box::new),
                body,
                until: until.map(Box::new),
            },
            value: None,
            is_parallel: false,
            body: None,
        })
    }

    fn parse_for_rest(
        &mut self,
        prefix: UsagePrefix,
        declaration: FeatureDeclaration,
    ) -> Option<Usage> {
        let var = self.parse_feature_declaration();
        self.expect_kw("in");
        let seq = self.parse_expr()?;
        let body = Box::new(self.parse_action_body_parameter()?);
        self.eat(TokenKind::Semi);
        Some(Usage {
            prefix,
            kind: UsageKind::ForLoop,
            declaration,
            detail: UsageDetail::ForLoop {
                var: Box::new(var),
                seq: Box::new(seq),
                body,
            },
            value: None,
            is_parallel: false,
            body: None,
        })
    }

    fn parse_feature_declaration(&mut self) -> FeatureDeclaration {
        let mut decl = FeatureDeclaration::default();
        if self.dialect == Dialect::Kerml {
            decl.is_sufficient = self.eat_kw("all");
        }
        decl.id = self.parse_identification();
        self.parse_feature_specializations(&mut decl);
        decl
    }

    fn parse_feature_specializations(&mut self, decl: &mut FeatureDeclaration) {
        let kerml = self.dialect == Dialect::Kerml;
        loop {
            if self.at(TokenKind::Colon)
                || (self.at_kw("defined") && self.nth_kw(1, "by"))
                || (kerml && self.at_kw("typed") && self.nth_kw(1, "by"))
            {
                if self.at(TokenKind::Colon) {
                    self.bump();
                } else {
                    self.bump();
                    self.bump();
                }
                let mut types = Vec::new();
                loop {
                    let is_conjugated = self.eat(TokenKind::Tilde);
                    if let Some(target) = self.parse_target_ref() {
                        types.push(TypeRef {
                            is_conjugated,
                            target,
                        });
                    }
                    if !self.eat(TokenKind::Comma) {
                        break;
                    }
                }
                decl.specializations
                    .push(FeatureSpecialization::TypedBy(types));
            } else if self.at(TokenKind::ColonGt) || self.at_kw("subsets") {
                self.bump();
                let mut targets = Vec::new();
                loop {
                    if let Some(t) = self.parse_target_ref() {
                        targets.push(t);
                    }
                    if !self.eat(TokenKind::Comma) {
                        break;
                    }
                }
                decl.specializations
                    .push(FeatureSpecialization::Subsets(targets));
            } else if self.at(TokenKind::ColonGtGt) || self.at_kw("redefines") {
                self.bump();
                let mut targets = Vec::new();
                loop {
                    if let Some(t) = self.parse_target_ref() {
                        targets.push(t);
                    }
                    if !self.eat(TokenKind::Comma) {
                        break;
                    }
                }
                decl.specializations
                    .push(FeatureSpecialization::Redefines(targets));
            } else if self.at(TokenKind::ColonColonGt) || self.at_kw("references") {
                self.bump();
                if let Some(t) = self.parse_target_ref() {
                    decl.specializations
                        .push(FeatureSpecialization::References(t));
                }
            } else if self.at(TokenKind::FatArrow) || self.at_kw("crosses") {
                self.bump();
                if let Some(t) = self.parse_target_ref() {
                    decl.specializations.push(FeatureSpecialization::Crosses(t));
                }
            } else if self.at(TokenKind::LBracket) && decl.multiplicity.is_none() {
                decl.multiplicity = self.parse_multiplicity();
                // `ordered` / `nonunique`, either order.
                loop {
                    if self.eat_kw("ordered") {
                        decl.is_ordered = true;
                    } else if self.eat_kw("nonunique") {
                        decl.is_nonunique = true;
                    } else {
                        break;
                    }
                }
            } else if self.at_kw("ordered") || self.at_kw("nonunique") {
                // Ordering markers are also legal without a multiplicity.
                loop {
                    if self.eat_kw("ordered") {
                        decl.is_ordered = true;
                    } else if self.eat_kw("nonunique") {
                        decl.is_nonunique = true;
                    } else {
                        break;
                    }
                }
            } else if kerml && (self.at(TokenKind::Tilde) || self.at_kw("conjugates")) {
                self.bump();
                decl.conjugates = self.parse_target_ref();
            } else if kerml && self.at_kw("chains") {
                self.bump();
                decl.chains = self.parse_target_ref();
            } else if kerml && self.at_kw("inverse") {
                self.bump();
                self.expect_kw("of");
                decl.inverse_of = self.parse_target_ref();
            } else if kerml && self.at_kw("featured") {
                self.bump();
                self.expect_kw("by");
                decl.featured_by.extend(self.parse_target_list());
            } else if kerml && self.at_kw("disjoint") {
                self.bump();
                self.expect_kw("from");
                decl.disjoint_from.extend(self.parse_target_list());
            } else if kerml && self.at_kw("unions") {
                self.bump();
                decl.unions.extend(self.parse_target_list());
            } else if kerml && self.at_kw("intersects") {
                self.bump();
                decl.intersects.extend(self.parse_target_list());
            } else if kerml && self.at_kw("differences") {
                self.bump();
                decl.differences.extend(self.parse_target_list());
            } else {
                break;
            }
        }
    }

    /// Boxed: a multiplicity holds two expressions inline, and every
    /// declaration that can carry one would otherwise pay for them.
    fn parse_multiplicity(&mut self) -> Option<Box<Multiplicity>> {
        let start = self.cur().span;
        self.expect(TokenKind::LBracket, "`[`")?;
        let Some(first) = self.parse_mult_bound() else {
            self.recover_to_rbracket();
            return None;
        };
        let (lower, upper) = if self.eat(TokenKind::DotDot) {
            let Some(upper) = self.parse_mult_bound() else {
                self.recover_to_rbracket();
                return None;
            };
            (Some(first), upper)
        } else {
            (None, first)
        };
        let end = self.cur().span;
        self.expect(TokenKind::RBracket, "`]` closing multiplicity");
        Some(Box::new(Multiplicity {
            lower,
            upper,
            span: start.join(end),
        }))
    }

    /// After a malformed multiplicity bound, skip to (and past) the `]`
    /// closing the multiplicity so the member keeps parsing with one
    /// diagnostic instead of a cascade. Stops at member boundaries.
    fn recover_to_rbracket(&mut self) {
        let mut depth = 0i32;
        while !self.at_eof() {
            match self.cur().kind {
                TokenKind::LBracket => depth += 1,
                TokenKind::RBracket => {
                    if depth == 0 {
                        self.bump();
                        return;
                    }
                    depth -= 1;
                }
                TokenKind::Semi | TokenKind::LBrace | TokenKind::RBrace => return,
                _ => {}
            }
            self.bump();
        }
    }

    /// Multiplicity bounds are restricted by the grammar to literal
    /// expressions or feature references (not general expressions).
    fn parse_mult_bound(&mut self) -> Option<Expr> {
        let start = self.cur().span;
        if self.at(TokenKind::Star) {
            self.bump();
            return Some(Expr {
                kind: ExprKind::Literal(Literal::Infinity),
                span: start,
            });
        }
        if self.at(TokenKind::Decimal) || self.at(TokenKind::Exp) || self.at(TokenKind::Dot) {
            return self.parse_number(start);
        }
        if self.at_kw("true") || self.at_kw("false") {
            let value = self.at_kw("true");
            self.bump();
            return Some(Expr {
                kind: ExprKind::Literal(Literal::Bool(value)),
                span: start,
            });
        }
        if self.at(TokenKind::String) {
            let tok = self.bump();
            return Some(Expr {
                kind: ExprKind::Literal(Literal::String(unescape(tok.text(self.src)))),
                span: start,
            });
        }
        if self.at_name() || self.at(TokenKind::Dollar) {
            let qn = self.parse_qualified_name()?;
            return Some(Expr {
                span: qn.span,
                kind: ExprKind::Ref(qn),
            });
        }
        // Interop: real-world models write
        // cardinality choices as a parenthesized sequence — `[(1, 2)]`,
        // `[(0, 2, 4)]`. Parenthesizing keeps `..` unambiguous, so accept
        // any parenthesized expression as a bound.
        if self.at(TokenKind::LParen) {
            self.bump();
            let expr = self.parse_sequence_expr()?;
            let end = self.cur().span;
            self.expect(TokenKind::RParen, "`)` closing multiplicity bound")?;
            return Some(Expr {
                span: start.join(end),
                kind: expr.kind,
            });
        }
        self.error_here(format!(
            "expected a multiplicity bound (literal or feature name), found `{}`",
            self.describe_cur()
        ));
        None
    }

    /// Boxed: a feature value holds an expression inline, and every
    /// usage carries the slot whether or not it has a value.
    fn parse_value_part(&mut self) -> Option<Box<FeatureValue>> {
        let kind = if self.eat(TokenKind::Eq) {
            ValueKind::Bound
        } else if self.eat(TokenKind::ColonEq) {
            ValueKind::Initial
        } else if self.eat_kw("default") {
            if self.eat(TokenKind::ColonEq) {
                ValueKind::DefaultInitial
            } else {
                self.eat(TokenKind::Eq);
                ValueKind::Default
            }
        } else {
            return None;
        };
        let expr = self.parse_expr()?;
        Some(Box::new(FeatureValue { kind, expr }))
    }

    // ---- expressions (KerML Expressions grammar, precedence climbing) ----

    pub(crate) fn parse_expr(&mut self) -> Option<Expr> {
        self.descend(Self::parse_conditional)
    }

    /// Take one expression-nesting step, running `parse` one level down.
    ///
    /// Every recursive expression path goes through here, so the bound is
    /// charged wherever the parser descends — including the
    /// right-associative exponentiation recursion, which does not return
    /// through [`Self::parse_expr`].
    fn descend(&mut self, parse: fn(&mut Self) -> Option<Expr>) -> Option<Expr> {
        if self.depth >= MAX_NESTING {
            self.refuse_deeper(format!(
                "nesting is too deep (more than {MAX_NESTING} levels of bodies and expressions)"
            ));
            return None;
        }
        if self.expr_frames == 0 {
            self.expr_chain = 0;
        }
        self.depth += 1;
        self.expr_frames += 1;
        let expr = parse(self);
        self.expr_frames -= 1;
        self.depth -= 1;
        expr
    }

    /// Report that the parser will not take this expression any further,
    /// and abandon the rest of it.
    ///
    /// One diagnostic per truncated subtree, as on the body path: the text
    /// that will not be parsed is consumed here, so it does not reach the
    /// member loop as a run of stray tokens each reported again.
    fn refuse_deeper(&mut self, message: String) {
        self.error_here(message);
        self.skip_to_member_end();
    }

    /// Consume the rest of the current member, leaving its `;` — or the
    /// closing brace of the enclosing body — for the caller. Brackets and
    /// parentheses opened before this point were consumed by the frames
    /// being abandoned, so a closer with no opener here belongs to the
    /// abandoned text.
    fn skip_to_member_end(&mut self) {
        let mut depth = 0i32;
        while !self.at_eof() {
            match self.cur().kind {
                TokenKind::Semi if depth == 0 => return,
                TokenKind::RBrace if depth == 0 => return,
                TokenKind::LBrace | TokenKind::LBracket | TokenKind::LParen => depth += 1,
                TokenKind::RBrace | TokenKind::RBracket | TokenKind::RParen => {
                    depth = (depth - 1).max(0);
                }
                _ => {}
            }
            self.bump();
        }
    }

    fn parse_conditional(&mut self) -> Option<Expr> {
        if self.at_kw("if") {
            let start = self.cur().span;
            self.bump();
            let cond = self.branch(Self::parse_null_coalescing)?;
            self.expect(TokenKind::Question, "`?` in conditional expression");
            let then_branch = self.branch(Self::parse_expr)?;
            self.expect_kw("else");
            let else_branch = self.branch(Self::parse_expr)?;
            let span = start.join(else_branch.span);
            return Some(Expr {
                kind: ExprKind::Conditional {
                    cond: Box::new(cond),
                    then_branch: Box::new(then_branch),
                    else_branch: Box::new(else_branch),
                },
                span,
            });
        }
        self.parse_null_coalescing()
    }

    /// Charge `links` more operators to the chain that leads here, and
    /// refuse to build it any longer once it passes
    /// [`MAX_EXPR_OPERATORS`].
    fn charge_chain(&mut self, links: u32) -> Option<()> {
        self.expr_chain = self.expr_chain.saturating_add(links);
        if self.expr_chain > MAX_EXPR_OPERATORS {
            self.refuse_deeper(format!(
                "expression has a chain of more than {MAX_EXPR_OPERATORS} operators"
            ));
            return None;
        }
        Some(())
    }

    /// Run `parse` as a branch hanging off the current chain rather than
    /// as a continuation of it: an operand on the right, one item of a
    /// sequence, one argument, one member of a body.
    ///
    /// The branch spells a chain of its own, so it starts from an empty
    /// budget — siblings do not charge each other. What it reaches is
    /// then folded back with a maximum, because the node that owns both
    /// leans on whichever side is longer: a branch deeper than the chain
    /// it hangs from keeps the whole expression's operators charged to
    /// everything built above it.
    fn branch<T>(&mut self, parse: impl FnOnce(&mut Self) -> T) -> T {
        let chain = std::mem::take(&mut self.expr_chain);
        let parsed = parse(self);
        self.expr_chain = chain.max(self.expr_chain);
        parsed
    }

    /// Build one binary node, charging it against the chain budget (see
    /// [`MAX_EXPR_OPERATORS`]).
    fn mk_binary(&mut self, op: BinaryOp, lhs: Expr, rhs: Expr) -> Option<Expr> {
        self.charge_chain(1)?;
        let span = lhs.span.join(rhs.span);
        Some(Expr {
            kind: ExprKind::Binary {
                op,
                lhs: Box::new(lhs),
                rhs: Box::new(rhs),
            },
            span,
        })
    }

    fn parse_null_coalescing(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_implies()?;
        while self.eat(TokenKind::QuestionQuestion) {
            let rhs = self.branch(Self::parse_implies)?;
            lhs = self.mk_binary(BinaryOp::NullCoalescing, lhs, rhs)?;
        }
        Some(lhs)
    }

    fn parse_implies(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_or()?;
        while self.eat_kw("implies") {
            let rhs = self.branch(Self::parse_or)?;
            lhs = self.mk_binary(BinaryOp::Implies, lhs, rhs)?;
        }
        Some(lhs)
    }

    fn parse_or(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_xor()?;
        loop {
            let op = if self.eat(TokenKind::Pipe) {
                BinaryOp::OrBar
            } else if self.eat_kw("or") {
                BinaryOp::CondOr
            } else {
                break;
            };
            let rhs = self.branch(Self::parse_xor)?;
            lhs = self.mk_binary(op, lhs, rhs)?;
        }
        Some(lhs)
    }

    fn parse_xor(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_and()?;
        while self.eat_kw("xor") {
            let rhs = self.branch(Self::parse_and)?;
            lhs = self.mk_binary(BinaryOp::Xor, lhs, rhs)?;
        }
        Some(lhs)
    }

    fn parse_and(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_equality()?;
        loop {
            let op = if self.eat(TokenKind::Amp) {
                BinaryOp::AndAmp
            } else if self.eat_kw("and") {
                BinaryOp::CondAnd
            } else {
                break;
            };
            let rhs = self.branch(Self::parse_equality)?;
            lhs = self.mk_binary(op, lhs, rhs)?;
        }
        Some(lhs)
    }

    fn parse_equality(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_classification()?;
        loop {
            let op = if self.eat(TokenKind::EqEq) {
                BinaryOp::Eq
            } else if self.eat(TokenKind::BangEq) {
                BinaryOp::NotEq
            } else if self.eat(TokenKind::EqEqEq) {
                BinaryOp::Same
            } else if self.eat(TokenKind::BangEqEq) {
                BinaryOp::NotSame
            } else {
                break;
            };
            let rhs = self.branch(Self::parse_classification)?;
            lhs = self.mk_binary(op, lhs, rhs)?;
        }
        Some(lhs)
    }

    fn classification_op(&mut self) -> Option<ClassificationOp> {
        if self.eat_kw("istype") {
            Some(ClassificationOp::IsType)
        } else if self.eat_kw("hastype") {
            Some(ClassificationOp::HasType)
        } else if self.eat(TokenKind::At) {
            Some(ClassificationOp::AtType)
        } else if self.eat(TokenKind::AtAt) {
            Some(ClassificationOp::MetaAtType)
        } else if self.eat_kw("as") {
            Some(ClassificationOp::As)
        } else if self.eat_kw("meta") {
            Some(ClassificationOp::Meta)
        } else {
            None
        }
    }

    fn parse_classification(&mut self) -> Option<Expr> {
        // Implicit-self forms: `istype T`, `hastype T`, `@T`, `as T`.
        let mut lhs = if self.at_kw("istype")
            || self.at_kw("hastype")
            || self.at_kw("as")
            || self.at(TokenKind::At)
        {
            let start = self.cur().span;
            let op = self.classification_op()?;
            let ty = self.parse_target_ref()?;
            let span = start.join(ty.span());
            Expr {
                kind: ExprKind::Classification {
                    op,
                    operand: None,
                    ty: Box::new(ty),
                },
                span,
            }
        } else {
            self.parse_relational()?
        };
        // Left-associative chain: a cast result can itself be classified
        // — `x as T istype U`, and the implicit-self `as T istype U`
        // used by filter conditions.
        while self.at_kw("istype")
            || self.at_kw("hastype")
            || self.at_kw("as")
            || self.at_kw("meta")
            || self.at(TokenKind::At)
            || self.at(TokenKind::AtAt)
        {
            let op = self.classification_op()?;
            let ty = self.parse_target_ref()?;
            self.charge_chain(1)?;
            let span = lhs.span.join(ty.span());
            lhs = Expr {
                kind: ExprKind::Classification {
                    op,
                    operand: Some(Box::new(lhs)),
                    ty: Box::new(ty),
                },
                span,
            };
        }
        Some(lhs)
    }

    fn parse_relational(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_range()?;
        loop {
            let op = if self.eat(TokenKind::Lt) {
                BinaryOp::Lt
            } else if self.eat(TokenKind::Gt) {
                BinaryOp::Gt
            } else if self.eat(TokenKind::LtEq) {
                BinaryOp::LtEq
            } else if self.eat(TokenKind::GtEq) {
                BinaryOp::GtEq
            } else {
                break;
            };
            let rhs = self.branch(Self::parse_range)?;
            lhs = self.mk_binary(op, lhs, rhs)?;
        }
        Some(lhs)
    }

    fn parse_range(&mut self) -> Option<Expr> {
        let lhs = self.parse_additive()?;
        if self.eat(TokenKind::DotDot) {
            let rhs = self.branch(Self::parse_additive)?;
            return self.mk_binary(BinaryOp::Range, lhs, rhs);
        }
        Some(lhs)
    }

    fn parse_additive(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_multiplicative()?;
        loop {
            let op = if self.eat(TokenKind::Plus) {
                BinaryOp::Add
            } else if self.eat(TokenKind::Minus) {
                BinaryOp::Sub
            } else {
                break;
            };
            let rhs = self.branch(Self::parse_multiplicative)?;
            lhs = self.mk_binary(op, lhs, rhs)?;
        }
        Some(lhs)
    }

    fn parse_multiplicative(&mut self) -> Option<Expr> {
        let mut lhs = self.parse_exponentiation()?;
        loop {
            let op = if self.at(TokenKind::Star) && !self.star_is_infinity() {
                self.bump();
                BinaryOp::Mul
            } else if self.eat(TokenKind::Slash) {
                BinaryOp::Div
            } else if self.eat(TokenKind::Percent) {
                BinaryOp::Rem
            } else {
                break;
            };
            let rhs = self.branch(Self::parse_exponentiation)?;
            lhs = self.mk_binary(op, lhs, rhs)?;
        }
        Some(lhs)
    }

    /// A `*` right before `]`, `)`, `,` or `..` is the infinity literal /
    /// end-of-context, not multiplication.
    fn star_is_infinity(&self) -> bool {
        matches!(
            self.nth(1).kind,
            TokenKind::RBracket | TokenKind::RParen | TokenKind::Comma | TokenKind::Semi
        )
    }

    fn parse_exponentiation(&mut self) -> Option<Expr> {
        let lhs = self.parse_unary()?;
        let op = if self.eat(TokenKind::StarStar) {
            BinaryOp::Pow
        } else if self.eat(TokenKind::Caret) {
            BinaryOp::Caret
        } else {
            return Some(lhs);
        };
        // Right-associative: the recursion is this operator's right
        // operand, one level further down, and is charged as such.
        let rhs = self.branch(|p| p.descend(Self::parse_exponentiation))?;
        self.mk_binary(op, lhs, rhs)
    }

    fn parse_unary(&mut self) -> Option<Expr> {
        let op = if self.at(TokenKind::Plus) {
            Some(UnaryOp::Plus)
        } else if self.at(TokenKind::Minus) {
            Some(UnaryOp::Minus)
        } else if self.at(TokenKind::Tilde) {
            Some(UnaryOp::Tilde)
        } else if self.at_kw("not") {
            Some(UnaryOp::Not)
        } else {
            None
        };
        if let Some(op) = op {
            let start = self.cur().span;
            self.bump();
            let operand = self.parse_extent()?;
            let span = start.join(operand.span);
            return Some(Expr {
                kind: ExprKind::Unary {
                    op,
                    operand: Box::new(operand),
                },
                span,
            });
        }
        self.parse_extent()
    }

    fn parse_extent(&mut self) -> Option<Expr> {
        if self.at_kw("all") {
            let start = self.cur().span;
            self.bump();
            let ty = self.parse_target_ref()?;
            let span = start.join(ty.span());
            return Some(Expr {
                kind: ExprKind::Extent { ty: Box::new(ty) },
                span,
            });
        }
        self.parse_primary()
    }

    fn parse_primary(&mut self) -> Option<Expr> {
        let mut expr = self.parse_base()?;
        loop {
            if self.at(TokenKind::Dot) {
                // `.{ body }` = collect; `.metadata` = metadata access;
                // otherwise a feature-chain step.
                self.charge_chain(1)?;
                match self.nth(1).kind {
                    TokenKind::LBrace | TokenKind::Semi => {
                        self.bump();
                        let body = self.branch(Self::parse_body_expr)?;
                        let span = expr.span.join(body.span);
                        expr = Expr {
                            kind: ExprKind::Collect {
                                target: Box::new(expr),
                                body: Box::new(body),
                            },
                            span,
                        };
                    }
                    _ if self.nth_kw(1, "metadata") => {
                        // Move the left operand out rather than copying it:
                        // a chain of suffixes would clone everything parsed
                        // so far at each `.metadata`.
                        let span = expr.span;
                        match expr.kind {
                            ExprKind::Ref(qn) => {
                                self.bump();
                                let end = self.bump().span;
                                expr = Expr {
                                    kind: ExprKind::MetadataAccess { target: qn },
                                    span: span.join(end),
                                };
                            }
                            kind => {
                                self.error_here(
                                    "`.metadata` requires an element reference on the left"
                                        .to_string(),
                                );
                                self.bump();
                                self.bump();
                                expr = Expr { kind, span };
                            }
                        }
                    }
                    _ => {
                        self.bump();
                        let member = self.parse_target_ref()?;
                        let span = expr.span.join(member.span());
                        expr = Expr {
                            kind: ExprKind::ChainStep {
                                target: Box::new(expr),
                                member,
                            },
                            span,
                        };
                    }
                }
            } else if self.at(TokenKind::DotQuestion) {
                self.charge_chain(1)?;
                self.bump();
                let body = self.branch(Self::parse_body_expr)?;
                let span = expr.span.join(body.span);
                expr = Expr {
                    kind: ExprKind::Select {
                        target: Box::new(expr),
                        body: Box::new(body),
                    },
                    span,
                };
            } else if self.at(TokenKind::Hash) && self.nth(1).kind == TokenKind::LParen {
                self.charge_chain(1)?;
                self.bump();
                self.bump();
                let index = self.branch(Self::parse_sequence_expr)?;
                let end = self.cur().span;
                self.expect(TokenKind::RParen, "`)` closing index");
                expr = Expr {
                    span: expr.span.join(end),
                    kind: ExprKind::Index {
                        target: Box::new(expr),
                        index: Box::new(index),
                    },
                };
            } else if self.at(TokenKind::LBracket) {
                self.charge_chain(1)?;
                self.bump();
                let arg = self.branch(Self::parse_sequence_expr)?;
                let end = self.cur().span;
                self.expect(TokenKind::RBracket, "`]`");
                expr = Expr {
                    span: expr.span.join(end),
                    kind: ExprKind::Bracket {
                        target: Box::new(expr),
                        arg: Box::new(arg),
                    },
                };
            } else if self.at(TokenKind::Arrow) {
                self.charge_chain(1)?;
                self.bump();
                let ty = self.parse_target_ref()?;
                let args = if self.at(TokenKind::LBrace)
                    || (self.dialect == Dialect::Sysml && self.at(TokenKind::Semi))
                {
                    ArrowArgs::Body(Box::new(self.branch(Self::parse_body_expr)?))
                } else if self.at(TokenKind::LParen) {
                    ArrowArgs::List(self.branch(Self::parse_argument_list)?)
                } else {
                    ArrowArgs::FunctionRef(self.parse_qualified_name()?)
                };
                let span = expr.span.join(self.prev_end_span());
                expr = Expr {
                    kind: ExprKind::Arrow {
                        target: Box::new(expr),
                        ty: Box::new(ty),
                        args,
                    },
                    span,
                };
            } else {
                break;
            }
        }
        Some(expr)
    }

    fn parse_base(&mut self) -> Option<Expr> {
        let start = self.cur().span;

        // Literals.
        if self.at_kw("true") || self.at_kw("false") {
            let value = self.at_kw("true");
            self.bump();
            return Some(Expr {
                kind: ExprKind::Literal(Literal::Bool(value)),
                span: start,
            });
        }
        if self.at_kw("null") {
            self.bump();
            return Some(Expr {
                kind: ExprKind::Null,
                span: start,
            });
        }
        if self.at(TokenKind::String) {
            let tok = self.bump();
            return Some(Expr {
                kind: ExprKind::Literal(Literal::String(unescape(tok.text(self.src)))),
                span: start,
            });
        }
        if self.at(TokenKind::Decimal) || self.at(TokenKind::Exp) || self.at(TokenKind::Dot) {
            return self.parse_number(start);
        }
        if self.at(TokenKind::Star) {
            self.bump();
            return Some(Expr {
                kind: ExprKind::Literal(Literal::Infinity),
                span: start,
            });
        }

        // `new Type(args)`.
        if self.at_kw("new") {
            self.bump();
            let ty = self.parse_target_ref()?;
            let args = self.branch(Self::parse_argument_list)?;
            let span = start.join(self.prev_end_span());
            return Some(Expr {
                kind: ExprKind::Constructor {
                    ty: Box::new(ty),
                    args,
                },
                span,
            });
        }

        // `( )` = null, `( sequence )`.
        if self.at(TokenKind::LParen) {
            self.bump();
            if self.eat(TokenKind::RParen) {
                return Some(Expr {
                    kind: ExprKind::Null,
                    span: start.join(self.prev_end_span()),
                });
            }
            let inner = self.parse_sequence_expr()?;
            self.expect(TokenKind::RParen, "`)`");
            // The span covers the parentheses: consumers placing
            // annotations at an expression's end (inlay hints) must
            // land after `)`, not after the last inner token.
            return Some(Expr {
                kind: inner.kind,
                span: start.join(self.prev_end_span()),
            });
        }

        // SysML redefines ExpressionBody to CalculationBody, whose
        // non-braced alternative is a single semicolon.
        if self.at(TokenKind::LBrace)
            || (self.dialect == Dialect::Sysml && self.at(TokenKind::Semi))
        {
            return self.parse_body_expr();
        }

        // Name-based: reference or invocation.
        if self.at_name() || self.at(TokenKind::Dollar) {
            let target = self.parse_target_ref()?;
            if self.at(TokenKind::LParen) {
                let args = self.branch(Self::parse_argument_list)?;
                let span = start.join(self.prev_end_span());
                return Some(Expr {
                    kind: ExprKind::Invocation {
                        ty: Box::new(target),
                        args,
                    },
                    span,
                });
            }
            return match target {
                TargetRef::Name(qn) => Some(Expr {
                    span: qn.span,
                    kind: ExprKind::Ref(qn),
                }),
                TargetRef::Chain(links) => {
                    // A chain in expression position: fold into chain steps
                    // from a leading reference. The fold leans one node per
                    // link, so the links are charged like any other chain.
                    let span = links.first().unwrap().span.join(links.last().unwrap().span);
                    self.charge_chain(links.len() as u32 - 1)?;
                    let mut iter = links.into_iter();
                    let first = iter.next().unwrap();
                    let mut expr = Expr {
                        span: first.span,
                        kind: ExprKind::Ref(first),
                    };
                    for link in iter {
                        let s = expr.span.join(link.span);
                        expr = Expr {
                            kind: ExprKind::ChainStep {
                                target: Box::new(expr),
                                member: TargetRef::Name(link),
                            },
                            span: s,
                        };
                    }
                    Some(Expr { span, ..expr })
                }
            };
        }

        self.error_here(format!(
            "expected an expression, found `{}`",
            self.describe_cur()
        ));
        None
    }

    /// Real/integer literal composition:
    /// `DECIMAL` | `EXP` | `DECIMAL? '.' (DECIMAL | EXP)`.
    fn parse_number(&mut self, start: Span) -> Option<Expr> {
        if self.at(TokenKind::Exp) {
            let tok = self.bump();
            return Some(Expr {
                kind: ExprKind::Literal(Literal::Real(tok.text(self.src).to_string())),
                span: start,
            });
        }
        if self.at(TokenKind::Dot) {
            // `.5`
            self.bump();
            if self.at(TokenKind::Decimal) || self.at(TokenKind::Exp) {
                let frac = self.bump();
                let span = start.join(frac.span);
                return Some(Expr {
                    kind: ExprKind::Literal(Literal::Real(span.slice(self.src).to_string())),
                    span,
                });
            }
            self.error_here("expected digits after `.`".to_string());
            return None;
        }
        let int_tok = self.bump(); // Decimal
        if self.at(TokenKind::Dot)
            && matches!(self.nth(1).kind, TokenKind::Decimal | TokenKind::Exp)
        {
            self.bump();
            let frac = self.bump();
            let span = start.join(frac.span);
            return Some(Expr {
                kind: ExprKind::Literal(Literal::Real(span.slice(self.src).to_string())),
                span,
            });
        }
        Some(Expr {
            kind: ExprKind::Literal(Literal::Integer(int_tok.text(self.src).to_string())),
            span: start,
        })
    }

    /// Expression body. SysML overrides these to full calculation bodies,
    /// including both the braced member form and a bare `;` alternative.
    fn parse_body_expr(&mut self) -> Option<Expr> {
        let start = self.cur().span;
        if self.dialect == Dialect::Sysml && self.eat(TokenKind::Semi) {
            return Some(Expr {
                kind: ExprKind::BodyTerminator,
                span: start,
            });
        }
        self.expect(TokenKind::LBrace, "`{`")?;
        let saved = std::mem::take(&mut self.meta_body);
        let members = self.parse_body_members();
        self.meta_body = saved;
        let end = self.cur().span;
        self.expect(TokenKind::RBrace, "`}` closing expression body");
        Some(Expr {
            kind: ExprKind::Body { members },
            span: start.join(end),
        })
    }

    /// Comma sequence inside `(...)`, `#(...)`, `[...]`.
    fn parse_sequence_expr(&mut self) -> Option<Expr> {
        let first = self.parse_expr()?;
        if !self.at(TokenKind::Comma) {
            return Some(first);
        }
        let mut items = vec![first];
        while self.eat(TokenKind::Comma) {
            // Trailing comma is allowed by the grammar.
            if self.at(TokenKind::RParen) || self.at(TokenKind::RBracket) {
                break;
            }
            items.push(self.branch(Self::parse_expr)?);
        }
        let span = items.first().unwrap().span.join(items.last().unwrap().span);
        Some(Expr {
            kind: ExprKind::Sequence(items),
            span,
        })
    }

    /// `( args? )` — positional or `name = value` named arguments.
    fn parse_argument_list(&mut self) -> Option<Vec<Arg>> {
        self.expect(TokenKind::LParen, "`(`")?;
        let mut args = Vec::new();
        if self.eat(TokenKind::RParen) {
            return Some(args);
        }
        loop {
            let value = self.branch(Self::parse_expr)?;
            if self.eat(TokenKind::Eq) {
                // Named argument: the "value" we parsed is the parameter name.
                let name = match value.kind {
                    ExprKind::Ref(qn) => Some(qn),
                    _ => {
                        self.diags.push(Diagnostic::error(
                            value.span,
                            "argument name must be a (qualified) name".to_string(),
                        ));
                        None
                    }
                };
                let actual = self.branch(Self::parse_expr)?;
                args.push(Arg {
                    name,
                    value: actual,
                });
            } else {
                args.push(Arg { name: None, value });
            }
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RParen, "`)` closing argument list");
        Some(args)
    }
}
