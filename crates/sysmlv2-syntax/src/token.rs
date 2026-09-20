//! Token definitions shared by the KerML and SysML dialects.
//!
//! The two textual notations share one lexical structure (KerML clause 8.2.2;
//! terminals in `KerMLExpressions.xtext`). Keywords are *not* distinguished
//! here: the dialects reserve different word sets, so word tokens are lexed as
//! [`TokenKind::Ident`] and the parser matches keyword text contextually.

use crate::span::Span;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum TokenKind {
    /// `ID`: `[a-zA-Z_][a-zA-Z0-9_]*` (includes words that are keywords in
    /// some contexts; the parser decides).
    Ident,
    /// `UNRESTRICTED_NAME`: `'...'` with escape sequences.
    UnrestrictedName,
    /// `STRING_VALUE`: `"..."` with escape sequences.
    String,
    /// `DECIMAL_VALUE`: one or more ASCII digits.
    Decimal,
    /// `EXP_VALUE`: `DECIMAL ('e'|'E') ('+'|'-')? DECIMAL`.
    Exp,
    /// `REGULAR_COMMENT`: `/* ... */`. Significant (it is the body of
    /// `comment` / `doc` / `rep` annotating elements), not trivia.
    RegularComment,

    // ---- trivia (hidden channel: WS, SL_NOTE, ML_NOTE) ----
    Whitespace,
    /// `SL_NOTE`: `// ...` to end of line (but not `//*`).
    LineNote,
    /// `ML_NOTE`: `//* ... */`.
    BlockNote,

    // ---- punctuation and operators ----
    Semi,             // ;
    Comma,            // ,
    Dot,              // .
    DotDot,           // ..
    DotQuestion,      // .?
    Question,         // ?
    QuestionQuestion, // ??
    Tilde,            // ~
    Eq,               // =
    EqEq,             // ==
    EqEqEq,           // ===
    BangEq,           // !=
    BangEqEq,         // !==
    FatArrow,         // => (cross-subsetting shorthand)
    Colon,            // :
    ColonColon,       // ::
    ColonGt,          // :>
    ColonGtGt,        // :>>
    ColonColonGt,     // ::>
    ColonEq,          // :=
    Lt,               // <
    Gt,               // >
    LtEq,             // <=
    GtEq,             // >=
    Plus,             // +
    Minus,            // -
    Star,             // *
    StarStar,         // **
    Slash,            // /
    Percent,          // %
    Caret,            // ^
    Pipe,             // |
    Amp,              // &
    At,               // @
    AtAt,             // @@
    Hash,             // #
    Dollar,           // $
    Arrow,            // ->
    LParen,           // (
    RParen,           // )
    LBracket,         // [
    RBracket,         // ]
    LBrace,           // {
    RBrace,           // }

    /// A character sequence that is not a valid token (a diagnostic is
    /// reported alongside).
    Error,
    /// End of input. Always the last token in a token stream.
    Eof,
}

impl TokenKind {
    /// Trivia tokens are skipped by the parser (Xtext "hidden" terminals).
    #[must_use]
    pub fn is_trivia(self) -> bool {
        matches!(
            self,
            TokenKind::Whitespace | TokenKind::LineNote | TokenKind::BlockNote
        )
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    #[must_use]
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Token { kind, span }
    }

    /// The source text of this token.
    #[must_use]
    pub fn text<'a>(&self, src: &'a str) -> &'a str {
        self.span.slice(src)
    }

    /// True if this token is the word `kw` (used for contextual keywords).
    #[must_use]
    pub fn is_kw(&self, src: &str, kw: &str) -> bool {
        self.kind == TokenKind::Ident && self.text(src) == kw
    }
}
