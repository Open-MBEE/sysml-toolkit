//! Tokenizer for the KerML / SysML v2 textual notation.
//!
//! Implements the terminal rules of the normative grammars
//! (`spec-refs/KerMLExpressions.xtext`):
//!
//! ```text
//! DECIMAL_VALUE     : '0'..'9' ('0'..'9')*
//! EXP_VALUE         : DECIMAL_VALUE ('e'|'E') ('+'|'-')? DECIMAL_VALUE
//! ID                : ('a'..'z'|'A'..'Z'|'_') ('a'..'z'|'A'..'Z'|'_'|'0'..'9')*
//! UNRESTRICTED_NAME : '\'' (ESCAPE | ~('\\'|'\''))* '\''
//! STRING_VALUE      : '"'  (ESCAPE | ~('\\'|'"'))* '"'
//! REGULAR_COMMENT   : '/*' -> '*/'
//! ML_NOTE           : '//*' -> '*/'
//! SL_NOTE           : '//' ...to end of line
//! WS                : (' '|'\t'|'\r'|'\n')+
//! ESCAPE            : '\\' ('b'|'t'|'n'|'f'|'r'|'"'|'\''|'\\')
//! ```
//!
//! Note that a real literal like `1.5` is *not* a single token: per the
//! grammar it is `DECIMAL '.' DECIMAL`, composed by the parser (which is what
//! makes `1..5` lex cleanly as a range).

use crate::diag::Diagnostic;
use crate::span::Span;
use crate::token::{Token, TokenKind};

/// The most token slots reserved before tokenizing, whatever the input
/// size (see the estimate below).
const MAX_TOKEN_HINT: usize = 64 * 1024;

/// Tokenize `src`, returning every token including trivia, terminated by an
/// [`TokenKind::Eof`] token. Malformed input yields `Error` tokens plus
/// diagnostics; the token stream always covers the entire input.
#[must_use]
pub fn tokenize(src: &str) -> (Vec<Token>, Vec<Diagnostic>) {
    let mut lexer = Lexer {
        src: src.as_bytes(),
        text: src,
        pos: 0,
        // Measured across the corpora, source text runs about two bytes
        // to the token once trivia is counted. The estimate is capped
        // because the ratio is a property of written notation, not of
        // text: a file that is mostly one long comment is a couple of
        // tokens, and a slot per two bytes of it would reserve orders of
        // magnitude more than the lexer will fill. Past the cap the
        // vector grows the usual way.
        tokens: Vec::with_capacity((src.len() / 2 + 1).min(MAX_TOKEN_HINT)),
        diags: Vec::new(),
    };
    lexer.run();
    (lexer.tokens, lexer.diags)
}

struct Lexer<'s> {
    src: &'s [u8],
    text: &'s str,
    pos: usize,
    tokens: Vec<Token>,
    diags: Vec<Diagnostic>,
}

impl<'s> Lexer<'s> {
    fn run(&mut self) {
        while self.pos < self.src.len() {
            let start = self.pos;
            let kind = self.next_kind();
            debug_assert!(self.pos > start, "lexer must always make progress");
            self.tokens.push(Token::new(kind, self.span_from(start)));
        }
        let end = crate::span::clamp_offset(self.src.len());
        self.tokens
            .push(Token::new(TokenKind::Eof, Span::new(end, end)));
    }

    fn span_from(&self, start: usize) -> Span {
        Span::new(
            crate::span::clamp_offset(start),
            crate::span::clamp_offset(self.pos),
        )
    }

    fn peek(&self, ahead: usize) -> Option<u8> {
        self.src.get(self.pos + ahead).copied()
    }

    fn bump(&mut self) -> u8 {
        let b = self.src[self.pos];
        self.pos += 1;
        b
    }

    fn eat(&mut self, b: u8) -> bool {
        if self.peek(0) == Some(b) {
            self.pos += 1;
            true
        } else {
            false
        }
    }

    fn error(&mut self, start: usize, message: impl Into<String>) {
        self.diags
            .push(Diagnostic::error(self.span_from(start), message));
    }

    fn next_kind(&mut self) -> TokenKind {
        use TokenKind::*;
        let start = self.pos;
        let b = self.bump();
        match b {
            b' ' | b'\t' | b'\r' | b'\n' => {
                while matches!(self.peek(0), Some(b' ' | b'\t' | b'\r' | b'\n')) {
                    self.pos += 1;
                }
                Whitespace
            }

            b'a'..=b'z' | b'A'..=b'Z' | b'_' => {
                while matches!(
                    self.peek(0),
                    Some(b'a'..=b'z' | b'A'..=b'Z' | b'0'..=b'9' | b'_')
                ) {
                    self.pos += 1;
                }
                Ident
            }

            b'0'..=b'9' => self.number(),

            b'\'' => self.quoted(start, b'\'', "unrestricted name"),
            b'"' => self.quoted(start, b'"', "string literal"),

            b'/' => match self.peek(0) {
                // REGULAR_COMMENT: /* ... */
                Some(b'*') => {
                    self.pos += 1;
                    if self.eat_until_star_slash() {
                        RegularComment
                    } else {
                        self.error(start, "unterminated comment (missing `*/`)");
                        Error
                    }
                }
                Some(b'/') => {
                    self.pos += 1;
                    if self.peek(0) == Some(b'*') {
                        // ML_NOTE: //* ... */
                        self.pos += 1;
                        if self.eat_until_star_slash() {
                            BlockNote
                        } else {
                            self.error(start, "unterminated note (missing `*/`)");
                            Error
                        }
                    } else {
                        // SL_NOTE: // to end of line (newline stays outside)
                        while !matches!(self.peek(0), None | Some(b'\n' | b'\r')) {
                            self.pos += 1;
                        }
                        LineNote
                    }
                }
                _ => Slash,
            },

            b';' => Semi,
            b',' => Comma,
            b'.' => {
                if self.eat(b'.') {
                    DotDot
                } else if self.eat(b'?') {
                    DotQuestion
                } else {
                    Dot
                }
            }
            b'?' => {
                if self.eat(b'?') {
                    QuestionQuestion
                } else {
                    Question
                }
            }
            b'~' => Tilde,
            b'=' => {
                if self.eat(b'=') {
                    if self.eat(b'=') { EqEqEq } else { EqEq }
                } else if self.eat(b'>') {
                    FatArrow
                } else {
                    Eq
                }
            }
            b'!' => {
                if self.eat(b'=') {
                    if self.eat(b'=') { BangEqEq } else { BangEq }
                } else {
                    self.error(
                        start,
                        "unexpected character `!` (did you mean `!=` or `not`?)",
                    );
                    Error
                }
            }
            b':' => {
                if self.eat(b':') {
                    if self.eat(b'>') {
                        ColonColonGt
                    } else {
                        ColonColon
                    }
                } else if self.eat(b'>') {
                    if self.eat(b'>') { ColonGtGt } else { ColonGt }
                } else if self.eat(b'=') {
                    ColonEq
                } else {
                    Colon
                }
            }
            b'<' => {
                if self.eat(b'=') {
                    LtEq
                } else {
                    Lt
                }
            }
            b'>' => {
                if self.eat(b'=') {
                    GtEq
                } else {
                    Gt
                }
            }
            b'+' => Plus,
            b'-' => {
                if self.eat(b'>') {
                    Arrow
                } else {
                    Minus
                }
            }
            b'*' => {
                if self.eat(b'*') {
                    StarStar
                } else {
                    Star
                }
            }
            b'%' => Percent,
            b'^' => Caret,
            b'|' => Pipe,
            b'&' => Amp,
            b'@' => {
                if self.eat(b'@') {
                    AtAt
                } else {
                    At
                }
            }
            b'#' => Hash,
            b'$' => Dollar,
            b'(' => LParen,
            b')' => RParen,
            b'[' => LBracket,
            b']' => RBracket,
            b'{' => LBrace,
            b'}' => RBrace,

            _ => {
                // Re-sync to a UTF-8 character boundary so the Error token
                // covers the whole character.
                while self.pos < self.src.len() && !self.text.is_char_boundary(self.pos) {
                    self.pos += 1;
                }
                let ch = self.span_from(start).slice(self.text);
                self.error(start, format!("unexpected character `{ch}`"));
                Error
            }
        }
    }

    /// DECIMAL_VALUE or EXP_VALUE. The exponent is consumed only if complete
    /// (`1e` lexes as `1` then ident `e`, matching the grammar's terminals).
    fn number(&mut self) -> TokenKind {
        while matches!(self.peek(0), Some(b'0'..=b'9')) {
            self.pos += 1;
        }
        if matches!(self.peek(0), Some(b'e' | b'E')) {
            let mut ahead = 1;
            if matches!(self.peek(1), Some(b'+' | b'-')) {
                ahead = 2;
            }
            if matches!(self.peek(ahead), Some(b'0'..=b'9')) {
                self.pos += ahead + 1;
                while matches!(self.peek(0), Some(b'0'..=b'9')) {
                    self.pos += 1;
                }
                return TokenKind::Exp;
            }
        }
        TokenKind::Decimal
    }

    /// Body of UNRESTRICTED_NAME (`quote == '\''`) or STRING_VALUE
    /// (`quote == '"'`). Escapes are validated here; use [`unescape`] to get
    /// the decoded value.
    fn quoted(&mut self, start: usize, quote: u8, what: &str) -> TokenKind {
        loop {
            match self.peek(0) {
                None => {
                    self.error(start, format!("unterminated {what}"));
                    return TokenKind::Error;
                }
                Some(b'\\') => {
                    self.pos += 1;
                    match self.peek(0) {
                        Some(b'b' | b't' | b'n' | b'f' | b'r' | b'"' | b'\'' | b'\\') => {
                            self.pos += 1;
                        }
                        Some(b) => {
                            let esc_start = self.pos - 1;
                            // Skip the whole (possibly multi-byte) escaped
                            // character so the error span stays on a char
                            // boundary.
                            self.pos += utf8_len(b);
                            let esc = self.span_from(esc_start).slice(self.text);
                            self.error(esc_start, format!("invalid escape sequence `{esc}`"));
                        }
                        None => {}
                    }
                }
                Some(b) if b == quote => {
                    self.pos += 1;
                    return if quote == b'\'' {
                        TokenKind::UnrestrictedName
                    } else {
                        TokenKind::String
                    };
                }
                Some(_) => self.pos += 1,
            }
        }
    }

    /// Consume up to and including the next `*/`. Returns false at EOF.
    fn eat_until_star_slash(&mut self) -> bool {
        while self.pos < self.src.len() {
            if self.src[self.pos] == b'*' && self.peek(1) == Some(b'/') {
                self.pos += 2;
                return true;
            }
            self.pos += 1;
        }
        false
    }
}

/// Decode the value of an `UNRESTRICTED_NAME` or `STRING_VALUE` token: strip
/// the quotes and resolve escape sequences. Invalid escapes (already reported
/// by the lexer) are kept verbatim without the backslash.
///
/// Total over any input: a leading quote and a trailing quote are removed
/// when present, so text that is not a complete token — empty, unterminated,
/// or never quoted at all — decodes to what it holds rather than failing.
#[must_use]
pub fn unescape(raw: &str) -> String {
    let inner = raw.strip_prefix(['\'', '"']).unwrap_or(raw);
    let inner = inner.strip_suffix(['\'', '"']).unwrap_or(inner);
    let mut out = String::with_capacity(inner.len());
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c != '\\' {
            out.push(c);
            continue;
        }
        match chars.next() {
            Some('b') => out.push('\u{0008}'),
            Some('t') => out.push('\t'),
            Some('n') => out.push('\n'),
            Some('f') => out.push('\u{000C}'),
            Some('r') => out.push('\r'),
            Some(c @ ('"' | '\'' | '\\')) => out.push(c),
            Some(c) => out.push(c),
            None => {}
        }
    }
    out
}

/// UTF-8 sequence length from a leading byte (continuation bytes yield 1,
/// which keeps forward progress on malformed input).
fn utf8_len(b: u8) -> usize {
    match b {
        0x00..=0x7F => 1,
        0xC0..=0xDF => 2,
        0xE0..=0xEF => 3,
        0xF0..=0xF7 => 4,
        _ => 1,
    }
}
