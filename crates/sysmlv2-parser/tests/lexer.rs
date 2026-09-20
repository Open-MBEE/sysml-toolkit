//! Lexer conformance tests against the normative terminal rules
//! (`spec-refs/KerMLExpressions.xtext`).

use sysmlv2_parser::lexer::{tokenize, unescape};
use sysmlv2_parser::token::TokenKind::{self, *};

/// Lex and return the non-trivia token kinds (without EOF).
fn kinds(src: &str) -> Vec<TokenKind> {
    let (tokens, diags) = tokenize(src);
    assert!(
        diags.is_empty(),
        "unexpected diagnostics for {src:?}: {diags:?}"
    );
    tokens
        .iter()
        .filter(|t| !t.kind.is_trivia() && t.kind != Eof)
        .map(|t| t.kind)
        .collect()
}

/// Lex and return (kind, text) pairs, trivia excluded.
fn lexed(src: &str) -> Vec<(TokenKind, std::string::String)> {
    let (tokens, _) = tokenize(src);
    tokens
        .iter()
        .filter(|t| !t.kind.is_trivia() && t.kind != Eof)
        .map(|t| (t.kind, t.text(src).to_string()))
        .collect()
}

fn diagnostics(src: &str) -> Vec<std::string::String> {
    let (_, diags) = tokenize(src);
    diags.into_iter().map(|d| d.message).collect()
}

#[test]
fn identifiers() {
    assert_eq!(kinds("abc _x A1_2 part def"), vec![Ident; 5]);
}

#[test]
fn unrestricted_names() {
    let toks = lexed("'hello world' '+-*/'");
    assert_eq!(
        toks,
        vec![
            (UnrestrictedName, "'hello world'".to_string()),
            (UnrestrictedName, "'+-*/'".to_string()),
        ]
    );
}

#[test]
fn unrestricted_name_escapes() {
    assert_eq!(kinds(r"'a\'b\\c\n'"), vec![UnrestrictedName]);
    assert_eq!(unescape(r"'a\'b\\c\nd\te'"), "a'b\\c\nd\te");
}

#[test]
fn string_values() {
    assert_eq!(kinds(r#""hello" "a\"b""#), vec![String, String]);
    assert_eq!(unescape(r#""a\"b\r\f\b""#), "a\"b\r\u{000C}\u{0008}");
}

#[test]
fn strings_may_contain_raw_newlines() {
    assert_eq!(kinds("\"line1\nline2\""), vec![String]);
}

#[test]
fn numbers() {
    assert_eq!(kinds("0 42 12345678901234567890"), vec![Decimal; 3]);
    assert_eq!(kinds("1e5 2E+10 3e-2"), vec![Exp, Exp, Exp]);
}

#[test]
fn incomplete_exponent_is_not_an_exp_token() {
    // `1e` = DECIMAL then ID; `1e+` = DECIMAL, ID, `+`.
    assert_eq!(kinds("1e"), vec![Decimal, Ident]);
    assert_eq!(kinds("1e+"), vec![Decimal, Ident, Plus]);
}

#[test]
fn real_literal_parts() {
    // Reals are parser-level compositions: `1.5` is three tokens.
    assert_eq!(kinds("1.5"), vec![Decimal, Dot, Decimal]);
    assert_eq!(kinds(".5"), vec![Dot, Decimal]);
    assert_eq!(kinds("1.5e-3"), vec![Decimal, Dot, Exp]);
}

#[test]
fn range_beats_fraction() {
    // Maximal munch: `1..2` must be DECIMAL `..` DECIMAL.
    assert_eq!(kinds("1..2"), vec![Decimal, DotDot, Decimal]);
    assert_eq!(
        kinds("[0..*]"),
        vec![LBracket, Decimal, DotDot, Star, RBracket]
    );
}

#[test]
fn regular_comment_is_significant() {
    // `/* ... */` is a real token (comment/doc bodies), not trivia.
    assert_eq!(kinds("/* body */"), vec![RegularComment]);
    assert_eq!(kinds("doc /* text */"), vec![Ident, RegularComment]);
}

#[test]
fn notes_are_trivia() {
    // `//` line note and `//* ... */` block note are hidden.
    assert_eq!(kinds("a // note\nb"), vec![Ident, Ident]);
    assert_eq!(
        kinds("a //* note\nstill note *//**/b"),
        vec![Ident, RegularComment, Ident]
    );
}

#[test]
fn line_note_at_eof() {
    assert_eq!(kinds("a // trailing"), vec![Ident]);
}

#[test]
fn multi_char_operators_maximal_munch() {
    assert_eq!(kinds("::>"), vec![ColonColonGt]);
    assert_eq!(kinds(":>>"), vec![ColonGtGt]);
    assert_eq!(kinds(":>"), vec![ColonGt]);
    assert_eq!(kinds("::"), vec![ColonColon]);
    assert_eq!(kinds(":="), vec![ColonEq]);
    assert_eq!(kinds(":"), vec![Colon]);
    assert_eq!(kinds("==="), vec![EqEqEq]);
    assert_eq!(kinds("=="), vec![EqEq]);
    assert_eq!(kinds("=>"), vec![FatArrow]);
    assert_eq!(kinds("="), vec![Eq]);
    assert_eq!(kinds("!=="), vec![BangEqEq]);
    assert_eq!(kinds("!="), vec![BangEq]);
    assert_eq!(kinds("**"), vec![StarStar]);
    assert_eq!(kinds("*"), vec![Star]);
    assert_eq!(kinds("@@"), vec![AtAt]);
    assert_eq!(kinds("@"), vec![At]);
    assert_eq!(kinds("->"), vec![Arrow]);
    assert_eq!(kinds("??"), vec![QuestionQuestion]);
    assert_eq!(kinds(".?"), vec![DotQuestion]);
    assert_eq!(kinds(".."), vec![DotDot]);
    assert_eq!(kinds("<="), vec![LtEq]);
    assert_eq!(kinds(">="), vec![GtEq]);
}

#[test]
fn import_wildcards_are_token_sequences() {
    // `::*` and `::**` are two tokens each.
    assert_eq!(kinds("P::*"), vec![Ident, ColonColon, Star]);
    assert_eq!(kinds("P::**"), vec![Ident, ColonColon, StarStar]);
    assert_eq!(kinds("$::A"), vec![Dollar, ColonColon, Ident]);
}

#[test]
fn declaration_snippet() {
    assert_eq!(
        kinds("part def Vehicle :> Base { attribute mass : Real = 10.5; }"),
        vec![
            Ident, Ident, Ident, ColonGt, Ident, LBrace, Ident, Ident, Colon, Ident, Eq, Decimal,
            Dot, Decimal, Semi, RBrace
        ]
    );
}

#[test]
fn unterminated_string_reports_error() {
    let msgs = diagnostics("\"abc");
    assert!(
        msgs.iter().any(|m| m.contains("unterminated string")),
        "{msgs:?}"
    );
}

#[test]
fn unterminated_comment_reports_error() {
    let msgs = diagnostics("/* abc");
    assert!(
        msgs.iter().any(|m| m.contains("unterminated comment")),
        "{msgs:?}"
    );
}

#[test]
fn invalid_escape_reports_error() {
    let msgs = diagnostics(r"'a\qb'");
    assert!(
        msgs.iter().any(|m| m.contains("invalid escape")),
        "{msgs:?}"
    );
}

#[test]
fn bare_bang_is_an_error() {
    let msgs = diagnostics("!");
    assert!(
        msgs.iter().any(|m| m.contains("unexpected character")),
        "{msgs:?}"
    );
}

#[test]
fn unknown_character_is_one_error_token() {
    let (tokens, diags) = tokenize("a § b");
    assert_eq!(diags.len(), 1);
    let non_trivia: Vec<_> = tokens
        .iter()
        .filter(|t| !t.kind.is_trivia() && t.kind != Eof)
        .map(|t| t.kind)
        .collect();
    assert_eq!(non_trivia, vec![Ident, Error, Ident]);
}

#[test]
fn tokens_cover_entire_input() {
    let src = "part def X { doc /* d */ attribute a : Real := 1.0e3; }";
    let (tokens, _) = tokenize(src);
    let mut pos = 0u32;
    for t in &tokens {
        assert_eq!(t.span.start, pos, "gap before {:?}", t);
        pos = t.span.end;
    }
    assert_eq!(pos, src.len() as u32);
}

/// Decoding a name or string value is total: text that is not a complete
/// token — empty, unterminated, cut inside a multi-byte character, or never
/// quoted — decodes to what it holds.
#[test]
fn unescape_accepts_text_that_is_not_a_complete_token() {
    assert_eq!(unescape(""), "");
    assert_eq!(unescape("'"), "");
    assert_eq!(unescape("\""), "");
    assert_eq!(unescape("''"), "");
    assert_eq!(unescape("\"\""), "");
    assert_eq!(unescape("'é"), "é");
    assert_eq!(unescape("\"héllo"), "héllo");
    assert_eq!(unescape("plain"), "plain");
    assert_eq!(unescape(r"'a\"), "a");
}
