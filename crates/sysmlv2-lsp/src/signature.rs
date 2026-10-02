//! Signature help: with the cursor in an invocation's argument list
//! (`KineticEnergy(m, |`), the signature of what the invocation calls —
//! the line a hover over the callable leads with — and the parameter the
//! argument being typed binds: by its position among the callable's
//! inputs (an output takes no argument), or by name when the argument is
//! written `name = …`. Calculations, constraints, and actions
//! (definitions and usages), and the KerML functions, predicates, and
//! behaviors, are the callables.
//!
//! Finding the invocation is lexical, on the toolkit's tokens back from
//! the cursor: the innermost `(` still open that follows a name.
//! Balanced groups — a body expression passed as an argument
//! (`f({ in z; z }, |`), a sequence, an index — and strings and comments
//! are passed over whole; a parenthesis grouping an argument, or a
//! bracket opened inside one (`f((a + b) * c, 9.8 [m|`), is looked
//! out of; a `;` ending the statement, or a body the cursor sits in
//! (`{ in x; |`), ends the search. An invocation on a feature chain
//! (`g(1, vehicle.ke(|`) calls the chain's last step, resolved as a
//! member of what the receiver before its dot reaches.
//! With the cursor in a comment, a note, or a string or quoted name
//! still open, there is no answer at all; one left open on an earlier
//! line runs no further than it, and the cursor's line is read on its
//! own, as completion reads it. Resolving the name is the model's (see
//! [`Nav::invocation_signature`]).

use crate::nav::Nav;
use crate::{Document, dialect_of};
use lsp_types::{
    Documentation, MarkupContent, MarkupKind, ParameterInformation, ParameterLabel, SignatureHelp,
    SignatureInformation, Uri,
};
use std::collections::BTreeMap;
use sysmlv2_parser::ast::{Dialect, Expr, ExprKind, Name, QualifiedName, TargetRef};
use sysmlv2_parser::span::Span;
use sysmlv2_parser::token::{Token, TokenKind};

/// The invocation whose argument list the cursor sits in.
struct Call {
    /// The invoked name, as written.
    name: QualifiedName,
    /// On a feature chain (`a.b.f(`), the receiver the name is a
    /// member of, as written (`a.b`).
    receiver: Option<String>,
    /// The position of the argument being typed.
    argument: usize,
    /// The parameter the argument being typed names (`name = …`).
    named: Option<String>,
}

/// Signature help at `offset` in `uri`: `None` outside an invocation's
/// argument list, or when what it invokes is not a callable the model
/// knows.
pub(crate) fn signature_help(
    nav: &mut Nav,
    docs: &BTreeMap<Uri, Document>,
    uri: &Uri,
    offset: u32,
) -> Option<SignatureHelp> {
    let text = docs.get(uri)?.text.clone();
    let (call, stmt_start) = call_at(&text, offset, dialect_of(uri))?;
    // The statement completion cuts out of the model it reads, so the
    // two read one session.
    let cut = crate::salvage::typed_statement_cut(&text, stmt_start, offset);
    let (line, doc) = nav.invocation_signature(docs, uri, cut, &call.callee(dialect_of(uri))?)?;
    // Arguments bind the inputs, in order; a name no input carries, or a
    // position past the last, highlights none.
    let active = match &call.named {
        Some(n) => line
            .inputs
            .iter()
            .copied()
            .find(|&i| line.params[i].0 == *n),
        None => line.inputs.get(call.argument).copied(),
    }
    .unwrap_or(line.params.len());
    let active = u32::try_from(active).ok();
    let offsets = nav.signature_label_offsets();
    let parameters = line
        .params
        .iter()
        .map(|(_, range)| ParameterInformation {
            label: if offsets {
                ParameterLabel::LabelOffsets([
                    utf16_len(&line.label[..range.start]),
                    utf16_len(&line.label[..range.end]),
                ])
            } else {
                ParameterLabel::Simple(line.label[range.clone()].to_string())
            },
            documentation: None,
        })
        .collect();
    Some(SignatureHelp {
        signatures: vec![SignatureInformation {
            label: line.label,
            documentation: doc.map(|value| {
                Documentation::MarkupContent(MarkupContent {
                    kind: MarkupKind::Markdown,
                    value,
                })
            }),
            parameters: Some(parameters),
            active_parameter: active,
        }],
        active_signature: Some(0),
        active_parameter: active,
    })
}

impl Call {
    /// The expression naming what the invocation calls: its name, or
    /// the chain's step on its receiver. `None` when the receiver does
    /// not read as an expression.
    fn callee(&self, dialect: Dialect) -> Option<Expr> {
        let name = Expr {
            kind: ExprKind::Ref(self.name.clone()),
            span: Span::new(0, 0),
        };
        let Some(receiver) = &self.receiver else {
            return Some(name);
        };
        Some(Expr {
            kind: ExprKind::ChainStep {
                target: Box::new(crate::receiver::parse_receiver(receiver, dialect)?),
                member: TargetRef::Name(self.name.clone()),
            },
            span: Span::new(0, 0),
        })
    }
}

/// A label offset: the protocol counts them in UTF-16 code units.
fn utf16_len(s: &str) -> u32 {
    crate::position::offset32(s.encode_utf16().count())
}

/// The invocation whose argument list the cursor at `offset` sits in
/// (see the module docs), and where the statement holding it starts —
/// the one completion cuts out of the model it reads (see
/// [`crate::site::statement_begins`]); `None` in a comment, a note, or
/// a string or quoted name being typed. The call is looked for in the
/// text from the start of a line a few lines back — twice as many each
/// time the tokens run out before the scan decides — so a long document
/// is not lexed whole for a `,` typed outside any call. A call found is
/// settled on the whole text ahead of the cursor, lexed once, as
/// completion lexes it (see [`crate::site::tokens_ahead`]): a line
/// start can fall inside a comment or string running into the lines
/// read, which the scan then reads as code.
fn call_at(text: &str, offset: u32, dialect: Dialect) -> Option<(Call, u32)> {
    let prefix = text.get(..offset as usize)?;
    let mut lines = 1;
    let found = loop {
        // The start of the line `lines - 1` lines above the cursor's.
        let from = prefix
            .rmatch_indices('\n')
            .nth(lines - 1)
            .map_or(0, |(i, _)| i + 1);
        if from == 0 {
            // The whole text: read once, below.
            break None;
        }
        let window = &prefix[from..];
        let lexed = sysmlv2_parser::lexer::tokenize(window).0;
        match scan(window, &significant(&lexed), dialect, false) {
            Scan::Nothing => return None,
            Scan::More => lines *= 2,
            Scan::Found(call) => break Some((call, from)),
        }
    };
    let (tokens, line) = crate::site::tokens_ahead(prefix);
    if in_text(prefix, &tokens) {
        return None;
    }
    let read_right = |from: usize| {
        line.is_none()
            && !tokens
                .iter()
                .any(|t| (t.span.start as usize) < from && from < t.span.end as usize)
    };
    let call = match found {
        Some((call, from)) if read_right(from) => call,
        // The whole text — or, with a quote left open on an earlier
        // line running into it, the cursor's line on its own.
        _ => match scan(
            prefix,
            &significant(&tokens[line.unwrap_or(0)..]),
            dialect,
            true,
        ) {
            Scan::Found(call) => call,
            Scan::Nothing | Scan::More => return None,
        },
    };
    Some((call, crate::site::statement_begins(prefix, &tokens, line)))
}

/// The tokens the scan reads: trivia and the end of input dropped.
fn significant(tokens: &[Token]) -> Vec<Token> {
    tokens
        .iter()
        .copied()
        .filter(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof)
        .collect()
}

/// Does the end of `text`, lexed as `tokens`, sit inside text rather
/// than code: a line note, or a comment, note, string, or quoted name
/// still open?
fn in_text(text: &str, tokens: &[Token]) -> bool {
    let Some(last) = tokens.iter().rev().find(|t| t.kind != TokenKind::Eof) else {
        return false;
    };
    match last.kind {
        TokenKind::LineNote => true,
        TokenKind::Error => {
            let opened = last.text(text);
            ["\"", "'", "/*", "//"]
                .iter()
                .any(|o| opened.starts_with(o))
        }
        _ => false,
    }
}

/// What a backward scan over a window's tokens decided.
enum Scan {
    /// The call.
    Found(Call),
    /// The cursor is in no invocation's argument list.
    Nothing,
    /// The window's first token came before anything was decided.
    More,
}

/// Scan `tokens` of `window` back from its end (see [`call_at`]).
/// `whole`: the window starts the text, so running out of tokens means
/// the statement starts there.
fn scan(window: &str, tokens: &[Token], dialect: Dialect, whole: bool) -> Scan {
    use TokenKind as K;
    // Groups being passed over whole: closers met, openers not yet.
    let mut closers = 0usize;
    // Separators met at the level being scanned, and the first of them
    // (the one closest to the cursor): the argument being typed follows
    // it.
    let mut argument = 0usize;
    let mut last_comma: Option<usize> = None;
    let mut found: Option<Call> = None;
    for i in (0..tokens.len()).rev() {
        let kind = tokens[i].kind;
        if closers > 0 {
            match kind {
                K::RParen | K::RBracket | K::RBrace => closers += 1,
                K::LParen | K::LBracket | K::LBrace => closers -= 1,
                _ => {}
            }
            continue;
        }
        match kind {
            K::RParen | K::RBracket => closers += 1,
            // Before the call is found, a `}` closes a body expression
            // passed as an argument; after it, outside the call's own
            // parentheses, the member before the statement.
            K::RBrace if found.is_none() => closers += 1,
            // The statement ends at a `;`, at a body it sits in, and at
            // the member before it.
            K::Semi | K::LBrace | K::RBrace => {
                return match found {
                    Some(call) => Scan::Found(call),
                    None => Scan::Nothing,
                };
            }
            K::LParen if found.is_none() => {
                let first = last_comma.map_or(i + 1, |c| c + 1);
                match invoked_name(window, &tokens[..i], dialect) {
                    // The name may run on before the window.
                    Some(Head::Call(_, _, 0)) if !whole => return Scan::More,
                    Some(Head::Select) => return Scan::Nothing,
                    Some(Head::Call(name, receiver, _)) => {
                        found = Some(Call {
                            name,
                            receiver: None,
                            // `x->f(a)` passes `x` as the first argument.
                            argument: argument + usize::from(receiver),
                            named: named_argument(window, &tokens[first..], dialect),
                        });
                    }
                    Some(Head::Step(name, dot)) => {
                        let start = match crate::receiver::receiver_start(&tokens[..dot]) {
                            // The receiver may run on before the window.
                            Some(0) | None if !whole => return Scan::More,
                            None => return Scan::Nothing,
                            Some(start) => start,
                        };
                        let receiver = &window
                            [tokens[start].span.start as usize..tokens[dot].span.start as usize];
                        found = Some(Call {
                            name,
                            receiver: Some(receiver.trim_end().to_string()),
                            argument,
                            named: named_argument(window, &tokens[first..], dialect),
                        });
                    }
                    // A group inside an argument: what was counted is
                    // its own.
                    None => {
                        argument = 0;
                        last_comma = None;
                    }
                }
            }
            K::LBracket if found.is_none() => {
                argument = 0;
                last_comma = None;
            }
            K::Comma if found.is_none() => {
                argument += 1;
                last_comma.get_or_insert(i);
            }
            _ => {}
        }
    }
    match found {
        Some(call) if whole => Scan::Found(call),
        None if whole => Scan::Nothing,
        _ => Scan::More,
    }
}

/// What a `(` follows, when a name does.
enum Head {
    /// The name it invokes — `f`, `P::f`, `$::P::f` — whether through
    /// `->` on a receiver, and the index of the name's first token.
    Call(QualifiedName, bool, usize),
    /// A feature-chain step (`a.f(`): the name, a member of what the
    /// receiver ending before the `.` at the index reaches.
    Step(QualifiedName, usize),
    /// A name after `.?` (`a.?f(`), where a body belongs: no
    /// invocation.
    Select,
}

/// The name an invocation's `(` follows (see [`Head`]). `None` when no
/// name precedes the `(` (a grouping parenthesis), or when a keyword
/// does (`if (`).
fn invoked_name(seg: &str, before: &[Token], dialect: Dialect) -> Option<Head> {
    let mut segments = Vec::new();
    let mut is_global = false;
    // Back over `Name (:: Name)*`, with `$::` possibly in front; `i`
    // ends at the path's first token.
    let mut i = before.len();
    loop {
        i = i.checked_sub(1)?;
        segments.push(name_value(seg, before[i], dialect)?);
        if i >= 1 && before[i - 1].kind == TokenKind::ColonColon {
            if i >= 2 && before[i - 2].kind == TokenKind::Dollar {
                is_global = true;
                i -= 2;
                break;
            }
            i -= 1;
            continue;
        }
        break;
    }
    segments.reverse();
    let name = QualifiedName {
        is_global,
        segments,
        span: Span::new(0, 0),
    };
    let prev = i.checked_sub(1).map(|p| before[p].kind);
    Some(match prev {
        Some(TokenKind::Dot) => Head::Step(name, i - 1),
        Some(TokenKind::DotQuestion) => Head::Select,
        _ => Head::Call(name, prev == Some(TokenKind::Arrow), i),
    })
}

/// The parameter an argument's tokens name, when it is written
/// `name = …`.
fn named_argument(seg: &str, argument: &[Token], dialect: Dialect) -> Option<String> {
    match argument {
        [name, eq, ..] if eq.kind == TokenKind::Eq => {
            name_value(seg, *name, dialect).map(|n| n.value)
        }
        _ => None,
    }
}

/// A name token's value — a basic name the dialect does not reserve, or
/// a quoted name, unescaped.
fn name_value(seg: &str, t: Token, dialect: Dialect) -> Option<Name> {
    let text = t.text(seg);
    let value = match t.kind {
        TokenKind::Ident if !sysmlv2_parser::parser::is_reserved(dialect, text) => text.to_string(),
        TokenKind::UnrestrictedName => sysmlv2_parser::lexer::unescape(text),
        _ => return None,
    };
    Some(Name {
        value,
        span: Span::new(0, 0),
    })
}

#[cfg(test)]
mod tests {
    use super::call_at;
    use crate::position::offset32;
    use sysmlv2_parser::ast::Dialect;

    /// The call at the end of `stmt`: its name as written — after its
    /// receiver and a `.` on a feature chain — the argument position,
    /// and the named parameter.
    fn call(stmt: &str) -> Option<(String, usize, Option<String>)> {
        call_at(stmt, offset32(stmt.len()), Dialect::Sysml).map(|(c, _)| {
            let name = c
                .name
                .segments
                .iter()
                .map(|s| s.value.as_str())
                .collect::<Vec<_>>()
                .join("::");
            let name = if c.name.is_global {
                format!("$::{name}")
            } else {
                name
            };
            let name = match c.receiver {
                Some(receiver) => format!("{receiver}.{name}"),
                None => name,
            };
            (name, c.argument, c.named)
        })
    }

    #[test]
    fn finds_the_innermost_open_invocation() {
        let at = |name: &str, argument: usize| Some((name.to_string(), argument, None));
        assert_eq!(call("attribute e = KineticEnergy("), at("KineticEnergy", 0));
        assert_eq!(
            call("attribute e = KineticEnergy(m, "),
            at("KineticEnergy", 1)
        );
        assert_eq!(call("attribute e = P::Q::F(a, b, c"), at("P::Q::F", 2));
        assert_eq!(call("attribute e = $::P::F("), at("$::P::F", 0));
        assert_eq!(call("attribute e = 'my calc'(1, "), at("my calc", 1));
        // Nested: the inner call while it is open, the outer after it.
        assert_eq!(call("attribute e = f(1, g(2, "), at("g", 1));
        assert_eq!(call("attribute e = f(1, g(2, 3), "), at("f", 2));
        // A group, a sequence, or a unit bracket inside an argument.
        assert_eq!(call("attribute e = f(a, (b + c) * "), at("f", 1));
        assert_eq!(call("attribute e = f(a, (b, c"), at("f", 1));
        assert_eq!(call("attribute e = f(a, 9.8 [m"), at("f", 1));
        // `->` passes the receiver first, a chain for one included.
        assert_eq!(call("attribute e = xs->including("), at("including", 1));
        assert_eq!(call("attribute e = x.y->f("), at("f", 1));
        // A closed call on a feature chain is an argument like any other.
        assert_eq!(call("attribute e = g(1, a.f(2), "), at("g", 2));
        // An open one is the call: the chain's step, on its receiver.
        assert_eq!(call("attribute e = a.f("), at("a.f", 0));
        assert_eq!(call("attribute e = g(1, a.b.f(2, "), at("a.b.f", 1));
        assert_eq!(call("attribute e = P::a.f(x, "), at("P::a.f", 1));
        assert_eq!(call("attribute e = $::P::a.f("), at("$::P::a.f", 0));
        assert_eq!(call("attribute e = xs#(1).f("), at("xs#(1).f", 0));
        assert_eq!(call("attribute e = g(x).f(y, "), at("g(x).f", 1));
        assert_eq!(call("attribute e = (a + b).f("), at("(a + b).f", 0));
        // A receiver starting lines before the call.
        assert_eq!(
            call(
                "part def P {\n    attribute e = a\n        .b\n        .f(\n            1,\n            "
            ),
            at("a\n        .b.f", 1)
        );
        // Inside a body expression, the call the body holds.
        assert_eq!(call("attribute e = xs->select {in x; f("), at("f", 0));
        // After a body expression passed as an argument, and past a
        // string or comment holding a statement's punctuation.
        assert_eq!(call("attribute e = f({ in z; z }, "), at("f", 1));
        assert_eq!(call("attribute e = f(\"a;b}\", "), at("f", 1));
        assert_eq!(call("attribute e = f(a /* ; { */, "), at("f", 1));
        // Across lines, however many.
        assert_eq!(
            call("part def P {\n    attribute e = f(\n        a,\n\n\n        b,\n        "),
            at("f", 2)
        );
    }

    #[test]
    fn named_arguments_name_their_parameter() {
        assert_eq!(
            call("attribute e = KineticEnergy(v = 3, m = "),
            Some(("KineticEnergy".to_string(), 1, Some("m".to_string())))
        );
        assert_eq!(
            call("attribute e = f(a == "),
            Some(("f".to_string(), 0, None)),
            "a comparison names nothing"
        );
    }

    /// The whole text ahead of the cursor is lexed once for a call
    /// found — whether in the lines read first or only in the whole
    /// text — and not at all for a `,` typed outside any call.
    #[test]
    fn the_text_ahead_is_lexed_once() {
        let lexes = |stmt: &str| {
            crate::site::PREFIX_LEXES.with(|n| n.set(0));
            let found = call_at(stmt, offset32(stmt.len()), Dialect::Sysml).is_some();
            (found, crate::site::PREFIX_LEXES.with(std::cell::Cell::get))
        };
        assert_eq!(
            lexes("package P {\n    part def Q;\n    attribute e = f(1, "),
            (true, 1)
        );
        assert_eq!(lexes("attribute e = f(\n    1,\n    "), (true, 1));
        assert_eq!(
            lexes("package P {\n    part def Q;\n    attribute e = (1, "),
            (false, 0)
        );
    }

    #[test]
    fn nothing_in_a_comment_or_string() {
        for stmt in [
            // A doc comment whose earlier line holds a statement's
            // punctuation, the window starting inside it.
            "part def V {\n    doc /* The energy\n     * of a moving mass; see below }\n     * KineticEnergy(m, ",
            "attribute e = KineticEnergy(m, // with (a, ",
            "attribute e = KineticEnergy(\"a, ",
            "attribute e = KineticEnergy(m, /* (a, ",
            "attribute e = KineticEnergy(m, 'my (a, ",
        ] {
            assert_eq!(call(stmt), None, "{stmt:?}");
        }
        // After a closed comment or string, the call is still there.
        assert_eq!(
            call("attribute e = f(m /* (c; */, \"d(\", "),
            Some(("f".to_string(), 2, None))
        );
    }

    /// A quote left open on an earlier line runs no further than it:
    /// the cursor's line is read on its own, as completion reads it —
    /// the call typed there found, and none around it before the line.
    #[test]
    fn a_quote_left_open_above_runs_no_further_than_it() {
        for (stmt, statement) in [
            (
                "package P {\n    attribute s = \"open;\n    attribute e = f(1, ",
                "attribute e = f(1, ",
            ),
            (
                "package P {\n    attribute 'open = 1;\n    attribute e = f('a', ",
                "attribute e = f('a', ",
            ),
        ] {
            assert_eq!(call(stmt), Some(("f".to_string(), 1, None)), "{stmt:?}");
            let (_, start) = call_at(stmt, offset32(stmt.len()), Dialect::Sysml).expect("call");
            assert_eq!(&stmt[start as usize..], statement);
        }
        for stmt in [
            "package P {\n    attribute s = g(\"open;\n    attribute e = (1, ",
            "package P {\n    attribute s = g(\"open;\n    h(\n    attribute e = (1, ",
        ] {
            assert_eq!(call(stmt), None, "{stmt:?}");
        }
    }

    #[test]
    fn nothing_outside_an_argument_list() {
        for stmt in [
            "attribute e = KineticEnergy(m, v)",
            "attribute e = (a + ",
            "attribute e = if (",
            // `.?` takes a body: a name after it invokes nothing, and
            // the call around it is not the one being typed.
            "attribute e = g(1, a.?f(",
            // A dot no receiver reads before.
            "attribute e = g(1, .f(",
            "attribute e = f(a, {in x; ",
            "attribute e = \"f(",
            "attribute e = f(a); attribute g = ",
        ] {
            assert_eq!(call(stmt), None, "{stmt:?}");
        }
    }
}
