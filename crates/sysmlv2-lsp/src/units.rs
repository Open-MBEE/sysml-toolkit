//! Units in quantity brackets. A `[` after a value opens the value's
//! unit (`5.5 [s]`, `mass [kg]`); after a declared name or type it opens
//! a multiplicity (`wheels : Wheel [4]`) — the two are told apart on
//! the tokens before the bracket. When a unit bracket annotates a
//! declaration's whole value, the declaration's type names the quantity
//! the unit measures, and the units of the same dimension are the ones
//! it takes; when it annotates the right operand of a comparison or a
//! sum, the left operand names it, and when it annotates an argument,
//! the parameter the argument binds.

use crate::nav::CompletionCx;
use std::collections::{HashMap, HashSet, VecDeque};
use sysmlv2_parser::ast::{
    Dialect, ExprKind, FeatureSpecialization, MemberKind, Name, QualifiedName,
};
use sysmlv2_parser::json::{ElementRef, ResolvedModel};
use sysmlv2_parser::quantity::QuantityDims;
use sysmlv2_parser::span::Span;
use sysmlv2_parser::token::{Token, TokenKind};

/// What the `[` around the cursor opens.
#[derive(Debug, PartialEq)]
pub(crate) enum Bracket {
    /// A quantity's unit. `open` is the bracket's offset; `header` the
    /// declaration the value belongs to (`attribute g : DurationValue`,
    /// up to its `=`) when the bracket annotates that whole value, so
    /// the declaration's type is the quantity the unit measures.
    Unit { open: u32, header: Option<Span> },
    /// Any other bracket — above all a multiplicity (`wheels : Wheel [`,
    /// `[0..`), where no unit is written.
    Other,
}

/// The bracket the cursor sits in, `None` outside one (the context's
/// `in_bracket`, read once per request). The tokens of the statement
/// ahead of the bracket decide: a number, a closing `)`, or — in an
/// expression — a name before it opens a unit; anything else, a
/// declared name or type above all, opens a multiplicity.
pub(crate) fn bracket_at(text: &str, cx: &CompletionCx, dialect: Dialect) -> Option<Bracket> {
    let (tokens, at) = bracketed_statement(text, cx)?;
    let ahead = &tokens[..at];
    let word = |t: &Token| &text[t.span.start as usize..t.span.end as usize];
    let unit = match ahead.last() {
        Some(t)
            if matches!(
                t.kind,
                TokenKind::Decimal | TokenKind::Exp | TokenKind::RParen
            ) =>
        {
            true
        }
        Some(t) if t.kind == TokenKind::UnrestrictedName => in_expression(text, ahead),
        Some(t) if t.kind == TokenKind::Ident => {
            !sysmlv2_parser::parser::is_reserved(dialect, word(t)) && in_expression(text, ahead)
        }
        _ => false,
    };
    if !unit {
        return Some(Bracket::Other);
    }
    // The declaration whose whole value the bracket annotates: one
    // primary between its `=` and the bracket.
    let header = value_start(text, ahead)
        .filter(|&(_, value)| single_primary(&ahead[value..]))
        .and_then(|(marker, _)| {
            let start = ahead.first()?.span.start;
            let end = ahead[marker].span.start;
            (start < end).then(|| Span::new(start, end))
        });
    Some(Bracket::Unit {
        open: tokens[at].span.start,
        header,
    })
}

/// The statement the cursor is in, when it leaves a `[` open there:
/// its significant tokens up to the word being completed, and the index
/// of the innermost `[` it leaves open. The statement begins where
/// completion reads it to ([`CompletionCx::stmt_start`]): after a `;`,
/// a `{`, a `}`, or a comment body, an expression's body passed within
/// a `(` or `[` (`f({ in z; z }, 5 [`) part of it, and on the cursor's
/// line when a quote left open above runs into it. `None` outside a
/// bracket (the context's `in_bracket`, read once per request).
fn bracketed_statement(text: &str, cx: &CompletionCx) -> Option<(Vec<Token>, usize)> {
    if !cx.in_bracket {
        return None;
    }
    let start = cx.stmt_start.min(cx.partial_start);
    let tokens: Vec<Token> =
        sysmlv2_parser::lexer::tokenize(text.get(start as usize..cx.partial_start as usize)?)
            .0
            .into_iter()
            .filter(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof)
            .map(|t| Token::new(t.kind, Span::new(t.span.start + start, t.span.end + start)))
            .collect();
    let mut open: Vec<usize> = Vec::new();
    for (i, t) in tokens.iter().enumerate() {
        match t.kind {
            TokenKind::LBracket => open.push(i),
            TokenKind::RBracket => {
                open.pop();
            }
            _ => {}
        }
    }
    let at = *open.last()?;
    Some((tokens, at))
}

/// The untyped attribute whose value's bracket the cursor sits in
/// (`attribute m = 5 [k`): where its declared name ends — where a
/// typing goes — and where the bracket opens. Read on the statement's
/// tokens, so the words of a comment ahead of the declaration never
/// count. `None` when the declaration types or specializes the feature
/// (`:`, `:>`, `:>>`, `::>`, or their keyword forms) before its `=` — a
/// keyword form may stand where the name would (`attribute redefines
/// mass`) — declares no name, or the bracket does not annotate its whole
/// value: the unit of an operand or an argument (`= v * 2 [`,
/// `= f(5 [`) says nothing of the value's type.
pub(crate) fn untyped_attribute(text: &str, cx: &CompletionCx) -> Option<(u32, u32)> {
    use TokenKind as K;
    let (tokens, at) = bracketed_statement(text, cx)?;
    let statement = &tokens[..at];
    let word = |t: &Token| &text[t.span.start as usize..t.span.end as usize];
    let keyword = statement
        .iter()
        .position(|t| t.kind == K::Ident && word(t) == "attribute")?;
    let mut name = keyword + 1;
    // A short name `<m>` ahead of the name.
    if statement.get(name).is_some_and(|t| t.kind == K::Lt) {
        name += statement[name..].iter().position(|t| t.kind == K::Gt)? + 1;
    }
    // `attribute` is a SysML word, so SysML's reserved words are the ones
    // that cannot name the feature: `attribute redefines mass` names none.
    let declared = statement.get(name).filter(|t| {
        t.kind == K::UnrestrictedName
            || (t.kind == K::Ident && !sysmlv2_parser::parser::is_reserved(Dialect::Sysml, word(t)))
    })?;
    let eq = name + 1 + statement[name + 1..].iter().position(|t| t.kind == K::Eq)?;
    let specialized = statement[name + 1..eq].iter().any(|t| {
        matches!(
            t.kind,
            K::Colon | K::ColonGt | K::ColonGtGt | K::ColonColonGt
        ) || (t.kind == K::Ident
            && matches!(
                word(t),
                "typed" | "defined" | "subsets" | "redefines" | "references" | "crosses"
            ))
    });
    (!specialized && single_primary(&statement[eq + 1..]))
        .then(|| (declared.span.end, tokens[at].span.start))
}

/// Whether `ahead` — a statement's tokens before a bracket — puts the
/// bracket in an expression (a value, an operand, an argument) rather
/// than in a declaration's header, where a bracket after a name is its
/// multiplicity. What closed brackets hold does not count, nor does a
/// short name's `<` `>`.
fn in_expression(text: &str, ahead: &[Token]) -> bool {
    use TokenKind as K;
    let mut depth = 0usize;
    let mut i = 0;
    while i < ahead.len() {
        let t = &ahead[i];
        match t.kind {
            K::LBracket => depth += 1,
            K::RBracket => depth = depth.saturating_sub(1),
            _ if depth > 0 => {}
            K::Lt if ahead.get(i + 2).is_some_and(|t| t.kind == K::Gt) => {
                i += 3;
                continue;
            }
            K::Eq
            | K::ColonEq
            | K::LParen
            | K::Plus
            | K::Minus
            | K::Star
            | K::StarStar
            | K::Slash
            | K::Percent
            | K::Caret
            | K::Lt
            | K::Gt
            | K::LtEq
            | K::GtEq
            | K::EqEq
            | K::BangEq
            | K::EqEqEq
            | K::BangEqEq
            | K::Question
            | K::QuestionQuestion
            | K::Pipe
            | K::Amp
            | K::Arrow => return true,
            K::Ident
                if matches!(
                    &text[t.span.start as usize..t.span.end as usize],
                    "default" | "and" | "or" | "xor" | "implies" | "not"
                ) =>
            {
                return true;
            }
            _ => {}
        }
        i += 1;
    }
    false
}

/// Where a declared value starts in `ahead`, a statement's tokens
/// before a bracket: the index of its `=`, `:=`, or `default` outside
/// any group, and the index the value itself starts at (past a `=` or
/// `:=` behind `default`). `None` when the statement declares no value
/// there.
fn value_start(text: &str, ahead: &[Token]) -> Option<(usize, usize)> {
    use TokenKind as K;
    let mut depth = 0usize;
    for (i, t) in ahead.iter().enumerate() {
        match t.kind {
            K::LBracket | K::LParen | K::LBrace => depth += 1,
            K::RBracket | K::RParen | K::RBrace => depth = depth.saturating_sub(1),
            K::Eq | K::ColonEq if depth == 0 => return Some((i, i + 1)),
            K::Ident
                if depth == 0 && &text[t.span.start as usize..t.span.end as usize] == "default" =>
            {
                let assigned = ahead
                    .get(i + 1)
                    .is_some_and(|t| matches!(t.kind, K::Eq | K::ColonEq));
                return Some((i, i + 1 + usize::from(assigned)));
            }
            _ => {}
        }
    }
    None
}

/// Whether `tokens` spell one primary — a number (`5`, `5.5`, `1.5e3`,
/// signed), a parenthesized expression, or a name chain (`a.b`,
/// `P::c`) — so a bracket behind them annotates all of it.
fn single_primary(tokens: &[Token]) -> bool {
    use TokenKind as K;
    let tokens = match tokens.first().map(|t| t.kind) {
        Some(K::Minus | K::Plus) => &tokens[1..],
        _ => tokens,
    };
    let kinds: Vec<K> = tokens.iter().map(|t| t.kind).collect();
    match kinds.as_slice() {
        [K::Decimal | K::Exp]
        | [K::Decimal, K::Dot, K::Decimal | K::Exp]
        | [K::Dot, K::Decimal] => true,
        [K::LParen, .., K::RParen] => {
            // One group: the opening `(` closes only at the end.
            let mut depth = 0usize;
            kinds.iter().enumerate().all(|(i, k)| {
                match k {
                    K::LParen | K::LBracket => depth += 1,
                    K::RParen | K::RBracket => depth = depth.saturating_sub(1),
                    _ => {}
                }
                depth > 0 || i + 1 == kinds.len()
            })
        }
        [] => false,
        names => {
            names.iter().enumerate().all(|(i, k)| match i % 2 {
                0 => matches!(k, K::Ident | K::UnrestrictedName),
                _ => matches!(k, K::Dot | K::ColonColon),
            }) && names.len() % 2 == 1
        }
    }
}

/// Where a unit bracket that annotates no declaration's whole value
/// finds the quantity its unit measures (see [`unit_context`]).
#[derive(Debug, PartialEq)]
pub(crate) enum Context {
    /// The bracket's value is the right operand of a comparison, a sum
    /// or a difference (`mass <= 1500 [`), which measures what the left
    /// operand measures: that operand's span.
    Operand(Span),
    /// The bracket's value is a whole argument of an invocation
    /// (`KineticEnergy(1500 [`), which measures what the parameter it
    /// binds measures: the invoked name's span, the argument's position,
    /// and the parameter it names (`v = 20 [`), when it names one.
    Argument {
        callee: Span,
        position: usize,
        named: Option<String>,
    },
}

/// The context of the unit bracket the cursor sits in, read on the
/// statement's tokens (see [`Context`]). `None` when the bracket's value
/// is a declaration's, a factor's (`mass * 2 [`) — whose quantity is
/// not the product's — or an operand whose left operand is a factor
/// (`2 * mass <= 1500 [`), and outside an argument list.
pub(crate) fn unit_context(text: &str, cx: &CompletionCx) -> Option<Context> {
    use TokenKind as K;
    let (tokens, at) = bracketed_statement(text, cx)?;
    let ahead = &tokens[..at];
    let mut value = operand_start(ahead, ahead.len())?;
    // A sign, where no operand ends before it.
    if value > 0
        && matches!(ahead[value - 1].kind, K::Plus | K::Minus)
        && !(value > 1 && ends_operand(text, &ahead[value - 2]))
    {
        value -= 1;
    }
    let span = |from: usize, to: usize| Span::new(ahead[from].span.start, ahead[to - 1].span.end);
    let before = &ahead[value.checked_sub(1)?];
    match before.kind {
        K::Lt
        | K::Gt
        | K::LtEq
        | K::GtEq
        | K::EqEq
        | K::BangEq
        | K::EqEqEq
        | K::BangEqEq
        | K::Plus
        | K::Minus => {
            let op = value - 1;
            let left = operand_start(ahead, op)?;
            let factor = left.checked_sub(1).is_some_and(|i| {
                matches!(
                    ahead[i].kind,
                    K::Star | K::StarStar | K::Slash | K::Percent | K::Caret
                )
            });
            (!factor).then(|| Context::Operand(span(left, op)))
        }
        K::LParen | K::Comma | K::Eq => {
            let (named, start) = if before.kind == K::Eq {
                let name = &ahead[value.checked_sub(2)?];
                if !matches!(name.kind, K::Ident | K::UnrestrictedName) {
                    return None;
                }
                let name = sysmlv2_parser::lexer::unescape(name.text(text));
                (Some(name), value - 2)
            } else {
                (None, value)
            };
            // Back to the `(` the argument list opens, counting the
            // arguments before this one.
            let mut depth = 0usize;
            let mut position = 0;
            for i in (0..start).rev() {
                match ahead[i].kind {
                    K::RParen | K::RBracket | K::RBrace => depth += 1,
                    K::LParen | K::LBracket | K::LBrace if depth > 0 => depth -= 1,
                    K::LParen => {
                        // The name invoked, not an index (`xs#(`), a
                        // group, or a step after `->`, whose first
                        // parameter the target binds.
                        if !matches!(
                            i.checked_sub(1).map(|j| ahead[j].kind),
                            Some(K::Ident | K::UnrestrictedName)
                        ) {
                            return None;
                        }
                        let callee = operand_start(ahead, i)?;
                        let arrow = callee
                            .checked_sub(1)
                            .is_some_and(|j| ahead[j].kind == K::Arrow);
                        return (!arrow).then(|| Context::Argument {
                            callee: span(callee, i),
                            position,
                            named,
                        });
                    }
                    K::LBracket | K::LBrace => return None,
                    K::Comma if depth == 0 => position += 1,
                    _ => {}
                }
            }
            None
        }
        _ => None,
    }
}

/// Where the operand ending with `tokens[..end]` starts: a number
/// (`5`, `5.5`, `.5`, `1.5e3`), a name chain (`a.b`, `P::c`), or a
/// parenthesized expression, with what follows one — an invocation's or
/// an index's arguments (`f(x)`, `xs#(1)`), a unit (`5 [kg]`), a chain
/// step after those (`f(x).y`). `None` when no operand ends there.
fn operand_start(tokens: &[Token], end: usize) -> Option<usize> {
    use TokenKind as K;
    let name = |i: usize| matches!(tokens[i].kind, K::Ident | K::UnrestrictedName);
    let mut i = end;
    loop {
        match tokens[..i].last()?.kind {
            K::Decimal | K::Exp => {
                i -= 1;
                if i > 0 && tokens[i - 1].kind == K::Dot {
                    i -= 1;
                    if i > 0 && tokens[i - 1].kind == K::Decimal {
                        i -= 1;
                    }
                }
                return Some(i);
            }
            K::Ident | K::UnrestrictedName => {
                i -= 1;
                let step = i > 1
                    && matches!(tokens[i - 1].kind, K::Dot | K::ColonColon)
                    && (name(i - 2) || tokens[i - 2].kind == K::RParen);
                if !step {
                    return Some(i);
                }
                i -= 1;
            }
            K::RParen | K::RBracket => {
                i = opener(tokens, i - 1)?;
                // An invocation's or an index's arguments, or a unit:
                // the operand they follow.
                if tokens[i].kind == K::LParen {
                    if i > 1 && tokens[i - 1].kind == K::Hash {
                        i -= 1;
                    } else if !(i > 0 && name(i - 1)) {
                        return Some(i);
                    }
                }
            }
            _ => return None,
        }
    }
}

/// The index of the opener matching the closer at `tokens[close]`.
fn opener(tokens: &[Token], close: usize) -> Option<usize> {
    use TokenKind as K;
    let mut depth = 0usize;
    for i in (0..=close).rev() {
        match tokens[i].kind {
            K::RParen | K::RBracket | K::RBrace => depth += 1,
            K::LParen | K::LBracket | K::LBrace => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return Some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// Can an operand end with `t` — a `+` or `-` after it a binary
/// operator, not a sign?
fn ends_operand(text: &str, t: &Token) -> bool {
    use TokenKind as K;
    match t.kind {
        K::Decimal | K::Exp | K::String | K::UnrestrictedName | K::RParen | K::RBracket => true,
        K::Ident => !matches!(
            t.text(text),
            "and" | "or" | "xor" | "implies" | "not" | "if" | "else" | "default"
        ),
        _ => false,
    }
}

/// The quantity a unit bracket's context gives its value (see
/// [`unit_context`]): an operand's — the quantity its type measures, or
/// the dimension of the unit it carries (`1200 [kg] + 300 [`) — or the
/// quantity of the parameter an argument binds. `enclosing` are the
/// declarations the statement sits in, innermost first, which names
/// resolve from. `None` when that names no quantity.
pub(crate) fn context_measure(
    resolved: &mut ResolvedModel,
    enclosing: &[ElementRef],
    text: &str,
    context: &Context,
    dialect: Dialect,
) -> Option<Measured> {
    let spelled = |span: &Span| {
        crate::receiver::parse_receiver(text.get(span.start as usize..span.end as usize)?, dialect)
    };
    match context {
        Context::Operand(operand) => {
            let operand = spelled(operand)?;
            let measured = match &operand.kind {
                // The unit the operand carries (`1200 [kg]`): its
                // dimension, and the references it is typed by, which a
                // unit with no dimension the library can compute fits by
                // (`5 ['$']`), as a declared quantity's do — but the
                // library's general references, the definitions
                // `MeasurementReferences` declares: a unit, a simple or a
                // derived unit, a scale, a frame of any kind, which every
                // unit of the kind is (the units of its dimension-one unit
                // fit by their dimension anyway).
                ExprKind::Bracket { arg, .. } => {
                    let unit = crate::receiver::receiver_element(resolved, enclosing, arg)?;
                    let dims = Units::new(resolved).dims_of(resolved, unit)?;
                    let general = resolved.resolve_qualified("MeasurementReferences");
                    let refs = resolved
                        .typings(unit)
                        .into_iter()
                        .filter(|&r| {
                            general.is_none_or(|general| resolved.owner(r) != Some(general))
                        })
                        .collect();
                    Measured {
                        dims: dims.into_iter().next(),
                        refs,
                    }
                }
                _ => {
                    let operand = crate::receiver::receiver_element(resolved, enclosing, &operand)?;
                    measured_by(resolved, operand)?
                }
            };
            // A reading on a scale — a time instant — is compared with,
            // or moved by, a difference, which the scale's unit measures
            // and not the scale (`TimeOf(a) - TimeOf(b) < 2 [s]`, `t + 5
            // [h]`): such an operand names no quantity for the bracket.
            (!on_a_scale(resolved, &measured)).then_some(measured)
        }
        Context::Argument {
            callee,
            position,
            named,
        } => {
            let callee = spelled(callee)?;
            let callee = crate::receiver::receiver_element(resolved, enclosing, &callee)?;
            // The inputs signature help shows, in its order: arguments
            // bind no output.
            let mut inputs = crate::receiver::parameters(resolved, callee)
                .into_iter()
                .filter(|&(p, _)| crate::receiver::binds_argument(resolved, p));
            let (parameter, _) = match named {
                Some(name) => inputs.find(|(_, n)| n.as_deref() == Some(name.as_str()))?,
                None => inputs.nth(*position)?,
            };
            measured_by(resolved, parameter)
        }
    }
}

/// The quantity a declaration's value measures, as the units that fit
/// it are told apart: its dimension, and the measurement-reference
/// definitions its `mRef` is typed by. A unit typed by one of those
/// fits even when it has no dimension the library can compute — a unit
/// of a quantity the model itself defines on a base quantity of its
/// own (`'$' : CurrencyUnit`), a vector's coordinate frame.
pub(crate) struct Measured {
    dims: Option<QuantityDims>,
    refs: Vec<ElementRef>,
}

/// The quantity a declaration's value measures (see [`Measured`]), read
/// from its `header` (`attribute g : ISQ::DurationValue`): the declared
/// type's, else — `attribute :>> mass`, `in limit` — that of the
/// feature it redefines or subsets, a directed parameter's being the
/// same-named one it redefines implicitly. `enclosing` are the
/// declarations the header sits in, innermost first; names resolve from
/// the innermost's body. `None` when the header names no quantity.
pub(crate) fn declared_measure(
    resolved: &mut ResolvedModel,
    enclosing: &[ElementRef],
    header: &str,
    dialect: Dialect,
) -> Option<Measured> {
    let source = format!("{header};");
    let parse = match dialect {
        Dialect::Kerml => sysmlv2_parser::parser::parse_kerml_source(&source),
        Dialect::Sysml => sysmlv2_parser::parser::parse_source(&source),
    };
    let usage = match &parse.unit.members.first()?.kind {
        MemberKind::Usage(u) | MemberKind::Return(u) => u,
        _ => return None,
    };
    let name_of = |t: &sysmlv2_parser::ast::TargetRef| match t {
        sysmlv2_parser::ast::TargetRef::Name(qn) => Some(qn.clone()),
        sysmlv2_parser::ast::TargetRef::Chain(_) => None,
    };
    // Types first, then the features the declaration specializes.
    let mut names: Vec<QualifiedName> = Vec::new();
    let mut features: Vec<QualifiedName> = Vec::new();
    for spec in &usage.declaration.specializations {
        match spec {
            FeatureSpecialization::TypedBy(types) => {
                names.extend(types.iter().filter_map(|t| name_of(&t.target)));
            }
            FeatureSpecialization::Redefines(targets) | FeatureSpecialization::Subsets(targets) => {
                features.extend(targets.iter().filter_map(name_of));
            }
            _ => {}
        }
    }
    names.append(&mut features);
    let scope = enclosing
        .first()
        .and_then(|&e| resolved.element_scope(e))
        .unwrap_or_else(|| resolved.root_scope());
    let mut found: Vec<ElementRef> = names
        .iter()
        .filter_map(|qn| resolved.resolve_in(scope, qn))
        .collect();
    if found.is_empty() && usage.prefix.direction.is_some() {
        if let (Some(&owner), Some(name)) = (enclosing.first(), &usage.declaration.id.name) {
            found.extend(
                resolved
                    .member_of(owner, &simple_name(&name.value))
                    .map(|(hit, _)| hit),
            );
        }
    }
    found.into_iter().find_map(|e| measured_by(resolved, e))
}

/// Whether `measured` is read on measurement scales alone (a time
/// instant's `TimeScale`), with no dimension of its own.
fn on_a_scale(resolved: &mut ResolvedModel, measured: &Measured) -> bool {
    let Some(scale) = resolved.resolve_qualified("MeasurementReferences::MeasurementScale") else {
        return false;
    };
    measured.dims.is_none()
        && !measured.refs.is_empty()
        && measured.refs.iter().all(|&r| resolved.conforms(r, scale))
}

/// The quantity a type — or a feature, through its types — measures;
/// `None` when it is no quantity.
fn measured_by(resolved: &mut ResolvedModel, e: ElementRef) -> Option<Measured> {
    let dims = resolved.quantity_dims_of_type(e);
    let refs = resolved
        .member_of(e, &simple_name("mRef"))
        .map(|(mref, _)| resolved.typings(mref))
        .unwrap_or_default();
    (dims.is_some() || !refs.is_empty()).then_some(Measured { dims, refs })
}

/// `name` as a one-segment reference.
fn simple_name(name: &str) -> QualifiedName {
    QualifiedName {
        is_global: false,
        segments: vec![Name {
            value: name.to_string(),
            span: Span::new(0, 0),
        }],
        span: Span::new(0, 0),
    }
}

/// A unit a completion can offer, as [`Units::entry`] classifies it.
pub(crate) struct UnitEntry {
    element: ElementRef,
    /// The dimensions it measures (see [`Units::dims_of`]).
    dims: Vec<QuantityDims>,
    /// Named by its short name (`kg`), not its declared one.
    pub(crate) short: bool,
}

/// Which elements are units, and the dimensions they measure. An
/// element typed by a measurement reference — a unit, a measurement
/// scale, a coordinate frame — is one, measuring the dimension of the
/// quantity types its definition is the unit of (failing that, those of
/// the nearest definition it specializes). Memoized per definition:
/// hundreds of units share a few dozen.
pub(crate) struct Units {
    /// The library's most general measurement reference; `None`
    /// without one, when nothing is a unit.
    reference: Option<ElementRef>,
    /// Per definition: `None` when it is no measurement reference,
    /// else the dimension it measures, when known.
    defs: HashMap<ElementRef, Option<Option<QuantityDims>>>,
}

impl Units {
    pub(crate) fn new(resolved: &mut ResolvedModel) -> Units {
        Units {
            reference: resolved
                .resolve_qualified("MeasurementReferences::TensorMeasurementReference"),
            defs: HashMap::new(),
        }
    }

    /// The unit the symbol `name` (`qualified` from the root) names, or
    /// `None` when it names no unit.
    pub(crate) fn entry(
        &mut self,
        resolved: &mut ResolvedModel,
        qualified: &str,
        name: &str,
    ) -> Option<UnitEntry> {
        let element = resolved.resolve_qualified(qualified)?;
        self.entry_of(resolved, element, name)
    }

    /// The unit `element`, named `name`, is, or `None` when it is no
    /// unit.
    pub(crate) fn entry_of(
        &mut self,
        resolved: &mut ResolvedModel,
        element: ElementRef,
        name: &str,
    ) -> Option<UnitEntry> {
        let dims = self.dims_of(resolved, element)?;
        let short = resolved.element_declared_short_name(element) == Some(name);
        Some(UnitEntry {
            element,
            dims,
            short,
        })
    }

    /// `None` when `e` is not a unit; else the dimensions it measures,
    /// empty when none is known (a scale, an opaque unit).
    fn dims_of(
        &mut self,
        resolved: &mut ResolvedModel,
        e: ElementRef,
    ) -> Option<Vec<QuantityDims>> {
        let reference = self.reference?;
        let mut unit = false;
        let mut dims = Vec::new();
        for def in resolved.typings(e) {
            let class = match self.defs.get(&def) {
                Some(class) => class.clone(),
                None => {
                    let class = Self::classify(resolved, reference, def);
                    self.defs.insert(def, class.clone());
                    class
                }
            };
            if let Some(measured) = class {
                unit = true;
                dims.extend(measured);
            }
        }
        unit.then_some(dims)
    }

    /// Whether `unit` fits the quantity `measured`: the same dimension,
    /// or typed by one of its measurement-reference definitions.
    pub(crate) fn fits(
        resolved: &mut ResolvedModel,
        unit: &UnitEntry,
        measured: &Measured,
    ) -> bool {
        measured
            .dims
            .as_ref()
            .is_some_and(|d| unit.dims.contains(d))
            || resolved
                .typings(unit.element)
                .into_iter()
                .any(|t| measured.refs.iter().any(|&r| resolved.conforms(t, r)))
    }

    /// A definition's entry in [`Units::defs`].
    fn classify(
        resolved: &mut ResolvedModel,
        reference: ElementRef,
        def: ElementRef,
    ) -> Option<Option<QuantityDims>> {
        if !resolved.conforms(def, reference) {
            return None;
        }
        // The quantity types this definition, or the nearest definition
        // it specializes, is the unit of.
        let mut visited = HashSet::new();
        let mut frontier = VecDeque::from([def]);
        while let Some(d) = frontier.pop_front() {
            if !visited.insert(d) {
                continue;
            }
            let measured = resolved
                .quantity_types_for_unit_def(d)
                .into_iter()
                .find_map(|q| resolved.quantity_dims_of_type(q));
            if measured.is_some() {
                return Some(measured);
            }
            frontier.extend(resolved.explicit_supertypes(d));
        }
        Some(None)
    }
}

#[cfg(test)]
mod tests {
    use super::{Bracket, bracket_at};
    use crate::nav::completion_context;
    use crate::position::offset32;
    use sysmlv2_parser::ast::Dialect;

    /// What [`bracket_at`] makes of the bracket before the end of
    /// `text`, with the unit's declaration header spelled out.
    fn classify(text: &str) -> Option<Result<Option<&str>, ()>> {
        let cx = completion_context(text, offset32(text.len()), Dialect::Sysml);
        Some(match bracket_at(text, &cx, Dialect::Sysml)? {
            Bracket::Unit { header, .. } => {
                Ok(header.map(|h| &text[h.start as usize..h.end as usize]))
            }
            Bracket::Other => Err(()),
        })
    }

    #[test]
    fn a_bracket_after_a_value_opens_a_unit() {
        for (text, header) in [
            (
                "attribute g : DurationValue = 5.5 [",
                Some("attribute g : DurationValue "),
            ),
            (
                "attribute g : DurationValue = 5.5 [mi",
                Some("attribute g : DurationValue "),
            ),
            (
                "part def P { attribute :>> mass = -1500 [k",
                Some("attribute :>> mass "),
            ),
            (
                "attribute x : Real default = 1e3 [",
                Some("attribute x : Real "),
            ),
            ("attribute x := (a + b) [", Some("attribute x ")),
            ("attribute m = mass [", Some("attribute m ")),
            (
                "attribute <m> mass : MassValue = 5 [",
                Some("attribute <m> mass : MassValue "),
            ),
            // a factor of a larger value, or an argument
            ("attribute d : LengthValue = v * 2 [", None),
            ("attribute e = f(1 [", None),
            ("attribute e = f(x [", None),
            ("attribute m = 5 [kg] + 3 [", None),
            // an expression statement: a constraint's operands
            ("assert constraint { mass <= 2000 [", None),
            ("assert constraint { mass <= limit [", None),
            // the statement goes on past a body passed as an argument
            ("attribute e = f({ in z; z }, x [", None),
            // and starts on its own line below a quote left open
            (
                "attribute s = \"open\nattribute g : DurationValue = 5 [",
                Some("attribute g : DurationValue "),
            ),
        ] {
            assert_eq!(classify(text), Some(Ok(header)), "{text:?}");
        }
    }

    #[test]
    fn a_bracket_after_a_declaration_opens_a_multiplicity() {
        for text in [
            "part wheels : Wheel[",
            "part wheels : Wheel [0..",
            "part wheels [",
            "attribute <m> mass [",
            "attribute x : Real[0..1] = 5; part w : W [",
            "connect [",
            "first a then [",
            "end [",
            "attribute x = [",
            // a declaration in a body passed as an argument
            "attribute e = f({ in z : Real [",
        ] {
            assert_eq!(classify(text), Some(Err(())), "{text:?}");
        }
    }

    /// Where [`super::untyped_attribute`] puts the typing of the
    /// declaration before the end of `text`, spelled as what precedes it.
    fn untyped(text: &str) -> Option<&str> {
        let cx = completion_context(text, offset32(text.len()), Dialect::Sysml);
        let (name_end, _) = super::untyped_attribute(text, &cx)?;
        Some(&text[..name_end as usize])
    }

    #[test]
    fn an_untyped_attribute_is_read_on_tokens() {
        for (text, before) in [
            ("attribute m = 5 [k", Some("attribute m")),
            (
                "attribute <m> 'the mass' [1] = 5 [",
                Some("attribute <m> 'the mass'"),
            ),
            (
                "doc /* the attribute of it */ attribute m = 5 [",
                Some("doc /* the attribute of it */ attribute m"),
            ),
            ("attribute m : MassValue = 5 [", None),
            ("attribute m :>> mass = 5 [", None),
            ("attribute m redefines mass = 5 [", None),
            ("attribute :>> mass = 5 [", None),
            ("attribute redefines mass = 5 [", None),
            ("attribute subsets mass = 5 [", None),
            ("part p = 5 [", None),
            ("attribute m [", None),
            // the unit of an operand or an argument, not of the value
            ("attribute m = -5 [", Some("attribute m")),
            ("attribute d = v * 2 [", None),
            ("attribute m = f(5 [", None),
            ("attribute m = f({ in z; z }, 5 [", None),
            // on its own line below a quote left open
            (
                "attribute s = \"open\nattribute m = 5 [",
                Some("attribute s = \"open\nattribute m"),
            ),
        ] {
            assert_eq!(untyped(text), before, "{text:?}");
        }
    }

    /// A context spelled out: the operand, or the invoked name with the
    /// argument's position and the parameter it names.
    type Spelled<'a> = (&'a str, Option<(usize, Option<String>)>);

    /// What [`super::unit_context`] reads before the end of `text`.
    fn context(text: &str) -> Option<Spelled<'_>> {
        let cx = completion_context(text, offset32(text.len()), Dialect::Sysml);
        let spelled = |s: sysmlv2_parser::span::Span| &text[s.start as usize..s.end as usize];
        Some(match super::unit_context(text, &cx)? {
            super::Context::Operand(operand) => (spelled(operand), None),
            super::Context::Argument {
                callee,
                position,
                named,
            } => (spelled(callee), Some((position, named))),
        })
    }

    #[test]
    fn a_unit_brackets_context_is_read_on_tokens() {
        for (text, operand) in [
            ("assert constraint { mass <= 1500 [", "mass"),
            ("assert constraint { mass <= -1500 [", "mass"),
            ("assert constraint { v.mass > 1.5e3 [", "v.mass"),
            ("assert constraint { P::m == .5 [", "P::m"),
            ("attribute w = 1200 [kg] + 300 [", "1200 [kg]"),
            ("attribute t = total(parts).mass - 5 [", "total(parts).mass"),
            ("attribute t = xs#(1) - 5 [", "xs#(1)"),
            ("attribute t = (a + b) - 5 [", "(a + b)"),
            ("assert constraint { m <= 5 [kg] and s < 30 [", "s"),
        ] {
            assert_eq!(context(text), Some((operand, None)), "{text:?}");
        }
        for (text, callee, position, named) in [
            (
                "attribute e = KineticEnergy(1500 [",
                "KineticEnergy",
                0,
                None,
            ),
            (
                "attribute e = Calcs::KineticEnergy(1500 [kg], 20 [",
                "Calcs::KineticEnergy",
                1,
                None,
            ),
            ("attribute e = f(g(1, 2), (3), -4 [", "f", 2, None),
            ("attribute e = v.energy(v = 20 [", "v.energy", 0, Some("v")),
            ("attribute e = f(1, 'the v' = 20 [", "f", 1, Some("the v")),
            ("attribute e = f({ in z; z }, 20 [", "f", 1, None),
        ] {
            let named = named.map(str::to_string);
            assert_eq!(
                context(text),
                Some((callee, Some((position, named)))),
                "{text:?}"
            );
        }
        for text in [
            // a declaration's value, a factor, an operand beside a factor
            "attribute m : MassValue = 5 [",
            "attribute p = mass * 2 [",
            "assert constraint { 2 * mass <= 1500 [",
            // an index, a group, a step after `->`, a sequence
            "attribute e = xs#(3 [",
            "attribute e = (1500 [",
            "attribute e = xs->f(3 [",
            "attribute e = (1, 2 [",
        ] {
            assert_eq!(context(text), None, "{text:?}");
        }
    }

    #[test]
    fn no_bracket_outside_one() {
        for text in [
            "attribute g = 9.8 [m] + ",
            "attribute s = \"[",
            "doc /* see [",
            "attribute g = 9.8 [m;\n part p : ",
        ] {
            assert_eq!(classify(text), None, "{text:?}");
        }
    }
}
