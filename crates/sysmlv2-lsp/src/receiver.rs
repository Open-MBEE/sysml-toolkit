//! Member access in the completion tier (`tank.|`, `wheels#(1).|`,
//! `f(x).|`): the receiver written before the dot, and the element it
//! reaches in the completion session's model — the one whose members
//! the next step can name — and what an invocation of a callee binds:
//! its parameters and its result.

use sysmlv2_parser::ast::{Dialect, Expr, ExprKind, Name, QualifiedName, TargetRef};
use sysmlv2_parser::json::{ElementRef, ResolvedModel};
use sysmlv2_parser::span::Span;
use sysmlv2_parser::token::{Token, TokenKind};

/// A name chain (`a.b.|` → `a`, `b`) as the receiver expression it
/// spells. Built rather than parsed: the names are the document's own,
/// which in KerML may be words the SysML expression grammar reserves.
pub(crate) fn chain_expr(chain: &[String]) -> Expr {
    let name = |value: &String| QualifiedName {
        is_global: false,
        segments: vec![Name {
            value: value.clone(),
            span: Span::new(0, 0),
        }],
        span: Span::new(0, 0),
    };
    let mut links = chain.iter().map(name);
    let head = Expr {
        kind: links.next().map_or(ExprKind::Null, ExprKind::Ref),
        span: Span::new(0, 0),
    };
    links.fold(head, |target, member| Expr {
        kind: ExprKind::ChainStep {
            target: Box::new(target),
            member: TargetRef::Name(member),
        },
        span: Span::new(0, 0),
    })
}

/// The receiver's span when `partial_start` (the start of the word being
/// completed) follows a member-access dot: one that ends an index or an
/// invocation (`wheels#(1).|`, `f(x).liq|`), or whose chain starts with a
/// qualified name (`P::part.|`) — where a scan for a plain name chain
/// stops at the `)` or the `::`. Read backward over the tokens of the
/// statement starting at `stmt_start`: names joined by `.` or `::`, the
/// first possibly rooted at the global namespace (`$::`), index and
/// argument groups, a parenthesized head. `None` anywhere
/// else: after a number's decimal point, or a dot inside a comment or
/// note that starts within the statement (one that starts before
/// `stmt_start` is out of this scan's sight).
pub(crate) fn postfix_receiver(text: &str, stmt_start: u32, partial_start: u32) -> Option<Span> {
    use TokenKind as K;
    let prefix = text.get(stmt_start as usize..partial_start as usize)?;
    let tokens: Vec<Token> = sysmlv2_parser::lexer::tokenize(prefix)
        .0
        .into_iter()
        .filter(|t| !matches!(t.kind, K::Whitespace | K::Eof))
        .collect();
    let (dot, tokens) = tokens.split_last()?;
    if dot.kind != K::Dot {
        return None;
    }
    let i = receiver_start(tokens)?;
    Some(Span::new(
        stmt_start + tokens[i].span.start,
        stmt_start + dot.span.start,
    ))
}

/// The index of the first token of the receiver `tokens` end in, read
/// backward (see [`postfix_receiver`]); `None` when they end in
/// something else, or run out before its head.
pub(crate) fn receiver_start(tokens: &[Token]) -> Option<usize> {
    use TokenKind as K;
    let is_name = |k: Option<K>| matches!(k, Some(K::Ident | K::UnrestrictedName));
    let mut i = tokens.len();
    loop {
        // One operand, ending at `tokens[i - 1]`.
        match tokens[..i].last()?.kind {
            K::Ident | K::UnrestrictedName => i -= 1,
            K::RParen => {
                i = matching_open(&tokens[..i])?;
                let before = tokens[..i].last().map(|t| t.kind);
                if before == Some(K::Hash) {
                    // `x#(i)`: the operand indexed comes next.
                    i -= 1;
                    continue;
                }
                if !is_name(before) {
                    // `(expr)`: a parenthesized head.
                    break;
                }
                // `f(args)`: the name invoked.
                i -= 1;
            }
            _ => return None,
        }
        match tokens[..i].last().map(|t| t.kind) {
            // `$::a…`: the global namespace heads the name.
            Some(K::ColonColon) if i >= 2 && tokens[i - 2].kind == K::Dollar => {
                i -= 2;
                break;
            }
            Some(K::Dot | K::ColonColon) => i -= 1,
            _ => break,
        }
    }
    Some(i)
}

/// The receiver expression `text` spells in `dialect`. The expression
/// grammar reserves the SysML words; in KerML, where most of them are
/// ordinary names (`part`, `port`), those are quoted first.
pub(crate) fn parse_receiver(text: &str, dialect: Dialect) -> Option<Expr> {
    use sysmlv2_parser::parser::is_reserved;
    if dialect == Dialect::Sysml {
        return sysmlv2_parser::parser::parse_expression(text).expr;
    }
    let mut spelled = String::with_capacity(text.len());
    let mut at = 0;
    for t in sysmlv2_parser::lexer::tokenize(text).0 {
        let (start, end) = (t.span.start as usize, t.span.end as usize);
        let word = &text[start..end];
        if t.kind == TokenKind::Ident
            && is_reserved(Dialect::Sysml, word)
            && !is_reserved(Dialect::Kerml, word)
        {
            spelled.push_str(&text[at..start]);
            spelled.push('\'');
            spelled.push_str(word);
            spelled.push('\'');
            at = end;
        }
    }
    spelled.push_str(&text[at..]);
    sysmlv2_parser::parser::parse_expression(&spelled).expr
}

/// The index of the `(` matching the `)` that ends `tokens`; `None` when
/// the groups do not balance.
fn matching_open(tokens: &[Token]) -> Option<usize> {
    use TokenKind as K;
    let mut depth = 0usize;
    for (i, t) in tokens.iter().enumerate().rev() {
        match t.kind {
            K::RParen | K::RBracket | K::RBrace => depth += 1,
            K::LParen | K::LBracket | K::LBrace => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    return (t.kind == K::LParen).then_some(i);
                }
            }
            _ => {}
        }
    }
    None
}

/// The user declarations in `unit` whose extent holds offset `at`,
/// innermost first: the scopes a name written there resolves from.
pub(crate) fn enclosing_declarations(
    resolved: &ResolvedModel,
    unit: usize,
    at: u32,
) -> Vec<ElementRef> {
    let mut enclosing: Vec<(ElementRef, u32)> = resolved
        .user_elements()
        .filter_map(|e| {
            let (u, span) = resolved.member_extent(e)?;
            (u == unit && span.start <= at && at <= span.end).then(|| (e, span.len()))
        })
        .collect();
    enclosing.sort_by_key(|&(_, len)| len);
    enclosing.into_iter().map(|(e, _)| e).collect()
}

/// The element `receiver` reaches, resolved the way the evaluator
/// resolves it: a head name from the innermost of the `enclosing`
/// declarations outward, each chain step as a member of the element
/// before it, an indexed feature as itself (its elements have its
/// types), an invocation as its callee's result parameter. `None` for
/// what does not resolve and for any other expression.
pub(crate) fn receiver_element(
    resolved: &mut ResolvedModel,
    enclosing: &[ElementRef],
    receiver: &Expr,
) -> Option<ElementRef> {
    receiver_reached(resolved, enclosing, receiver, &mut Vec::new())
}

/// [`receiver_element`], recording in `reached` every element the
/// resolution reaches on the way — the head's, each step's, an
/// invocation's callee — and the one it returns: the declarations whose
/// text decides the answer.
pub(crate) fn receiver_reached(
    resolved: &mut ResolvedModel,
    enclosing: &[ElementRef],
    receiver: &Expr,
    reached: &mut Vec<ElementRef>,
) -> Option<ElementRef> {
    let hit = match &receiver.kind {
        ExprKind::Ref(name) => resolve_head(resolved, enclosing, name, reached),
        ExprKind::ChainStep { target, member } => {
            let target = receiver_reached(resolved, enclosing, target, reached)?;
            members_along(resolved, target, target_links(member), reached)
        }
        ExprKind::Index { target, .. } => receiver_reached(resolved, enclosing, target, reached),
        ExprKind::Invocation { ty, .. } => {
            let (head, rest) = target_links(ty).split_first()?;
            let callee = resolve_head(resolved, enclosing, head, reached)?;
            reached.push(callee);
            let callee = members_along(resolved, callee, rest, reached)?;
            result_parameter(resolved, callee)
        }
        _ => None,
    }?;
    reached.push(hit);
    Some(hit)
}

/// A reference's links: one qualified name, or a chain's.
fn target_links(target: &TargetRef) -> &[QualifiedName] {
    match target {
        TargetRef::Name(name) => std::slice::from_ref(name),
        TargetRef::Chain(links) => links,
    }
}

/// A head name, resolved from the innermost enclosing declaration
/// outward, the root namespace last — or, spelled from the global
/// namespace (`$::a`), from the root alone. Each namespace a qualified
/// name passes through on the way (`P` of `P::x`) is recorded in
/// `reached`.
fn resolve_head(
    resolved: &mut ResolvedModel,
    enclosing: &[ElementRef],
    name: &QualifiedName,
    reached: &mut Vec<ElementRef>,
) -> Option<ElementRef> {
    let root = resolved.root_scope();
    let mut resolve = |name: &QualifiedName| {
        if name.is_global {
            return resolved.resolve_in(root, name);
        }
        enclosing
            .iter()
            .find_map(|&e| resolved.member_of(e, name).map(|(hit, _)| hit))
            .or_else(|| resolved.resolve_in(root, name))
    };
    for len in 1..name.segments.len() {
        let path = QualifiedName {
            segments: name.segments[..len].to_vec(),
            ..name.clone()
        };
        reached.extend(resolve(&path));
    }
    resolve(name)
}

/// `from.l1.l2…`: each link resolved as a member of the element before
/// it, the way the evaluator steps a chain, each recorded in `reached`.
fn members_along(
    resolved: &mut ResolvedModel,
    from: ElementRef,
    links: &[QualifiedName],
    reached: &mut Vec<ElementRef>,
) -> Option<ElementRef> {
    links.iter().try_fold(from, |cur, link| {
        let hit = resolved.member_of(cur, link).map(|(hit, _)| hit)?;
        reached.push(hit);
        Some(hit)
    })
}

/// A callee's result parameter: its own `return`, else the nearest one
/// its written specializations declare (a calculation usage typed by
/// its definition, a definition specializing another).
pub(crate) fn result_parameter(
    resolved: &mut ResolvedModel,
    callee: ElementRef,
) -> Option<ElementRef> {
    nearest_in_heritage(resolved, callee, |resolved, e| {
        resolved.calc_return_param(e)
    })
}

/// The first answer `find` gives over `from` and its written heritage,
/// nearest first: what it is typed by or specializes, then theirs.
pub(crate) fn nearest_in_heritage<T>(
    resolved: &mut ResolvedModel,
    from: ElementRef,
    mut find: impl FnMut(&mut ResolvedModel, ElementRef) -> Option<T>,
) -> Option<T> {
    let mut visited = std::collections::HashSet::new();
    let mut frontier = std::collections::VecDeque::from([from]);
    while let Some(e) = frontier.pop_front() {
        if !visited.insert(e) {
            continue;
        }
        if let Some(found) = find(resolved, e) {
            return Some(found);
        }
        frontier.extend(resolved.explicit_supertypes(e));
    }
    None
}

/// The parameters an invocation of `callee` binds its arguments to, in
/// order, each with its name: the model's own reading of the callee's
/// written heritage (see `ResolvedModel::callable_parameters`), so
/// signature help lists exactly what an evaluation binds — the directed
/// features, the result aside, it owns, then each general's in the order
/// written, but for those its own redefine. An own parameter takes over
/// each general's at its place even when it also redefines one
/// explicitly: `calc def D :> Diff { in :>> b; }` has the one parameter
/// `b`. A callee whose heritage the model cannot read (a specialization
/// cycle) lists the parameters it owns.
pub(crate) fn parameters(
    resolved: &mut ResolvedModel,
    callee: ElementRef,
) -> Vec<(ElementRef, Option<String>)> {
    if let Some(parameters) = resolved.callable_parameters(callee) {
        return parameters
            .into_iter()
            .map(|p| (p.element, (!p.name.is_empty()).then_some(p.name)))
            .collect();
    }
    resolved
        .owned_features(callee)
        .into_iter()
        .filter(|&p| {
            resolved.declared_direction(p).is_some()
                && resolved.owning_membership_type(p) != Some("ReturnParameterMembership")
        })
        .map(|p| (p, feature_name(resolved, p)))
        .collect()
}

/// Whether an argument binds parameter `p`: an input, `in` or `inout`.
/// An invocation's arguments take the callee's inputs in order, so an
/// output holds no argument position (`f(x, y)` for `f { out o; in x;
/// in y; }`), as evaluation binds them.
pub(crate) fn binds_argument(resolved: &ResolvedModel, p: ElementRef) -> bool {
    resolved.declared_direction(p) != Some("out")
}

/// A feature's name — a parameter's, a callable's: the one declared,
/// else that of what it redefines as written (`in :>> m` is `m`, `calc
/// :>> ke` is `ke`).
pub(crate) fn feature_name(resolved: &ResolvedModel, e: ElementRef) -> Option<String> {
    resolved
        .element_name(e)
        .map(str::to_string)
        .or_else(|| resolved.element_lookup_name(e))
}

#[cfg(test)]
mod tests {
    use super::postfix_receiver;
    use crate::position::offset32;

    /// The receiver `postfix_receiver` reads before the end of `text`.
    fn receiver(text: &str) -> Option<&str> {
        let span = postfix_receiver(text, 0, offset32(text.len()))?;
        Some(&text[span.start as usize..span.end as usize])
    }

    #[test]
    fn index_and_invocation_receivers() {
        for (text, expected) in [
            ("attribute d = vehicle1.wheels#(1).", "vehicle1.wheels#(1)"),
            (
                "attribute e = KineticEnergy(1 [kg], 2 [m/s]).",
                "KineticEnergy(1 [kg], 2 [m/s])",
            ),
            ("attribute e = Calcs::f(x).", "Calcs::f(x)"),
            ("attribute e = a.f(x).g.", "a.f(x).g"),
            ("attribute e = xs#(1)#(2).", "xs#(1)#(2)"),
            ("attribute e = 2 * (a + b).", "(a + b)"),
            ("attribute e = 'my part'.", "'my part'"),
        ] {
            assert_eq!(receiver(text), Some(expected), "{text:?}");
        }
    }

    #[test]
    fn no_receiver_without_a_member_dot() {
        for text in [
            // a decimal point, a range, no dot at all
            "attribute x = 5.",
            "part w : Wheel [0..",
            "attribute e = f(x)",
            // a dot in a note or a string
            "attribute e = a. // see f(x).",
            "attribute s = \"f(x).",
            // groups that do not balance
            "attribute e = f(x)).",
            "attribute e = [x).",
        ] {
            assert_eq!(receiver(text), None, "{text:?}");
        }
    }
}
