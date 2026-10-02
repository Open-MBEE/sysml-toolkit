//! Answering the statement being typed off a model built from other
//! texts. What a member access reaches, the units a bracket takes, the
//! signature of the callable invoked: each such answer reads a few
//! declarations and looks up a few names, so a session already built —
//! for an earlier statement, or for navigation — answers as a new one
//! would wherever the texts it was built from differ from those a build
//! for the statement would read only where the answer does not look.
//!
//! [`Changes`] is where the two sets of texts differ, statement by
//! statement; [`Needs`] is what an answer read in the built model, which
//! [`Reach`] follows to the declarations whose text decides it and the
//! names their headers look up; [`Imports`] is what the session's imports
//! make every answer depend on; [`Changes::allow`] tells whether the
//! changes leave all that alone. Both err towards a build: a change the
//! check cannot place — one opening or closing a body, a unit that parses
//! in one set only, an import, a parameter that redefines by position, a
//! change where a recursive import sees — takes one.

use std::collections::HashSet;
use sysmlv2_parser::ast::{Dialect, Expr, ExprKind, Name, QualifiedName, TargetRef};
use sysmlv2_parser::json::{ElementRef, ResolvedModel};
use sysmlv2_parser::span::Span;
use sysmlv2_parser::token::{Token, TokenKind};
use sysmlv2_transform::Session;

/// What an answer read in the model it was read off.
#[derive(Default)]
pub(crate) struct Needs {
    /// The names it looked up.
    names: HashSet<String>,
    /// The declarations it read whole, and — through them — their
    /// general types.
    reads: Vec<ElementRef>,
    /// The declarations a name resolved from: their headers, and their
    /// general types whole.
    scopes: Vec<ElementRef>,
    /// Whether it listed the workspace's measurement units.
    units: bool,
}

impl Needs {
    /// A name the answer looked up.
    pub(crate) fn name(&mut self, name: &str) {
        self.names.insert(name.to_string());
    }

    /// Every segment of a name the answer looked up.
    pub(crate) fn qualified(&mut self, qn: &QualifiedName) {
        for segment in &qn.segments {
            self.name(&segment.value);
        }
    }

    /// Every name `expr` spells as a reference or a member step — the
    /// names resolving a receiver looks up.
    pub(crate) fn expr(&mut self, expr: &Expr) {
        match &expr.kind {
            ExprKind::Ref(qn) => self.qualified(qn),
            ExprKind::ChainStep { target, member } => {
                self.expr(target);
                self.target(member);
            }
            ExprKind::Index { target, .. } => self.expr(target),
            ExprKind::Invocation { ty, .. } => self.target(ty),
            _ => {}
        }
    }

    fn target(&mut self, target: &TargetRef) {
        match target {
            TargetRef::Name(qn) => self.qualified(qn),
            TargetRef::Chain(links) => links.iter().for_each(|qn| self.qualified(qn)),
        }
    }

    /// A declaration the answer read whole.
    pub(crate) fn read(&mut self, e: ElementRef) {
        self.reads.push(e);
    }

    /// The declarations a name was resolved from, innermost first.
    pub(crate) fn scopes(&mut self, enclosing: &[ElementRef]) {
        self.scopes.extend_from_slice(enclosing);
    }

    /// The answer listed the workspace's measurement units.
    pub(crate) fn units(&mut self) {
        self.units = true;
    }

    /// What reading a unit bracket's context — the operand its value is
    /// compared with or added to, or the callable it is an argument of
    /// (see [`crate::units::Context`]) — looks up: the names the operand
    /// or the callable's name spells, and the elements they resolve to,
    /// the unit an operand carries included, and the callable's
    /// parameters, its own and those it inherits, one of which the
    /// argument binds.
    pub(crate) fn context(
        &mut self,
        resolved: &mut ResolvedModel,
        enclosing: &[ElementRef],
        text: &str,
        context: &crate::units::Context,
        dialect: Dialect,
    ) {
        let span = match context {
            crate::units::Context::Operand(span) => span,
            crate::units::Context::Argument { callee, .. } => callee,
        };
        let Some(expr) = text
            .get(span.start as usize..span.end as usize)
            .and_then(|spelled| crate::receiver::parse_receiver(spelled, dialect))
        else {
            return;
        };
        let read = match &expr.kind {
            ExprKind::Bracket { arg, .. } => arg,
            _ => &expr,
        };
        self.expr(read);
        let reached = crate::receiver::receiver_reached(resolved, enclosing, read, &mut self.reads);
        if let (crate::units::Context::Argument { .. }, Some(callee)) = (context, reached) {
            let parameters = crate::receiver::parameters(resolved, callee);
            self.reads.extend(parameters.into_iter().map(|(p, _)| p));
        }
    }

    /// What reading the declaration `header` — a statement's text ahead
    /// of its value, declared in the innermost of `enclosing` — looks
    /// up: every name it spells, and the elements its types and the
    /// features it specializes or redefines resolve to, with the feature
    /// of its own name the innermost declaration has.
    pub(crate) fn declaration(
        &mut self,
        resolved: &mut ResolvedModel,
        enclosing: &[ElementRef],
        header: &str,
        dialect: Dialect,
    ) {
        for t in significant(header) {
            if let Some(name) = name_of(&t, header, dialect) {
                self.names.insert(name);
            }
        }
        let source = format!("{header};");
        let parse = match dialect {
            Dialect::Kerml => sysmlv2_parser::parser::parse_kerml_source(&source),
            Dialect::Sysml => sysmlv2_parser::parser::parse_source(&source),
        };
        let Some(usage) = parse.unit.members.last().and_then(|m| match &m.kind {
            sysmlv2_parser::ast::MemberKind::Usage(u)
            | sysmlv2_parser::ast::MemberKind::Return(u) => Some(u),
            _ => None,
        }) else {
            return;
        };
        let scope = enclosing
            .first()
            .and_then(|&e| resolved.element_scope(e))
            .unwrap_or_else(|| resolved.root_scope());
        for spec in &usage.declaration.specializations {
            use sysmlv2_parser::ast::FeatureSpecialization as F;
            let targets: Vec<&TargetRef> = match spec {
                F::TypedBy(types) => types.iter().map(|t| &t.target).collect(),
                F::Redefines(targets) | F::Subsets(targets) => targets.iter().collect(),
                _ => Vec::new(),
            };
            for target in targets {
                if let TargetRef::Name(qn) = target {
                    if let Some(e) = resolved.resolve_in(scope, qn) {
                        self.reads.push(e);
                    }
                }
            }
        }
        if let (Some(&owner), Some(name)) = (enclosing.first(), &usage.declaration.id.name) {
            let own = QualifiedName {
                is_global: false,
                segments: vec![name.clone()],
                span: Span::new(0, 0),
            };
            if let Some((e, _)) = resolved.member_of(owner, &own) {
                self.reads.push(e);
            }
        }
    }
}

/// Where the texts a session was built from differ from those a build
/// for the statement would read, and where the statement starts in the
/// built text of its unit.
pub(crate) struct Changes {
    /// The statement's start in the session's text of its unit.
    pub(crate) at: u32,
    units: Vec<Changed>,
}

/// One unit's changed statements.
struct Changed {
    name: String,
    /// Where they are in the built text: the bytes they span, or, where
    /// statements were only added, the gap between the tokens around
    /// them. A declaration overlapping it holds a change.
    lo: u32,
    hi: u32,
    /// Only added in the new text: `lo..hi` is a gap, not a span.
    insertion: bool,
    /// They sit at the unit's top level, among the root namespace's
    /// members.
    top: bool,
    /// Every name the headers of the changed statements, either text's,
    /// may declare or name them after.
    declared: HashSet<String>,
    /// A header holds what changes the names a namespace makes visible
    /// without spelling them (see [`OPAQUE`]).
    opaque: bool,
    /// The types and features the changed declarations, at any depth,
    /// are typed by, specialize, subset, or redefine: a unit declared or
    /// taken away is one typed by a measurement reference.
    targets: Vec<Target>,
}

impl Changed {
    /// Nothing changed yet in the unit `name`.
    fn new(name: String) -> Changed {
        Changed {
            name,
            lo: 0,
            hi: 0,
            insertion: false,
            top: false,
            declared: HashSet::new(),
            opaque: false,
            targets: Vec::new(),
        }
    }
}

/// A name a changed declaration's header refers to.
struct Target {
    name: QualifiedName,
    /// A redefinition's or a reference subsetting's target, resolved
    /// among the general types' features rather than from the
    /// declaration's scope.
    inherited: bool,
}

/// Words whose statements change what a namespace makes visible, or name
/// a feature after one they redefine without spelling it: imports and
/// what filters them, aliases, parameters and the memberships that
/// redefine by position or by kind, annotations, and the relationships a
/// KerML statement adds to elements declared elsewhere.
const OPAQUE: &[&str] = &[
    "actor",
    "alias",
    "assume",
    "conjugate",
    "conjugation",
    "disjoining",
    "disjoint",
    "do",
    "end",
    "entry",
    "exit",
    "expose",
    "featuring",
    "filter",
    "frame",
    "import",
    "in",
    "inout",
    "inverse",
    "member",
    "multiplicity",
    "objective",
    "out",
    "redefinition",
    "render",
    "require",
    "return",
    "specialization",
    "stakeholder",
    "subclassifier",
    "subject",
    "subset",
    "subtype",
    "typing",
    "verify",
];

/// A text's significant tokens: all but whitespace and notes.
fn significant(text: &str) -> Vec<Token> {
    sysmlv2_parser::lexer::tokenize(text)
        .0
        .into_iter()
        .filter(|t| !t.kind.is_trivia() && t.kind != TokenKind::Eof)
        .collect()
}

/// Whether a token ends a statement or opens or closes a body.
fn separates(t: &Token) -> bool {
    matches!(
        t.kind,
        TokenKind::Semi | TokenKind::LBrace | TokenKind::RBrace
    )
}

/// Whether `tokens` open and close their bodies alike, none closing one
/// opened before them.
fn balanced(tokens: &[Token]) -> bool {
    let mut depth = 0usize;
    for t in tokens {
        match t.kind {
            TokenKind::LBrace => depth += 1,
            TokenKind::RBrace => match depth.checked_sub(1) {
                Some(d) => depth = d,
                None => return false,
            },
            _ => {}
        }
    }
    depth == 0
}

/// A name token's name: an identifier that is no reserved word, or an
/// unrestricted name, unquoted.
fn name_of(t: &Token, text: &str, dialect: Dialect) -> Option<String> {
    let word = t.text(text);
    match t.kind {
        TokenKind::Ident if !sysmlv2_parser::parser::is_reserved(dialect, word) => {
            Some(word.to_string())
        }
        TokenKind::UnrestrictedName => Some(sysmlv2_parser::lexer::unescape(word)),
        _ => None,
    }
}

fn dialect(unit: &str) -> Dialect {
    if crate::is_kerml(unit) {
        Dialect::Kerml
    } else {
        Dialect::Sysml
    }
}

impl Changes {
    /// How `built` — the units a session was built from, by name, in
    /// its order — differs from `fresh`, the units a build for the
    /// statement starting at `at` in `unit` would read, and where the
    /// statement starts in the built text. `None` where the check cannot
    /// place a change: the units are not the same, a change opens or
    /// closes a body or holds a token in error, or the statement touches
    /// one.
    pub(crate) fn between<'a>(
        built: impl Iterator<Item = (&'a str, &'a str)>,
        fresh: &[(String, String)],
        unit: &str,
        at: u32,
    ) -> Option<Changes> {
        let built: Vec<(&str, &str)> = built.collect();
        if built.len() != fresh.len() {
            return None;
        }
        let mut units = Vec::new();
        let mut mapped = None;
        for ((name, old), (fresh_name, new)) in built.iter().zip(fresh) {
            if name != fresh_name {
                return None;
            }
            let here = *name == unit;
            if old == new {
                if here {
                    mapped = Some(at);
                }
                continue;
            }
            let diff = Diff::of(old, new)?;
            if here {
                mapped = Some(diff.map(old, at)?);
            }
            if let Some(changed) = diff.changed(name, old, new) {
                units.push(changed);
            }
        }
        Some(Changes { at: mapped?, units })
    }

    /// Whether an answer that read `needs` in `session` — the one these
    /// changes were taken against — is the answer a session built from
    /// the new texts would give: no changed statement holds an import or
    /// the like, declares a name at the top level or one the answer's
    /// names resolve through, declares, where the session's imports look,
    /// a name they look up, or lies in a declaration the answer read (see
    /// [`Reach`]) or one the imports bring members in from (see
    /// [`Imports`]).
    pub(crate) fn allow(&self, session: &mut Session, needs: &Needs, imports: &Imports) -> bool {
        if self.units.is_empty() {
            return true;
        }
        if self
            .units
            .iter()
            .any(|c| c.opaque || (c.top && !c.declared.is_empty()))
        {
            return false;
        }
        // The model's index of each changed unit.
        let Some(indices) = self
            .units
            .iter()
            .map(|c| {
                session
                    .units()
                    .find(|(_, n, _)| *n == c.name)
                    .map(|(i, _, _)| i)
            })
            .collect::<Option<Vec<usize>>>()
        else {
            return false;
        };
        if needs.units && !self.units_unchanged(session.resolved(), &indices) {
            return false;
        }
        let mut reach = Reach::default();
        reach.walk(session, &needs.scopes, &needs.reads, true);
        let named = |d: &String| needs.names.contains(d) || reach.names.contains(d);
        let read = |unit: usize, c: &Changed| {
            reach
                .spans
                .iter()
                .chain(&imports.reach.spans)
                .any(|&(u, s)| u == unit && s.start < c.hi && c.lo < s.end)
        };
        let resolved = session.resolved();
        self.units.iter().zip(&indices).all(|(c, &unit)| {
            // What the changed statements declare is a member of the
            // declaration around them, which the lookups behind the
            // imports' names see or not.
            let imported = || {
                around(resolved, unit, c).is_none_or(|a| imports.scopes.contains(&a))
                    && c.declared.iter().any(|d| imports.reach.names.contains(d))
            };
            !c.declared.iter().any(named) && !read(unit, c) && !imported()
        })
    }

    /// Whether the changed declarations leave the workspace's units as
    /// they are: none, at any depth, typed by, specializing, or
    /// redefining a measurement reference or a unit, as the built model
    /// resolves their targets from where they are declared, and none
    /// named as another member of the namespace around it. A target
    /// that does not resolve there, or whose first name the changes
    /// declare, cannot be told apart from one that does.
    fn units_unchanged(&self, resolved: &mut ResolvedModel, indices: &[usize]) -> bool {
        let Some(reference) =
            resolved.resolve_qualified("MeasurementReferences::TensorMeasurementReference")
        else {
            // No measurement reference: nothing is a unit.
            return true;
        };
        for (c, &unit) in self.units.iter().zip(indices) {
            let holder = around(resolved, unit, c);
            // A unit is listed by its qualified name, which another
            // declaration of its name beside it makes resolve elsewhere.
            if let Some(holder) = holder {
                let apart = |s: Span| s.end <= c.lo || c.hi <= s.start;
                let twice = resolved.owned_members(holder).into_iter().any(|m| {
                    [
                        resolved.element_name(m),
                        resolved.element_declared_short_name(m),
                    ]
                    .into_iter()
                    .flatten()
                    .any(|n| c.declared.contains(n))
                        && resolved
                            .member_extent(m)
                            .is_none_or(|(u, s)| u != unit || apart(s))
                });
                if twice {
                    return false;
                }
            }
            if c.targets.is_empty() {
                continue;
            }
            let scope = holder
                .and_then(|e| resolved.element_scope(e))
                .unwrap_or_else(|| resolved.root_scope());
            for target in &c.targets {
                let captured = !target.inherited
                    && target
                        .name
                        .segments
                        .first()
                        .is_some_and(|s| c.declared.contains(&s.value));
                let Some(t) = resolved
                    .resolve_in(scope, &target.name)
                    .filter(|_| !captured)
                else {
                    return false;
                };
                if resolved.conforms(t, reference)
                    || resolved
                        .typings(t)
                        .into_iter()
                        .any(|d| resolved.conforms(d, reference))
                {
                    return false;
                }
            }
        }
        true
    }
}

/// The innermost user declaration around the changed statements `c` of
/// `unit`: its body holds them.
fn around(resolved: &ResolvedModel, unit: usize, c: &Changed) -> Option<ElementRef> {
    resolved
        .user_elements()
        .filter_map(|e| {
            let (u, s) = resolved.member_extent(e)?;
            let holds = if c.insertion {
                s.start < c.hi && c.lo < s.end
            } else {
                s.start < c.lo && c.hi < s.end
            };
            (u == unit && holds).then(|| (e, s.len()))
        })
        .min_by_key(|&(_, len)| len)
        .map(|(e, _)| e)
}

/// The text an answer, or what a session's imports bring in, depends on
/// (see [`Reach::walk`]): the declarations whose text decides it, and the
/// names their headers look up — declaring one of those changes what the
/// header resolves to.
#[derive(Default)]
pub(crate) struct Reach {
    spans: Vec<(usize, Span)>,
    names: HashSet<String>,
    /// The namespaces the headers read resolve from.
    origins: HashSet<ElementRef>,
    /// The namespaces their qualified names look into (`P` of `P::T`).
    inside: HashSet<ElementRef>,
}

impl Reach {
    /// Takes in what `headers` and `whole` depend on. Of a declaration in
    /// `headers` — one a name resolved from or looked into, a namespace an
    /// import brings in the members of — its header: the names it spells;
    /// whole, the types and features its targets resolve to and the
    /// general types the model reports, which its members come from; as a
    /// header, each namespace a target's path looks into (`P` and `P::Q`
    /// of `P::Q::T`). Of one in `whole` — one an answer read — its whole
    /// text as well, and, with `members`, every namespace a member it
    /// inherits is declared in: a general type re-exporting what it
    /// imports, or one the inheritance walk reaches where the targets do
    /// not resolve as written. An element without a declaration of its
    /// own — the conjugate of a port definition — stands for the
    /// declaration that owns it. Library elements are left out: no
    /// workspace text changes them.
    pub(crate) fn walk(
        &mut self,
        session: &mut Session,
        headers: &[ElementRef],
        whole: &[ElementRef],
        members: bool,
    ) {
        let mut seen = HashSet::new();
        let mut walk: Vec<(ElementRef, bool)> = headers
            .iter()
            .map(|&e| (e, false))
            .chain(whole.iter().map(|&e| (e, true)))
            .collect();
        while let Some((e, entire)) = walk.pop() {
            if !seen.insert((e, entire)) {
                continue;
            }
            let resolved = session.resolved();
            if resolved.is_library_element(e) {
                continue;
            }
            let Some((unit, span)) = resolved.member_extent(e) else {
                walk.extend(resolved.owner(e).map(|owner| (owner, entire)));
                continue;
            };
            if entire {
                self.spans.push((unit, span));
            }
            walk.extend(
                resolved
                    .explicit_supertypes(e)
                    .into_iter()
                    .map(|t| (t, true)),
            );
            if members && entire {
                for m in resolved.inherited_memberships(e, false) {
                    walk.extend(resolved.owner(m).map(|owner| (owner, true)));
                }
            }
            // The header resolves from the namespace around it.
            let owner = resolved.owner(e);
            self.origins.extend(owner);
            let scope = owner
                .and_then(|owner| resolved.element_scope(owner))
                .unwrap_or_else(|| resolved.root_scope());
            let Some(header) = Header::of(session, unit, span) else {
                continue;
            };
            self.names.extend(header.names);
            let resolved = session.resolved();
            for target in &header.targets {
                let last = target.segments.len();
                for len in 1..=last {
                    let path = QualifiedName {
                        is_global: target.is_global,
                        segments: target.segments[..len].to_vec(),
                        span: Span::new(0, 0),
                    };
                    let Some(t) = resolved.resolve_in_excluding(scope, &path, Some(e)) else {
                        // Nothing further resolves: what the rest names is
                        // among the header's names.
                        break;
                    };
                    // A namespace on the way is looked into: its header, and
                    // its general types whole; the target, whole.
                    if len < last {
                        self.inside.insert(t);
                    }
                    walk.push((t, len == last));
                }
            }
        }
    }
}

/// A declaration's header — through its body's `{`, all of it without a
/// body — as resolving it reads it.
struct Header {
    /// Every name it spells.
    names: Vec<String>,
    /// What it is typed by, specializes, subsets, or redefines.
    targets: Vec<QualifiedName>,
}

impl Header {
    /// The header of the declaration spanning `span` of the session's
    /// unit `unit`; `None` for a unit the session holds no text of.
    fn of(session: &Session, unit: usize, span: Span) -> Option<Header> {
        let (_, name, text) = session.units().find(|(i, _, _)| *i == unit)?;
        let member = text.get(span.start as usize..span.end as usize)?;
        // A header ends early in a member's text: read that far first.
        let end = |tokens: &[Token]| {
            let mut depth = 0usize;
            tokens.iter().position(|t| {
                match t.kind {
                    TokenKind::LParen | TokenKind::LBracket => depth += 1,
                    TokenKind::RParen | TokenKind::RBracket => depth = depth.saturating_sub(1),
                    _ => {}
                }
                depth == 0 && t.kind == TokenKind::LBrace
            })
        };
        let near = member
            .char_indices()
            .nth(HEADER_BYTES)
            .map_or(member, |(i, _)| &member[..i]);
        let mut tokens = significant(near);
        let stop = match end(&tokens) {
            Some(stop) => stop,
            None if near.len() < member.len() => {
                tokens = significant(member);
                end(&tokens).unwrap_or(tokens.len())
            }
            None => tokens.len(),
        };
        let header = &tokens[..stop];
        let dialect = dialect(name);
        let mut scanned = Changed::new(String::new());
        scan(member, header, dialect, &mut scanned);
        Some(Header {
            names: header
                .iter()
                .filter_map(|t| name_of(t, member, dialect))
                .collect(),
            targets: scanned.targets.into_iter().map(|t| t.name).collect(),
        })
    }
}

/// How much of a member's text [`Header::of`] reads first.
const HEADER_BYTES: usize = 4096;

/// An import, alias, expose, or filter statement (see [`Imports::of`]).
struct Site {
    /// Its model unit, and where it starts there.
    unit: usize,
    at: u32,
    /// The qualified names it spells, in order: an import's target first.
    paths: Vec<QualifiedName>,
    /// It is a filter member, which filters its namespace's imports.
    filter: bool,
    /// A condition filters what it brings in.
    filtered: bool,
}

/// What a session's import, alias, expose, and filter statements make an
/// answer depend on: the names they spell — declaring one where they
/// look changes what they bring in — and what their targets' members
/// come from: a recursive import's target whole, as everything in it (a
/// recursive import sees into its nested namespaces, and into what the
/// types there inherit), and as a header each namespace an import
/// brings in the members of and each one their names look into (see
/// [`Reach::walk`]). Worked out once per session.
pub(crate) struct Imports {
    reach: Reach,
    /// The namespaces whose own members the lookups behind those names
    /// see: each that a lookup starts from, or passes on the way out, and
    /// each a namespace import brings the members of. Only a change
    /// declaring members of one of them can change what those names find.
    scopes: HashSet<ElementRef>,
}

impl Imports {
    pub(crate) fn of(session: &mut Session) -> Imports {
        let mut reach = Reach::default();
        // Where each such statement stands, by model unit, the qualified
        // names it spells, and whether a condition filters what it brings
        // in.
        let mut sites: Vec<Site> = Vec::new();
        // The names a filter's condition spells: what it evaluates reads
        // the metadata those name, their default values above all.
        let mut conditions: HashSet<String> = HashSet::new();
        for (unit, name, text) in session.units() {
            let dialect = dialect(name);
            let (mut statement, mut condition) = (false, 0usize);
            let mut path: Vec<Name> = Vec::new();
            for t in significant(text) {
                if t.kind == TokenKind::Ident
                    && matches!(t.text(text), "import" | "alias" | "expose" | "filter")
                {
                    statement = true;
                    let filter = t.text(text) == "filter";
                    condition = usize::from(filter);
                    sites.push(Site {
                        unit,
                        at: t.span.start,
                        paths: Vec::new(),
                        filter,
                        filtered: filter,
                    });
                    continue;
                }
                if !statement {
                    continue;
                }
                match t.kind {
                    TokenKind::LBracket => {
                        condition += 1;
                        if let Some(site) = sites.last_mut() {
                            site.filtered = true;
                        }
                    }
                    TokenKind::RBracket => condition = condition.saturating_sub(1),
                    _ => {}
                }
                let name = name_of(&t, text, dialect);
                if condition > 0 {
                    conditions.extend(name.clone());
                }
                if t.kind != TokenKind::ColonColon && name.is_none() && !path.is_empty() {
                    let segments = std::mem::take(&mut path);
                    if let Some(site) = sites.last_mut() {
                        site.paths.push(QualifiedName {
                            is_global: false,
                            segments,
                            span: Span::new(0, 0),
                        });
                    }
                }
                if separates(&t) {
                    statement = false;
                } else if let Some(name) = name {
                    reach.names.insert(name.clone());
                    path.push(Name {
                        value: name,
                        span: Span::new(0, 0),
                    });
                }
            }
        }
        let resolved = session.resolved();
        let elements: Vec<ElementRef> = resolved.user_elements().collect();
        let extent_of: Vec<(ElementRef, usize, Span)> = elements
            .iter()
            .filter_map(|&e| resolved.member_extent(e).map(|(u, s)| (e, u, s)))
            .collect();
        // A statement resolves its names from the declaration around it,
        // looking into each namespace they name. What a condition admits
        // depends on the metadata of each member it is asked of, as a
        // recursive import's target depends on all it holds: a filtered
        // import's target — each that a filter member's namespace imports —
        // is read the same way.
        let (mut origins, mut namespaces, mut recursive) = (Vec::new(), Vec::new(), Vec::new());
        for site in &sites {
            let origin = extent_of
                .iter()
                .filter(|&&(_, u, s)| u == site.unit && s.start < site.at && site.at < s.end)
                .min_by_key(|&&(_, _, s)| s.len())
                .map(|&(e, _, _)| e);
            origins.extend(origin);
            let scope = origin
                .and_then(|o| resolved.element_scope(o))
                .unwrap_or_else(|| resolved.root_scope());
            for (i, path) in site.paths.iter().enumerate() {
                for len in 1..=path.segments.len() {
                    let prefix = QualifiedName {
                        segments: path.segments[..len].to_vec(),
                        ..path.clone()
                    };
                    let Some(t) = resolved.resolve_in(scope, &prefix) else {
                        break;
                    };
                    if resolved.is_library_element(t) {
                        continue;
                    }
                    reach.inside.insert(t);
                    namespaces.push(t);
                    if site.filtered && !site.filter && i == 0 && len == path.segments.len() {
                        recursive.push(t);
                    }
                }
            }
            if let Some(origin) = origin.filter(|_| site.filter) {
                recursive.extend(
                    resolved
                        .import_details(origin)
                        .into_iter()
                        .map(|(t, ..)| t)
                        .filter(|&t| !resolved.is_library_element(t)),
                );
            }
        }
        for &e in &elements {
            for (target, namespace, deep, _) in resolved.import_details(e) {
                if resolved.is_library_element(target) {
                    continue;
                }
                if deep {
                    recursive.push(target);
                } else if namespace {
                    namespaces.push(target);
                }
            }
        }
        let extents: Vec<(usize, Span)> = recursive
            .iter()
            .filter_map(|&t| resolved.member_extent(t))
            .collect();
        let mut scopes: HashSet<ElementRef> =
            namespaces.iter().chain(&recursive).copied().collect();
        let mut whole = recursive;
        if !conditions.is_empty() {
            whole.extend(elements.iter().copied().filter(|&e| {
                resolved
                    .element_name(e)
                    .is_some_and(|n| conditions.contains(n))
            }));
        }
        if !extents.is_empty() {
            whole.extend(extent_of.iter().filter_map(|&(e, u, s)| {
                extents
                    .iter()
                    .any(|&(eu, es)| eu == u && es.start <= s.start && s.end <= es.end)
                    .then_some(e)
            }));
        }
        reach.walk(session, &namespaces, &whole, false);
        // Each namespace a lookup starts from, and those around it; each
        // one looked into.
        origins.extend(reach.origins.iter().copied());
        scopes.extend(reach.inside.iter().copied());
        let resolved = session.resolved();
        let mut climbed = HashSet::new();
        for origin in origins {
            let mut at = Some(origin);
            while let Some(e) = at.filter(|&e| climbed.insert(e)) {
                scopes.insert(e);
                at = resolved.owner(e);
            }
        }
        // What a recursive import's target holds is read with it.
        reach
            .spans
            .sort_by_key(|&(u, s)| (u, s.start, std::cmp::Reverse(s.end)));
        let mut kept: Vec<(usize, Span)> = Vec::new();
        for (u, s) in std::mem::take(&mut reach.spans) {
            if !kept
                .last()
                .is_some_and(|&(ku, k)| ku == u && k.start <= s.start && s.end <= k.end)
            {
                kept.push((u, s));
            }
        }
        reach.spans = kept;
        Imports { reach, scopes }
    }
}

/// A unit's significant tokens in the two texts, and how much of either
/// end the two share: `prefix` tokens from the start, `suffix` from the
/// end — widened to whole statements.
struct Diff {
    old: Vec<Token>,
    new: Vec<Token>,
    prefix: usize,
    suffix: usize,
}

impl Diff {
    /// `None` when the texts differ where the check cannot place it: in
    /// statements that open or close a body they do not close or open,
    /// or in a token in error.
    fn of(old_text: &str, new_text: &str) -> Option<Diff> {
        let (old, new) = (significant(old_text), significant(new_text));
        let same = |a: &Token, b: &Token| a.kind == b.kind && a.text(old_text) == b.text(new_text);
        let mut prefix = old.iter().zip(&new).take_while(|(a, b)| same(a, b)).count();
        let mut suffix = old[prefix..]
            .iter()
            .rev()
            .zip(new[prefix..].iter().rev())
            .take_while(|(a, b)| same(a, b))
            .count();
        if prefix == old.len() && prefix == new.len() {
            // Only whitespace and notes differ.
            return Some(Diff {
                old,
                new,
                prefix,
                suffix: 0,
            });
        }
        // Whole statements: the changed tokens start after a statement's
        // end or a brace, and end with one, in both texts.
        while prefix > 0 && !separates(&old[prefix - 1]) {
            prefix -= 1;
        }
        let ends = |tokens: &[Token], suffix: usize| {
            let end = tokens.len() - suffix;
            end == prefix || separates(&tokens[end - 1])
        };
        while suffix > 0 && !(ends(&old, suffix) && ends(&new, suffix)) {
            suffix -= 1;
        }
        let diff = Diff {
            old,
            new,
            prefix,
            suffix,
        };
        let (a, b) = (diff.old_changed(), diff.new_changed());
        let clean = |tokens: &[Token]| {
            balanced(tokens) && tokens.iter().all(|t| t.kind != TokenKind::Error)
        };
        (clean(a) && clean(b)).then_some(diff)
    }

    fn old_changed(&self) -> &[Token] {
        &self.old[self.prefix..self.old.len() - self.suffix]
    }

    fn new_changed(&self) -> &[Token] {
        &self.new[self.prefix..self.new.len() - self.suffix]
    }

    /// The position in the old text that the declarations around it
    /// hold as those around `at` hold it in the new one: the same gap
    /// between tokens, touching the same neighbors. `None` where no
    /// position does: inside a token, among the changed statements or
    /// against one, or between tokens the old text leaves no room
    /// between.
    fn map(&self, old_text: &str, at: u32) -> Option<u32> {
        let (old, new) = (&self.old, &self.new);
        // `at` is in the gap before `new[next]`, touching the tokens on
        // either side or not.
        let next = new.partition_point(|t| t.span.start < at);
        if next > 0 && new[next - 1].span.end > at {
            return None;
        }
        let touch_prev = next > 0 && new[next - 1].span.end == at;
        let touch_next = next < new.len() && new[next].span.start == at;
        let (first, last) = (self.prefix, new.len() - self.suffix);
        let old_last = old.len() - self.suffix;
        let changed = first < last || first < old_last;
        // The same gap in the old text, by the index of the token after it.
        let gap = if first < next && next < last {
            return None;
        } else if next < first || (next == first && !touch_next) {
            next
        } else if next > last || (next == last && !touch_prev) {
            old_last + (next - last)
        } else if changed {
            // Against a changed statement, or — none added here — against
            // both sides of those taken away.
            return None;
        } else {
            next
        };
        let prev_end = gap.checked_sub(1).map(|i| old[i].span.end);
        let next_start = old.get(gap).map(|t| t.span.start);
        match (touch_prev, touch_next) {
            (true, true) => prev_end.filter(|&p| next_start == Some(p)),
            (true, false) => prev_end.filter(|&p| next_start != Some(p)),
            (false, true) => next_start.filter(|&p| prev_end != Some(p)),
            (false, false) => {
                let lo = prev_end.map_or(0, |end| end + 1);
                let hi = next_start.map_or_else(
                    || crate::position::offset32(old_text.len()),
                    |start| start.saturating_sub(1),
                );
                (next_start.is_none_or(|start| start > 0) && lo <= hi).then_some(lo)
            }
        }
    }

    /// The changed statements of unit `name`, `None` where only
    /// whitespace and notes changed.
    fn changed(&self, name: &str, old_text: &str, new_text: &str) -> Option<Changed> {
        let (a, b) = (self.old_changed(), self.new_changed());
        if a.is_empty() && b.is_empty() {
            return None;
        }
        let (lo, hi, insertion) = match (a.first(), a.last()) {
            (Some(first), Some(last)) => (first.span.start, last.span.end, false),
            _ => {
                let lo = self
                    .prefix
                    .checked_sub(1)
                    .map_or(0, |i| self.old[i].span.end);
                let hi = self.old.get(self.prefix).map_or_else(
                    || crate::position::offset32(old_text.len()),
                    |t| t.span.start,
                );
                (lo, hi, true)
            }
        };
        let depth = self.old[..self.prefix]
            .iter()
            .fold(0isize, |d, t| match t.kind {
                TokenKind::LBrace => d + 1,
                TokenKind::RBrace => d - 1,
                _ => d,
            });
        let mut changed = Changed {
            lo,
            hi,
            insertion,
            top: depth <= 0,
            ..Changed::new(name.to_string())
        };
        let dialect = dialect(name);
        scan(old_text, a, dialect, &mut changed);
        scan(new_text, b, dialect, &mut changed);
        Some(changed)
    }
}

/// Reads the statements `tokens` of `text` (whole ones, at one level)
/// into `into`: what their headers may declare and whether one is
/// opaque (see [`OPAQUE`]), and what the headers at every depth refer
/// to.
fn scan(text: &str, tokens: &[Token], dialect: Dialect, into: &mut Changed) {
    let mut i = 0;
    while i < tokens.len() {
        i = statement(text, tokens, i, dialect, 0, into).max(i + 1);
    }
}

/// Reads the statement starting at `tokens[start]`, `depth` bodies below
/// the changed statements' level, into `into` (see [`scan`]); returns
/// where the next one starts — at the `}` closing the body around it,
/// when that ends it.
fn statement(
    text: &str,
    tokens: &[Token],
    start: usize,
    dialect: Dialect,
    depth: usize,
    into: &mut Changed,
) -> usize {
    use TokenKind as K;
    // What the header's names are: declared, or a list of targets.
    #[derive(PartialEq)]
    enum Mode {
        Names,
        Targets { inherited: bool },
    }
    let mut mode = Mode::Names;
    let mut path: Vec<Name> = Vec::new();
    let mut global = false;
    let finish = |path: &mut Vec<Name>, global: &mut bool, mode: &Mode, into: &mut Changed| {
        if let (false, Mode::Targets { inherited }) = (path.is_empty(), mode) {
            into.targets.push(Target {
                name: QualifiedName {
                    is_global: *global,
                    segments: std::mem::take(path),
                    span: Span::new(0, 0),
                },
                inherited: *inherited,
            });
        }
        path.clear();
        *global = false;
    };
    let mut i = start;
    let mut header = true;
    while i < tokens.len() {
        let t = &tokens[i];
        match t.kind {
            K::Semi => {
                finish(&mut path, &mut global, &mode, into);
                return i + 1;
            }
            K::LBrace => {
                finish(&mut path, &mut global, &mode, into);
                // The body: its statements are the member's own.
                i += 1;
                while i < tokens.len() && tokens[i].kind != K::RBrace {
                    i = statement(text, tokens, i, dialect, depth + 1, into).max(i + 1);
                }
                return i + 1;
            }
            K::RBrace => {
                finish(&mut path, &mut global, &mode, into);
                return i;
            }
            _ if !header => {}
            K::LParen | K::LBracket => {
                finish(&mut path, &mut global, &mode, into);
                mode = Mode::Names;
                // A multiplicity's bounds, a filter, or a connection's
                // ends: none is a target, and names inside are looked up.
                let close = if t.kind == K::LParen {
                    K::RParen
                } else {
                    K::RBracket
                };
                let mut nested = 0usize;
                while i < tokens.len() {
                    let k = tokens[i].kind;
                    if k == t.kind {
                        nested += 1;
                    } else if k == close {
                        nested -= 1;
                        if nested == 0 {
                            break;
                        }
                    } else if k == K::LBrace || k == K::Semi {
                        // A body expression or a statement's end: read on
                        // from there.
                        i -= 1;
                        break;
                    } else if depth == 0 {
                        if let Some(name) = name_of(&tokens[i], text, dialect) {
                            into.declared.insert(name);
                        }
                    }
                    i += 1;
                }
            }
            K::Eq | K::ColonEq => {
                finish(&mut path, &mut global, &mode, into);
                // The value: no declaration of the statement's own.
                header = false;
            }
            K::Colon | K::ColonGt | K::Tilde => {
                finish(&mut path, &mut global, &mode, into);
                mode = Mode::Targets { inherited: false };
            }
            K::ColonGtGt | K::ColonColonGt | K::FatArrow => {
                finish(&mut path, &mut global, &mode, into);
                mode = Mode::Targets { inherited: true };
            }
            K::Comma => finish(&mut path, &mut global, &mode, into),
            K::Dollar if matches!(mode, Mode::Targets { .. }) => global = true,
            K::ColonColon | K::Dot => {}
            K::At if depth == 0 => into.opaque = true,
            K::Ident | K::UnrestrictedName => {
                let word = t.text(text);
                // A metadata usage annotates the element around it, as `@`
                // does; a metadata definition declares a name like any other.
                let annotation =
                    word == "metadata" && tokens.get(i + 1).is_none_or(|t| t.text(text) != "def");
                if t.kind == K::Ident && depth == 0 && (OPAQUE.contains(&word) || annotation) {
                    into.opaque = true;
                }
                // The words that start or go on with a list of targets are
                // keywords wherever they stand, reserved or not.
                let switch = t.kind == K::Ident
                    && matches!(
                        word,
                        "typed"
                            | "defined"
                            | "by"
                            | "specializes"
                            | "subsets"
                            | "conjugates"
                            | "redefines"
                            | "references"
                            | "crosses"
                            | "default"
                    );
                let name = name_of(t, text, dialect);
                // Such a word that is no reserved one may name a feature,
                // too.
                if let Some(name) = name.as_ref().filter(|_| switch && depth == 0) {
                    into.declared.insert(name.clone());
                }
                match name.filter(|_| !switch) {
                    Some(name) => {
                        if matches!(mode, Mode::Names | Mode::Targets { inherited: true })
                            && depth == 0
                        {
                            into.declared.insert(name.clone());
                        }
                        if matches!(mode, Mode::Targets { .. }) {
                            path.push(Name {
                                value: name,
                                span: Span::new(0, 0),
                            });
                        }
                    }
                    None => {
                        finish(&mut path, &mut global, &mode, into);
                        mode = match word {
                            "typed" | "defined" | "specializes" | "subsets" | "conjugates" => {
                                Mode::Targets { inherited: false }
                            }
                            "redefines" | "references" | "crosses" => {
                                Mode::Targets { inherited: true }
                            }
                            // `by` goes on with the targets `typed` or
                            // `defined` started.
                            "by" if matches!(mode, Mode::Targets { .. }) => mode,
                            "default" => {
                                header = false;
                                Mode::Names
                            }
                            _ => Mode::Names,
                        };
                    }
                }
            }
            _ => {
                finish(&mut path, &mut global, &mode, into);
                mode = Mode::Names;
            }
        }
        i += 1;
    }
    tokens.len()
}

#[cfg(test)]
mod tests {
    use super::{Changed, Changes};

    /// The changes from `old` to `new`, where `|` marks the statement's
    /// start (and is no part of the text), for one unit.
    fn between(old: &str, new: &str) -> Option<Changes> {
        let at = new.find('|').expect("statement marker");
        let new = new.replacen('|', "", 1);
        Changes::between(
            std::iter::once(("u.sysml", old)),
            &[("u.sysml".to_string(), new)],
            "u.sysml",
            u32::try_from(at).expect("short"),
        )
    }

    /// The one changed unit of `old` → `new` (see [`between`]).
    fn changed(old: &str, new: &str) -> Changed {
        between(old, new)
            .expect("placed")
            .units
            .pop()
            .expect("a change")
    }

    fn declared(c: &Changed) -> Vec<&str> {
        let mut names: Vec<&str> = c.declared.iter().map(String::as_str).collect();
        names.sort_unstable();
        names
    }

    fn targets(c: &Changed) -> Vec<(String, bool)> {
        c.targets
            .iter()
            .map(|t| {
                let path: Vec<&str> = t.name.segments.iter().map(|s| s.value.as_str()).collect();
                (path.join("::"), t.inherited)
            })
            .collect()
    }

    const OLD: &str = "package P {\n    part def D {\n        \n    }\n}\n";

    #[test]
    fn a_statement_added_before_the_one_typed() {
        let new =
            "package P {\n    part def D {\n        attribute a = v.m;\n        |\n    }\n}\n";
        let changes = between(OLD, new).expect("placed");
        // Inside `D`'s body in the old text, touching neither brace.
        let open = OLD.find("D {").expect("body") + 3;
        let close = OLD.rfind("    }").expect("close") + 4;
        assert!(open < changes.at as usize && (changes.at as usize) < close);
        let c = &changes.units[0];
        assert!(c.insertion && !c.top && !c.opaque);
        assert_eq!(declared(c), ["a"]);
    }

    #[test]
    fn notes_and_whitespace_change_nothing() {
        let new = "package P {\n    // a note\n    part def D {\n\n        |\n    }\n}\n";
        let changes = between(OLD, new).expect("placed");
        assert!(changes.units.is_empty());
        assert_eq!(OLD.as_bytes()[changes.at as usize - 2], b'{');
    }

    #[test]
    fn what_opens_or_closes_a_body_is_not_placed() {
        for new in [
            "package P {\n    part def D {\n        part def E {\n        |\n    }\n}\n",
            "package P {\n    part def D {\n        }\n        |\n    }\n}\n",
            // A renamed body keeps its braces outside the change.
            "package Q {\n    part def D {\n        |\n    }\n}\n",
        ] {
            assert!(between(OLD, new).is_none(), "{new:?}");
        }
    }

    #[test]
    fn a_statement_against_a_change_is_not_placed() {
        let new = "package P {\n    part def D {\n        attribute a = 1;|\n    }\n}\n";
        assert!(between(OLD, new).is_none());
    }

    #[test]
    fn a_statement_taken_away() {
        let old =
            "package P {\n    part def D {\n        part a;\n        part b;\n        \n    }\n}\n";
        let new = "package P {\n    part def D {\n        part a;\n        |\n    }\n}\n";
        let changes = between(old, new).expect("placed");
        let c = &changes.units[0];
        assert!(!c.insertion);
        assert_eq!(declared(c), ["b"]);
        // Outside what was taken away.
        let taken = old.find("part b;").expect("b");
        let at = changes.at as usize;
        assert!(at < taken || at > taken + "part b;".len(), "{at}");
    }

    #[test]
    fn opaque_statements() {
        for (statement, opaque) in [
            ("private import Q::*;", true),
            ("in x : T;", true),
            ("return r : R;", true),
            ("@Safety;", true),
            ("metadata Safety;", true),
            ("alias A for B;", true),
            ("entry action a;", true),
            ("end e : E;", true),
            ("metadata def M;", false),
            ("part p : P;", false),
            ("attribute :>> mass = 1;", false),
            ("part q { in x; import R::*; }", false),
            ("attribute x = s->select { in p; p > 0 };", false),
        ] {
            let new = OLD.replace("        \n", &format!("        {statement}\n        |\n"));
            assert_eq!(changed(OLD, &new).opaque, opaque, "{statement}");
        }
    }

    #[test]
    fn declared_names_and_targets() {
        for (statement, names, refs) in [
            (
                "attribute m : MassValue = 5 [kg];",
                &["m"][..],
                &[("MassValue", false)][..],
            ),
            (
                "attribute :>> mass = 1500 [kg];",
                &["mass"],
                &[("mass", true)],
            ),
            (
                "part def Car :> Vehicle { part e : Engine; }",
                &["Car"],
                &[("Vehicle", false), ("Engine", false)],
            ),
            ("port p : ~FuelPort;", &["p"], &[("FuelPort", false)]),
            ("attribute x : ISQ::T;", &["x"], &[("ISQ::T", false)]),
            ("perform providePower;", &["providePower"], &[]),
            // A bound is looked up, not declared; it counts all the same.
            (
                "part <s> 'short one' : S [0..n];",
                &["n", "s", "short one"],
                &[("S", false)],
            ),
            (
                "ref :>> a.b : T;",
                &["a", "b"],
                &[("a::b", true), ("T", false)],
            ),
        ] {
            let new = OLD.replace("        \n", &format!("        {statement}\n        |\n"));
            let c = changed(OLD, &new);
            assert_eq!(declared(&c), names, "{statement}");
            let expected: Vec<(String, bool)> =
                refs.iter().map(|&(n, i)| (n.to_string(), i)).collect();
            assert_eq!(targets(&c), expected, "{statement}");
        }
    }

    #[test]
    fn top_level_statements() {
        let old = "part def A;\n\n";
        let c = changed(old, "part def A;\npart def B;\n|\n");
        assert!(c.top);
        assert_eq!(declared(&c), ["B"]);
        let c = changed(
            OLD,
            &OLD.replace("        \n", "        part b;\n        |\n"),
        );
        assert!(!c.top);
    }
}
