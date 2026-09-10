//! Document outline: the syntax AST rendered as hierarchical
//! `DocumentSymbol`s — one response feeds VS Code's Outline view,
//! breadcrumbs, and sticky scroll.
//!
//! Pure syntax tier: one AST walk, no model, so the outline is live from
//! the first keystroke and survives parse errors (the tree is partial,
//! never absent). The discipline that matters is *containment* — VS Code
//! silently drops any symbol whose `selectionRange` is not inside its
//! `range` or whose children leak outside it — so every range here comes
//! from the member's own span and every selection from a name span inside
//! it (anonymous members select the empty range at their start).
//!
//! `SymbolKind` assignment: every KerML and SysML metaclass the syntax
//! tier distinguishes gets a deliberate kind, and the 26 kinds are
//! partitioned so each one belongs to exactly one declaration-keyword
//! color family (structure, value, behavior, connect, requirement,
//! package, metadata, flow-control, namespace plumbing). Clients theme
//! each kind's icon (`symbolIcon.*`) to its family color, so the outline
//! mirrors the editor's highlighting. Keep this partition in sync with
//! the workbench themes when changing any mapping below.

use crate::position::Mapper;
use lsp_types::{DocumentSymbol, SymbolKind};
use sysmlv2_parser::ast::{
    DefKind, Definition, FeatureSpecialization, Identification, Member, MemberKind, SourceUnit,
    TargetRef, Usage, UsageKind,
};
use sysmlv2_parser::span::Span;

/// Build the outline for one parsed unit over its source text.
pub fn document_symbols(unit: &SourceUnit, src: &str, mapper: &Mapper<'_>) -> Vec<DocumentSymbol> {
    let ctx = Ctx { src, mapper };
    walk(&unit.members, &ctx, false)
}

/// First `doc` body per declaration, keyed by the declared name's
/// start position (the outline's `selection_range.start`). Syntax-tier
/// like the outline itself, so completion can attach documentation
/// without a model build.
pub fn doc_bodies(
    unit: &SourceUnit,
    mapper: &Mapper<'_>,
) -> std::collections::HashMap<lsp_types::Position, String> {
    let mut out = std::collections::HashMap::new();
    collect_doc_bodies(&unit.members, mapper, &mut out);
    out
}

/// Short names of members declaring both spellings (`attribute
/// <'m/s²'> 'metre per second squared'`), keyed by the regular name's
/// position (the outline's selection anchor). The outline labels such
/// members by their regular name; the completion tier offers the short
/// symbol as its own item, since both are referenceable.
pub(crate) fn short_names(
    unit: &sysmlv2_parser::ast::SourceUnit,
    mapper: &Mapper<'_>,
) -> std::collections::HashMap<lsp_types::Position, String> {
    let mut out = std::collections::HashMap::new();
    collect_short_names(&unit.members, mapper, &mut out);
    out
}

fn collect_short_names(
    members: &[Member],
    mapper: &Mapper<'_>,
    out: &mut std::collections::HashMap<lsp_types::Position, String>,
) {
    for m in members {
        let (id, body) = match &m.kind {
            MemberKind::Package(p) => (&p.id, p.body.as_deref()),
            MemberKind::Definition(d) => (&d.id, d.body.as_deref()),
            MemberKind::Usage(u)
            | MemberKind::Subject(u)
            | MemberKind::Actor(u)
            | MemberKind::Stakeholder(u)
            | MemberKind::Objective(u)
            | MemberKind::RequirementConstraint { usage: u, .. } => {
                (&u.declaration.id, u.body.as_deref())
            }
            _ => continue,
        };
        if let (Some(short), Some(name)) = (&id.short_name, &id.name) {
            out.insert(mapper.position(name.span.start), short.value.clone());
        }
        if let Some(body) = body {
            collect_short_names(body, mapper, out);
        }
    }
}

fn collect_doc_bodies(
    members: &[Member],
    mapper: &Mapper<'_>,
    out: &mut std::collections::HashMap<lsp_types::Position, String>,
) {
    for m in members {
        let (id, body) = match &m.kind {
            MemberKind::Package(p) => (&p.id, p.body.as_deref()),
            MemberKind::Definition(d) => (&d.id, d.body.as_deref()),
            MemberKind::Usage(u)
            | MemberKind::Subject(u)
            | MemberKind::Actor(u)
            | MemberKind::Stakeholder(u)
            | MemberKind::Objective(u)
            | MemberKind::RequirementConstraint { usage: u, .. } => {
                (&u.declaration.id, u.body.as_deref())
            }
            _ => continue,
        };
        let Some(body) = body else { continue };
        let doc = body.iter().find_map(|b| match &b.kind {
            MemberKind::Doc(d) => Some(d.body.as_str()),
            _ => None,
        });
        if let Some(doc) = doc {
            let text = sysmlv2_parser::json::doc_display_text(doc);
            if !text.is_empty() {
                out.insert(mapper.position(sel(id, m.span).start), text);
            }
        }
        collect_doc_bodies(body, mapper, out);
    }
}

struct Ctx<'a> {
    src: &'a str,
    mapper: &'a Mapper<'a>,
}

impl Ctx<'_> {
    /// Exact source spelling of a reference target.
    fn spell(&self, t: &TargetRef) -> &str {
        t.span().slice(self.src)
    }
}

fn walk(members: &[Member], ctx: &Ctx<'_>, in_enum: bool) -> Vec<DocumentSymbol> {
    members
        .iter()
        .filter_map(|m| symbol(m, ctx, in_enum))
        .collect()
}

fn symbol(member: &Member, ctx: &Ctx<'_>, in_enum: bool) -> Option<DocumentSymbol> {
    let span = member.span;
    match &member.kind {
        MemberKind::Package(p) => {
            let (keyword, kind) = if p.is_namespace {
                ("namespace", SymbolKind::NAMESPACE)
            } else {
                ("package", SymbolKind::PACKAGE)
            };
            Some(node(
                name_of(&p.id, keyword),
                None,
                kind,
                span,
                sel(&p.id, span),
                p.body.as_deref().map(|b| walk(b, ctx, false)),
                ctx,
            ))
        }
        MemberKind::Definition(d) => Some(def_symbol(d, span, ctx)),
        MemberKind::Usage(u) => Some(usage_symbol(u, span, ctx, in_enum)),
        // Membership-shaped members carrying a usage: keep the usage,
        // labeled by the membership keyword when it is anonymous, and
        // kinded by the membership metaclass where it is more specific
        // than the carried usage's own kind.
        MemberKind::Subject(u) => Some(usage_kinded(u, span, ctx, "subject", SymbolKind::STRING)),
        MemberKind::Actor(u) => Some(usage_kinded(u, span, ctx, "actor", SymbolKind::STRING)),
        MemberKind::Stakeholder(u) => Some(usage_kinded(
            u,
            span,
            ctx,
            "stakeholder",
            SymbolKind::STRING,
        )),
        MemberKind::Objective(u) => {
            Some(usage_kinded(u, span, ctx, "objective", SymbolKind::STRING))
        }
        MemberKind::RequirementConstraint { usage, .. } => Some(usage_kinded(
            usage,
            span,
            ctx,
            "constraint",
            SymbolKind::OPERATOR,
        )),
        MemberKind::FramedConcern(u) => Some(usage_named(u, span, ctx, "frame")),
        MemberKind::RequirementVerification(u) => {
            Some(usage_kinded(u, span, ctx, "verify", SymbolKind::CONSTANT))
        }
        MemberKind::StateSubaction { action, .. } => {
            action.as_ref().map(|u| usage_named(u, span, ctx, "action"))
        }
        MemberKind::Render(u) => Some(usage_named(u, span, ctx, "render")),
        MemberKind::Return(u) => Some(usage_kinded(u, span, ctx, "return", SymbolKind::NULL)),
        MemberKind::Import(i) | MemberKind::Expose(i) => Some(node(
            i.target.to_display_string(),
            None,
            SymbolKind::MODULE,
            span,
            i.target.span,
            None,
            ctx,
        )),
        MemberKind::Alias(a) => Some(node(
            name_of(&a.id, "alias"),
            Some(format!("= {}", a.target.to_display_string())),
            SymbolKind::MODULE,
            span,
            sel(&a.id, span),
            None,
            ctx,
        )),
        MemberKind::Dependency(d) => Some(node(
            name_of(&d.id, "dependency"),
            None,
            SymbolKind::MODULE,
            span,
            sel(&d.id, span),
            None,
            ctx,
        )),
        // Annotations, filters, standalone relationships, control
        // memberships: not structural — no outline entry.
        _ => None,
    }
}

fn def_symbol(d: &Definition, span: Span, ctx: &Ctx<'_>) -> DocumentSymbol {
    let kind = match d.kind {
        // Structure family (part-like classifiers).
        DefKind::Part
        | DefKind::Item
        | DefKind::Occurrence
        | DefKind::Individual
        | DefKind::Class
        | DefKind::Classifier
        | DefKind::Extended => SymbolKind::CLASS,
        DefKind::Struct => SymbolKind::STRUCT,
        DefKind::Type => SymbolKind::TYPE_PARAMETER,
        // Value family (datatypes, calculations, constraints).
        DefKind::Attribute | DefKind::DataType => SymbolKind::NUMBER,
        DefKind::Enum => SymbolKind::ENUM,
        DefKind::Calc | DefKind::Function => SymbolKind::FUNCTION,
        DefKind::Constraint | DefKind::Predicate => SymbolKind::OPERATOR,
        // Behavior family.
        DefKind::Action | DefKind::State | DefKind::Behavior | DefKind::Interaction => {
            SymbolKind::METHOD
        }
        // Connect family (ports, connections, associations).
        DefKind::Port => SymbolKind::INTERFACE,
        DefKind::Connection
        | DefKind::Interface
        | DefKind::Flow
        | DefKind::Allocation
        | DefKind::Assoc
        | DefKind::AssocStruct => SymbolKind::CONSTRUCTOR,
        // Requirement family.
        DefKind::Requirement | DefKind::Concern => SymbolKind::OBJECT,
        DefKind::Case | DefKind::Analysis | DefKind::Verification | DefKind::UseCase => {
            SymbolKind::CONSTANT
        }
        DefKind::View | DefKind::Viewpoint | DefKind::Rendering => SymbolKind::FILE,
        // Metadata family.
        DefKind::Metadata | DefKind::Metaclass => SymbolKind::KEY,
    };
    let detail = (!d.specializes.is_empty()).then(|| {
        format!(
            ":> {}",
            d.specializes
                .iter()
                .map(|t| ctx.spell(t))
                .collect::<Vec<_>>()
                .join(", ")
        )
    });
    let in_enum = d.kind == DefKind::Enum;
    node(
        name_of(&d.id, def_keyword(d.kind)),
        detail,
        kind,
        span,
        sel(&d.id, span),
        d.body.as_deref().map(|b| walk(b, ctx, in_enum)),
        ctx,
    )
}

fn usage_symbol(u: &Usage, span: Span, ctx: &Ctx<'_>, in_enum: bool) -> DocumentSymbol {
    let kind = if in_enum && matches!(u.kind, UsageKind::Default | UsageKind::Enum) {
        SymbolKind::ENUM_MEMBER
    } else {
        match u.kind {
            // Structure family.
            UsageKind::Ref | UsageKind::Feature => SymbolKind::VARIABLE,
            // Value family.
            UsageKind::Attribute => SymbolKind::PROPERTY,
            UsageKind::Enum => SymbolKind::ENUM_MEMBER,
            UsageKind::Calc | UsageKind::Expr => SymbolKind::FUNCTION,
            UsageKind::BoolExpr | UsageKind::Invariant => SymbolKind::BOOLEAN,
            UsageKind::Constraint | UsageKind::AssertConstraint => SymbolKind::OPERATOR,
            // Behavior family: performed actions keep the action icon,
            // state-machine surface gets the event icon.
            UsageKind::Action | UsageKind::Perform | UsageKind::Step => SymbolKind::METHOD,
            UsageKind::State | UsageKind::Exhibit | UsageKind::Event | UsageKind::Transition => {
                SymbolKind::EVENT
            }
            // Connect family.
            UsageKind::Port => SymbolKind::INTERFACE,
            UsageKind::Connection
            | UsageKind::Interface
            | UsageKind::Flow
            | UsageKind::Succession
            | UsageKind::SuccessionFlow
            | UsageKind::Binding
            | UsageKind::Allocation
            | UsageKind::Connector
            | UsageKind::Message => SymbolKind::ARRAY,
            // Requirement family.
            UsageKind::Requirement | UsageKind::Concern | UsageKind::Satisfy => SymbolKind::OBJECT,
            UsageKind::Case
            | UsageKind::Analysis
            | UsageKind::Verification
            | UsageKind::UseCase
            | UsageKind::Include => SymbolKind::CONSTANT,
            UsageKind::View | UsageKind::Viewpoint | UsageKind::Rendering => SymbolKind::FILE,
            // Metadata family.
            UsageKind::Metadata => SymbolKind::KEY,
            // Control nodes and control-flow actions (flow-keyword family).
            UsageKind::Merge
            | UsageKind::Decide
            | UsageKind::Join
            | UsageKind::Fork
            | UsageKind::IfNode
            | UsageKind::WhileLoop
            | UsageKind::ForLoop
            | UsageKind::Accept
            | UsageKind::Send
            | UsageKind::Assign
            | UsageKind::Terminate => SymbolKind::NULL,
            // Plain structural usages (part, item, occurrence, …).
            _ => SymbolKind::FIELD,
        }
    };
    node(
        name_of(&u.declaration.id, usage_keyword(u.kind)),
        usage_detail(u, ctx),
        kind,
        span,
        sel(&u.declaration.id, span),
        u.body.as_deref().map(|b| walk(b, ctx, false)),
        ctx,
    )
}

/// A membership-carried usage labeled by the membership keyword when the
/// usage itself is anonymous.
fn usage_named(u: &Usage, span: Span, ctx: &Ctx<'_>, keyword: &str) -> DocumentSymbol {
    let mut s = usage_symbol(u, span, ctx, false);
    if u.declaration.id.is_empty() {
        s.name = format!("«{keyword}»");
    }
    s
}

/// `usage_named`, with the kind forced to the membership metaclass'
/// (the carried usage is often a plain reference whose own kind says
/// nothing about the membership's role).
fn usage_kinded(
    u: &Usage,
    span: Span,
    ctx: &Ctx<'_>,
    keyword: &str,
    kind: SymbolKind,
) -> DocumentSymbol {
    let mut s = usage_named(u, span, ctx, keyword);
    s.kind = kind;
    s
}

/// `: T1, T2 [mult]` from the declaration, spelled as in source.
fn usage_detail(u: &Usage, ctx: &Ctx<'_>) -> Option<String> {
    let mut parts = Vec::new();
    for s in &u.declaration.specializations {
        if let FeatureSpecialization::TypedBy(types) = s {
            let names: Vec<String> = types
                .iter()
                .map(|t| {
                    let spelled = ctx.spell(&t.target);
                    if t.is_conjugated {
                        format!("~{spelled}")
                    } else {
                        spelled.to_string()
                    }
                })
                .collect();
            parts.push(format!(": {}", names.join(", ")));
        }
    }
    if let Some(m) = &u.declaration.multiplicity {
        let spelled = m.span.slice(ctx.src);
        if spelled.starts_with('[') {
            parts.push(spelled.to_string());
        } else {
            parts.push(format!("[{spelled}]"));
        }
    }
    if parts.is_empty() {
        None
    } else {
        Some(parts.join(" "))
    }
}

/// Declared name: regular name preferred, short name as fallback,
/// `«keyword»` for anonymous members (positional structure stays visible).
fn name_of(id: &Identification, keyword: &str) -> String {
    id.name
        .as_ref()
        .or(id.short_name.as_ref())
        .map(|n| n.value.clone())
        .unwrap_or_else(|| format!("«{keyword}»"))
}

/// Selection span: the declared name, else the empty range at the member
/// start (always contained in the member range).
fn sel(id: &Identification, member: Span) -> Span {
    id.name
        .as_ref()
        .or(id.short_name.as_ref())
        .map(|n| n.span)
        .unwrap_or(Span::new(member.start, member.start))
}

#[allow(deprecated)] // DocumentSymbol's `deprecated` field must be filled
fn node(
    name: String,
    detail: Option<String>,
    kind: SymbolKind,
    span: Span,
    selection: Span,
    children: Option<Vec<DocumentSymbol>>,
    ctx: &Ctx<'_>,
) -> DocumentSymbol {
    // Containment backstop: a selection outside the member span (never
    // expected) degrades to the member start rather than being dropped
    // client-side.
    let selection = if selection.start >= span.start && selection.end <= span.end {
        selection
    } else {
        Span::new(span.start, span.start)
    };
    DocumentSymbol {
        name,
        detail,
        kind,
        tags: None,
        deprecated: None,
        range: ctx.mapper.range(span),
        selection_range: ctx.mapper.range(selection),
        children: children.filter(|c| !c.is_empty()),
    }
}

/// The declaration keyword for anonymous labels, spelled as in source.
fn def_keyword(kind: DefKind) -> &'static str {
    match kind {
        DefKind::Attribute => "attribute def",
        DefKind::Enum => "enum def",
        DefKind::Occurrence => "occurrence def",
        DefKind::Individual => "individual def",
        DefKind::Item => "item def",
        DefKind::Metadata => "metadata def",
        DefKind::Part => "part def",
        DefKind::Port => "port def",
        DefKind::Connection => "connection def",
        DefKind::Interface => "interface def",
        DefKind::Allocation => "allocation def",
        DefKind::Flow => "flow def",
        DefKind::Action => "action def",
        DefKind::State => "state def",
        DefKind::Calc => "calc def",
        DefKind::Constraint => "constraint def",
        DefKind::Requirement => "requirement def",
        DefKind::Concern => "concern def",
        DefKind::Case => "case def",
        DefKind::Analysis => "analysis def",
        DefKind::Verification => "verification def",
        DefKind::UseCase => "use case def",
        DefKind::View => "view def",
        DefKind::Viewpoint => "viewpoint def",
        DefKind::Rendering => "rendering def",
        DefKind::Extended => "def",
        DefKind::Type => "type",
        DefKind::Classifier => "classifier",
        DefKind::Class => "class",
        DefKind::Struct => "struct",
        DefKind::DataType => "datatype",
        DefKind::Assoc => "assoc",
        DefKind::AssocStruct => "assoc struct",
        DefKind::Behavior => "behavior",
        DefKind::Interaction => "interaction",
        DefKind::Function => "function",
        DefKind::Predicate => "predicate",
        DefKind::Metaclass => "metaclass",
    }
}

fn usage_keyword(kind: UsageKind) -> &'static str {
    match kind {
        UsageKind::Attribute => "attribute",
        UsageKind::Enum => "enum",
        UsageKind::Occurrence => "occurrence",
        UsageKind::Item => "item",
        UsageKind::Metadata => "metadata",
        UsageKind::Part => "part",
        UsageKind::Port => "port",
        UsageKind::Connection => "connection",
        UsageKind::Interface => "interface",
        UsageKind::Allocation => "allocation",
        UsageKind::Flow => "flow",
        UsageKind::Action => "action",
        UsageKind::State => "state",
        UsageKind::Calc => "calc",
        UsageKind::Constraint => "constraint",
        UsageKind::Requirement => "requirement",
        UsageKind::Concern => "concern",
        UsageKind::Case => "case",
        UsageKind::Analysis => "analysis",
        UsageKind::Verification => "verification",
        UsageKind::UseCase => "use case",
        UsageKind::View => "view",
        UsageKind::Viewpoint => "viewpoint",
        UsageKind::Rendering => "rendering",
        UsageKind::Ref => "ref",
        UsageKind::Default => "feature",
        UsageKind::Extended => "usage",
        UsageKind::Perform => "perform",
        UsageKind::Exhibit => "exhibit",
        UsageKind::Include => "include",
        UsageKind::Event => "event",
        UsageKind::Satisfy => "satisfy",
        UsageKind::AssertConstraint => "assert constraint",
        UsageKind::Succession => "succession",
        UsageKind::SuccessionFlow => "succession flow",
        UsageKind::Binding => "bind",
        UsageKind::Message => "message",
        UsageKind::Transition => "transition",
        UsageKind::Merge => "merge",
        UsageKind::Decide => "decide",
        UsageKind::Join => "join",
        UsageKind::Fork => "fork",
        UsageKind::Accept => "accept",
        UsageKind::Send => "send",
        UsageKind::Assign => "assign",
        UsageKind::Terminate => "terminate",
        UsageKind::IfNode => "if",
        UsageKind::WhileLoop => "while",
        UsageKind::ForLoop => "for",
        UsageKind::Feature => "feature",
        UsageKind::Step => "step",
        UsageKind::Expr => "expr",
        UsageKind::BoolExpr => "bool",
        UsageKind::Invariant => "inv",
        UsageKind::Connector => "connector",
    }
}
