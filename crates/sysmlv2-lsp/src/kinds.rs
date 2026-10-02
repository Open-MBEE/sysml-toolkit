//! What a completion candidate names, and which kinds of element a
//! position takes.
//!
//! Every symbol completion offers carries a [`Decl`]: whether its
//! declaration is a namespace, a definition (a SysML `… def` or a KerML
//! type) of some kind, or a usage (a SysML usage or a KerML feature) of
//! some kind — read off the syntax tree like the outline, so it costs no
//! model build. Positions admit and rank candidates by it, following the
//! metamodel: an attribute is typed by data types (attribute and
//! enumeration definitions among them), a part by part definitions, a
//! definition specializes definitions of its own kind or of the kinds
//! its kind specializes, and a usage of a kind is one of every kind its
//! kind specializes too (a part usage is an item usage).

use crate::position::Mapper;
use std::collections::{HashMap, HashSet};
use sysmlv2_parser::ast::{
    DefKind, FeatureSpecialization, Identification, Member, MemberKind, QualifiedName, SourceUnit,
    TargetRef, Usage, UsageKind,
};
use sysmlv2_parser::span::Span;

/// What a symbol's declaration is.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Decl {
    /// A package or namespace.
    Namespace,
    /// A definition or KerML type, by its kind keyword.
    Definition(DefKind),
    /// A usage or KerML feature, by its kind keyword; one declared
    /// without a kind keyword (`x : T;`) is [`UsageKind::Default`].
    Usage(UsageKind),
    /// Anything else the outline names: a dependency, an alias the
    /// symbol tables cannot follow to what it names.
    Other,
}

/// A declaration as completion reads it: what it declares, and the
/// types it names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Declared {
    pub decl: Decl,
    /// The names, last segment only, of the types a usage is typed by or
    /// a definition specializes, as written.
    pub types: Vec<String>,
}

impl Declared {
    fn other() -> Declared {
        Declared {
            decl: Decl::Other,
            types: Vec::new(),
        }
    }
}

/// Every named member of `unit` as [`Declared`], keyed by the position
/// the outline selects for it (its name, else its short name). An alias
/// declares nothing of its own: the symbol table it is indexed in takes
/// it as what its target names.
pub(crate) fn declarations(
    unit: &SourceUnit,
    mapper: &Mapper<'_>,
) -> HashMap<lsp_types::Position, Declared> {
    let mut out = HashMap::new();
    collect(&unit.members, mapper, &mut out);
    out
}

/// The member's identification, declaration, and body, when it declares
/// something.
fn declared(m: &Member) -> Option<(&Identification, Declared, Option<&[Member]>)> {
    let names = |targets: &mut dyn Iterator<Item = &TargetRef>| -> Vec<String> {
        targets
            .filter_map(|t| match t {
                TargetRef::Name(qn) => qn.segments.last().map(|s| s.value.clone()),
                _ => None,
            })
            .collect()
    };
    match &m.kind {
        MemberKind::Package(p) => Some((
            &p.id,
            Declared {
                decl: Decl::Namespace,
                types: Vec::new(),
            },
            p.body.as_deref(),
        )),
        MemberKind::Definition(d) => Some((
            &d.id,
            Declared {
                decl: Decl::Definition(d.kind),
                types: names(&mut d.specializes.iter()),
            },
            d.body.as_deref(),
        )),
        MemberKind::Dependency(d) => Some((&d.id, Declared::other(), None)),
        _ => {
            let u = usage(m)?;
            let mut typings = u.declaration.specializations.iter().flat_map(|s| match s {
                FeatureSpecialization::TypedBy(types) => types.iter().map(|t| &t.target).collect(),
                _ => Vec::new(),
            });
            Some((
                &u.declaration.id,
                Declared {
                    decl: Decl::Usage(u.kind),
                    types: names(&mut typings),
                },
                u.body.as_deref(),
            ))
        }
    }
}

/// The usage member `m` declares, whatever membership owns it.
pub(crate) fn usage(m: &Member) -> Option<&Usage> {
    match &m.kind {
        MemberKind::Usage(u)
        | MemberKind::Subject(u)
        | MemberKind::Actor(u)
        | MemberKind::Stakeholder(u)
        | MemberKind::Objective(u)
        | MemberKind::FramedConcern(u)
        | MemberKind::RequirementVerification(u)
        | MemberKind::Render(u)
        | MemberKind::Return(u)
        | MemberKind::RequirementConstraint { usage: u, .. }
        | MemberKind::StateSubaction {
            action: Some(u), ..
        } => Some(u),
        _ => None,
    }
}

/// A declaration whose body holds an offset, as the live text writes it
/// (see [`enclosing`]).
pub(crate) struct Enclosing {
    /// Its name, else its short name, else the name of the feature it
    /// redefines; `None` for an anonymous one (`@Safety { … }`, `part :
    /// Wheel { … }`).
    pub name: Option<String>,
    /// The types it names, qualified as written: a usage's typings, a
    /// definition's specializations.
    pub types: Vec<QualifiedName>,
    /// What it declares.
    pub decl: Decl,
    /// The whole member, its body included.
    pub span: Span,
}

/// The declarations of `unit` whose bodies hold byte offset `at`,
/// outermost first — those in an expression's body too (`forAll { …
/// attribute t : T { … } … }`) — and the innermost's body, the unit's
/// members when none holds it. The named ones spell the innermost's
/// qualified name, which finds it in a model built from an earlier text
/// as well.
pub(crate) fn enclosing(unit: &SourceUnit, at: u32) -> (Vec<Enclosing>, &[Member]) {
    let mut out = Vec::new();
    let mut members: &[Member] = &unit.members;
    while let Some((m, id, declared, body)) = declaration_around(members, at) {
        out.push(Enclosing {
            name: id
                .name
                .as_ref()
                .or(id.short_name.as_ref())
                .map(|n| n.value.clone())
                .or_else(|| redefined_name(m)),
            types: written_types(m),
            decl: declared.decl,
            span: m.span,
        });
        members = body;
    }
    (out, members)
}

/// The member of `members` holding byte offset `at` when it declares
/// something with a body, else the declaration with a body holding it
/// in that member's expression body (a constraint's `forAll { … }`, a
/// select's `?{ … }`): with its identification, what it declares, and
/// its body.
fn declaration_around(
    members: &[Member],
    at: u32,
) -> Option<(&Member, &Identification, Declared, &[Member])> {
    let m = members
        .iter()
        .find(|m| m.span.start < at && at < m.span.end)?;
    match declared(m) {
        Some((id, declared, Some(body))) => Some((m, id, declared, body)),
        _ => declaration_around(expression_body(m, at)?, at),
    }
}

/// The members of the expression body in `m` holding byte offset `at`.
fn expression_body(m: &Member, at: u32) -> Option<&[Member]> {
    use sysmlv2_parser::ast::{Expr, ExprKind};
    use sysmlv2_parser::visit::{Visit, walk_expr};
    struct Find<'a> {
        at: u32,
        found: Option<&'a [Member]>,
    }
    impl<'a> Visit<'a> for Find<'a> {
        fn visit_expr(&mut self, e: &'a Expr) {
            if self.found.is_some() || !(e.span.start < self.at && self.at < e.span.end) {
                return;
            }
            if let ExprKind::Body { members } = &e.kind {
                self.found = Some(members);
            } else {
                walk_expr(self, e);
            }
        }
    }
    let mut find = Find { at, found: None };
    find.visit_member(m);
    find.found
}

/// The members of `body` other than the statement being typed, which
/// starts at byte offset `at`.
fn settled(body: &[Member], at: u32) -> impl Iterator<Item = &Member> {
    body.iter()
        .filter(move |m| !(m.span.start <= at && at < m.span.end.max(m.span.start + 1)))
}

/// The features `body` declares, but for the statement being typed at
/// `at`: each with the name it is found by — a redefinition declaring
/// none by the feature it redefines — and what it declares.
pub(crate) fn body_features(body: &[Member], at: u32) -> Vec<(String, Decl)> {
    settled(body, at)
        .filter_map(|m| {
            let (id, declared, _) = declared(m)?;
            if !matches!(declared.decl, Decl::Usage(_)) {
                return None;
            }
            let name = id
                .name
                .as_ref()
                .or(id.short_name.as_ref())
                .map(|n| n.value.clone())
                .or_else(|| redefined_name(m))?;
            Some((name, declared.decl))
        })
        .collect()
}

/// The names of the features the members of `body` redefine, but for
/// the statement being typed at `at`, last segment only — and those
/// they redefine without naming them: a `subject` the library's `subj`
/// every case and requirement has, a `return` parameter the `result`
/// every calculation has.
pub(crate) fn redefined_names(body: &[Member], at: u32) -> HashSet<String> {
    let mut names: HashSet<String> = settled(body, at)
        .filter_map(usage)
        .flat_map(|u| &u.declaration.specializations)
        .filter_map(|s| match s {
            FeatureSpecialization::Redefines(targets) => Some(targets),
            _ => None,
        })
        .flatten()
        .filter_map(|t| match t {
            TargetRef::Name(qn) => qn.segments.last().map(|s| s.value.clone()),
            _ => None,
        })
        .collect();
    for m in settled(body, at) {
        match m.kind {
            MemberKind::Subject(_) => names.insert("subj".to_string()),
            MemberKind::Return(_) => names.insert("result".to_string()),
            _ => false,
        };
    }
    names
}

/// The name a usage declaring none takes from the first feature it
/// redefines (`part :>> engine { … }` is named `engine`), as the model
/// names it.
fn redefined_name(m: &Member) -> Option<String> {
    let redefined = usage(m)?
        .declaration
        .specializations
        .iter()
        .find_map(|s| match s {
            FeatureSpecialization::Redefines(targets) => targets.first(),
            _ => None,
        })?;
    match redefined {
        TargetRef::Name(qn) => qn.segments.last().map(|s| s.value.clone()),
        _ => None,
    }
}

/// The types member `m` names, qualified as written: a usage's typings,
/// a definition's specializations.
fn written_types(m: &Member) -> Vec<QualifiedName> {
    let name = |t: &TargetRef| match t {
        TargetRef::Name(qn) => Some(qn.clone()),
        _ => None,
    };
    if let MemberKind::Definition(d) = &m.kind {
        return d.specializes.iter().filter_map(name).collect();
    }
    usage(m).map_or_else(Vec::new, |u| {
        u.declaration
            .specializations
            .iter()
            .flat_map(|s| match s {
                FeatureSpecialization::TypedBy(types) => {
                    types.iter().filter_map(|t| name(&t.target)).collect()
                }
                _ => Vec::new(),
            })
            .collect()
    })
}

fn collect(
    members: &[Member],
    mapper: &Mapper<'_>,
    out: &mut HashMap<lsp_types::Position, Declared>,
) {
    for m in members {
        let Some((id, declared, body)) = declared(m) else {
            continue;
        };
        out.insert(mapper.position(selection(id, m.span).start), declared);
        if let Some(body) = body {
            collect(body, mapper, out);
        }
    }
}

/// The measurement-unit types among `definitions` — (name, the names it
/// specializes) pairs: the standard library's measurement-unit type,
/// given by its `root` name, and every definition specializing one of
/// them, transitively, following the specializations the declarations
/// write. `known` holds unit types already established (the library's,
/// when extending them with a workspace's definitions).
pub(crate) fn unit_types<'a>(
    root: Option<&str>,
    known: &HashSet<String>,
    definitions: impl IntoIterator<Item = (&'a str, &'a [String])>,
) -> HashSet<String> {
    let definitions: Vec<(&str, &[String])> = definitions.into_iter().collect();
    let mut units: HashSet<String> = known.clone();
    units.extend(root.map(str::to_string));
    loop {
        let before = units.len();
        for &(name, supers) in &definitions {
            if !units.contains(name) && supers.iter().any(|s| units.contains(s)) {
                units.insert(name.to_string());
            }
        }
        if units.len() == before {
            return units;
        }
    }
}

/// The span the outline selects for a declaration: its name, else its
/// short name, else the empty span at the member's start.
fn selection(id: &Identification, member: Span) -> Span {
    id.name
        .as_ref()
        .or(id.short_name.as_ref())
        .map(|n| n.span)
        .unwrap_or_else(|| Span::new(member.start, member.start))
}

/// The declaration kind of a feature from its abstract-syntax metaclass
/// name (`AttributeUsage`, `ActionUsage`, `Feature`), for features a
/// semantic session reports rather than the syntax tree.
pub(crate) fn feature_decl(metaclass: &str) -> Decl {
    use UsageKind as U;
    let kind = match metaclass {
        "AttributeUsage" => U::Attribute,
        "EnumerationUsage" => U::Enum,
        "OccurrenceUsage" => U::Occurrence,
        "EventOccurrenceUsage" => U::Event,
        "ItemUsage" => U::Item,
        "MetadataUsage" | "MetadataFeature" => U::Metadata,
        "PartUsage" => U::Part,
        "PortUsage" => U::Port,
        "ConnectionUsage" => U::Connection,
        "InterfaceUsage" => U::Interface,
        "AllocationUsage" => U::Allocation,
        "FlowUsage" | "Flow" => U::Flow,
        "SuccessionFlowUsage" | "SuccessionFlow" => U::SuccessionFlow,
        "ActionUsage" => U::Action,
        "PerformActionUsage" => U::Perform,
        "StateUsage" => U::State,
        "ExhibitStateUsage" => U::Exhibit,
        "TransitionUsage" => U::Transition,
        "CalculationUsage" => U::Calc,
        "ConstraintUsage" => U::Constraint,
        "AssertConstraintUsage" => U::AssertConstraint,
        "RequirementUsage" => U::Requirement,
        "SatisfyRequirementUsage" => U::Satisfy,
        "ConcernUsage" => U::Concern,
        "CaseUsage" => U::Case,
        "AnalysisCaseUsage" => U::Analysis,
        "VerificationCaseUsage" => U::Verification,
        "UseCaseUsage" => U::UseCase,
        "IncludeUseCaseUsage" => U::Include,
        "ViewUsage" => U::View,
        "ViewpointUsage" => U::Viewpoint,
        "RenderingUsage" => U::Rendering,
        "ReferenceUsage" => U::Ref,
        "SuccessionAsUsage" | "Succession" => U::Succession,
        "BindingConnectorAsUsage" | "BindingConnector" => U::Binding,
        "AcceptActionUsage" => U::Accept,
        "SendActionUsage" => U::Send,
        "AssignmentActionUsage" => U::Assign,
        "TerminateActionUsage" => U::Terminate,
        "IfActionUsage" => U::IfNode,
        "WhileLoopActionUsage" => U::WhileLoop,
        "ForLoopActionUsage" => U::ForLoop,
        "MergeNode" => U::Merge,
        "DecisionNode" => U::Decide,
        "JoinNode" => U::Join,
        "ForkNode" => U::Fork,
        "Step" => U::Step,
        "Expression" => U::Expr,
        "BooleanExpression" => U::BoolExpr,
        "Invariant" => U::Invariant,
        "Connector" => U::Connector,
        "Feature" => U::Feature,
        _ => return Decl::Other,
    };
    Decl::Usage(kind)
}

/// Every definition kind: what a reference usage, a KerML feature, or a
/// parameter declared without a kind keyword may be typed by.
pub(crate) const ALL_DEFINITIONS: &[DefKind] = &[
    DefKind::Attribute,
    DefKind::Enum,
    DefKind::Occurrence,
    DefKind::Individual,
    DefKind::Item,
    DefKind::Metadata,
    DefKind::Part,
    DefKind::Port,
    DefKind::Connection,
    DefKind::Interface,
    DefKind::Allocation,
    DefKind::Flow,
    DefKind::Action,
    DefKind::State,
    DefKind::Calc,
    DefKind::Constraint,
    DefKind::Requirement,
    DefKind::Concern,
    DefKind::Case,
    DefKind::Analysis,
    DefKind::Verification,
    DefKind::UseCase,
    DefKind::View,
    DefKind::Viewpoint,
    DefKind::Rendering,
    DefKind::Extended,
    DefKind::Type,
    DefKind::Classifier,
    DefKind::Class,
    DefKind::Struct,
    DefKind::DataType,
    DefKind::Assoc,
    DefKind::AssocStruct,
    DefKind::Behavior,
    DefKind::Interaction,
    DefKind::Function,
    DefKind::Predicate,
    DefKind::Metaclass,
];

/// The definitions that may be invoked in an expression
/// (`KineticEnergy(m, v)`, `sqrt(2.0)`): calculations and functions,
/// constraints and predicates, and the cases, which are calculations.
pub(crate) const CALLABLES: &[DefKind] = &[
    DefKind::Calc,
    DefKind::Function,
    DefKind::Constraint,
    DefKind::Predicate,
    DefKind::Case,
    DefKind::Analysis,
    DefKind::Verification,
    DefKind::UseCase,
];

/// The definitions a usage of `kind` may be typed by: the metamodel's
/// typing rule for the kind (an attribute usage's definitions are data
/// types, a part usage's part definitions, an item usage's structures,
/// an action or a state usage's behaviors, a calculation usage's
/// functions, …), split into the kinds that fit best and the other kinds
/// the rule admits. A part usage also takes the other structures, after
/// the part definitions, and a connection usage plain associations,
/// which the library types connections by. A reference usage, a KerML
/// feature, and a usage declared without a kind keyword take any type.
pub(crate) fn typed_by(kind: UsageKind) -> (&'static [DefKind], &'static [DefKind]) {
    use DefKind as D;
    use UsageKind as U;
    match kind {
        U::Attribute => (&[D::Attribute, D::Enum, D::DataType], &[]),
        U::Enum => (&[D::Enum], &[]),
        U::Occurrence | U::Event => (
            &[D::Occurrence, D::Individual],
            &[
                D::Item,
                D::Part,
                D::Port,
                D::Connection,
                D::Interface,
                D::Allocation,
                D::Flow,
                D::Action,
                D::State,
                D::Calc,
                D::Constraint,
                D::Requirement,
                D::Concern,
                D::Case,
                D::Analysis,
                D::Verification,
                D::UseCase,
                D::View,
                D::Viewpoint,
                D::Rendering,
                D::Metadata,
                D::Class,
                D::Struct,
                D::Behavior,
                D::Function,
                D::Predicate,
                D::Interaction,
                D::AssocStruct,
                D::Metaclass,
            ],
        ),
        U::Item => (
            &[D::Item, D::Part],
            &[
                D::Port,
                D::Connection,
                D::Interface,
                D::Allocation,
                D::View,
                D::Rendering,
                D::Metadata,
                D::Struct,
                D::AssocStruct,
                D::Metaclass,
            ],
        ),
        U::Part => (
            &[
                D::Part,
                D::Connection,
                D::Interface,
                D::Allocation,
                D::View,
                D::Rendering,
            ],
            &[
                D::Item,
                D::Port,
                D::Metadata,
                D::Struct,
                D::AssocStruct,
                D::Metaclass,
            ],
        ),
        U::Port => (&[D::Port], &[]),
        U::Connection => (
            &[D::Connection, D::Interface, D::Allocation],
            &[D::AssocStruct, D::Assoc],
        ),
        U::Interface => (&[D::Interface], &[]),
        U::Allocation => (&[D::Allocation], &[]),
        U::Flow | U::SuccessionFlow | U::Message => (&[D::Flow], &[D::Interaction]),
        U::Action | U::Perform | U::Step => (
            &[D::Action, D::Behavior],
            &[
                D::State,
                D::Calc,
                D::Case,
                D::Analysis,
                D::Verification,
                D::UseCase,
                D::Flow,
                D::Constraint,
                D::Requirement,
                D::Concern,
                D::Viewpoint,
                D::Function,
                D::Predicate,
                D::Interaction,
            ],
        ),
        U::State | U::Exhibit => (
            &[D::State],
            &[
                D::Action,
                D::Behavior,
                D::Calc,
                D::Case,
                D::Analysis,
                D::Verification,
                D::UseCase,
                D::Flow,
                D::Constraint,
                D::Requirement,
                D::Concern,
                D::Viewpoint,
                D::Function,
                D::Predicate,
                D::Interaction,
            ],
        ),
        U::Calc | U::Expr => (
            &[D::Calc, D::Function],
            &[
                D::Case,
                D::Analysis,
                D::Verification,
                D::UseCase,
                D::Constraint,
                D::Requirement,
                D::Concern,
                D::Viewpoint,
                D::Predicate,
            ],
        ),
        U::Constraint | U::AssertConstraint | U::BoolExpr | U::Invariant => (
            &[D::Constraint, D::Predicate],
            &[D::Requirement, D::Concern, D::Viewpoint],
        ),
        U::Requirement | U::Satisfy => (&[D::Requirement], &[D::Concern, D::Viewpoint]),
        U::Concern => (&[D::Concern], &[]),
        U::Case => (&[D::Case], &[D::Analysis, D::Verification, D::UseCase]),
        U::Analysis => (&[D::Analysis], &[]),
        U::Verification => (&[D::Verification], &[]),
        U::UseCase | U::Include => (&[D::UseCase], &[]),
        U::View => (&[D::View], &[]),
        U::Viewpoint => (&[D::Viewpoint], &[]),
        U::Rendering => (&[D::Rendering], &[]),
        U::Metadata => (&[D::Metadata, D::Metaclass], &[]),
        U::Connector => (
            &[
                D::Assoc,
                D::AssocStruct,
                D::Connection,
                D::Interface,
                D::Allocation,
            ],
            &[],
        ),
        _ => (ALL_DEFINITIONS, &[]),
    }
}

/// Every kind of usage the syntax tells apart.
const ALL_USAGES: &[UsageKind] = &[
    UsageKind::Attribute,
    UsageKind::Enum,
    UsageKind::Occurrence,
    UsageKind::Event,
    UsageKind::Item,
    UsageKind::Metadata,
    UsageKind::Part,
    UsageKind::Port,
    UsageKind::Connection,
    UsageKind::Interface,
    UsageKind::Allocation,
    UsageKind::Flow,
    UsageKind::Message,
    UsageKind::SuccessionFlow,
    UsageKind::Action,
    UsageKind::Perform,
    UsageKind::State,
    UsageKind::Exhibit,
    UsageKind::Transition,
    UsageKind::Calc,
    UsageKind::Case,
    UsageKind::Analysis,
    UsageKind::Verification,
    UsageKind::UseCase,
    UsageKind::Include,
    UsageKind::Constraint,
    UsageKind::AssertConstraint,
    UsageKind::Requirement,
    UsageKind::Satisfy,
    UsageKind::Concern,
    UsageKind::Viewpoint,
    UsageKind::View,
    UsageKind::Rendering,
    UsageKind::Accept,
    UsageKind::Send,
    UsageKind::Assign,
    UsageKind::Terminate,
    UsageKind::IfNode,
    UsageKind::WhileLoop,
    UsageKind::ForLoop,
    UsageKind::Merge,
    UsageKind::Decide,
    UsageKind::Join,
    UsageKind::Fork,
    UsageKind::Ref,
    UsageKind::Default,
    UsageKind::Extended,
    UsageKind::Succession,
    UsageKind::Binding,
    UsageKind::Feature,
    UsageKind::Step,
    UsageKind::Expr,
    UsageKind::BoolExpr,
    UsageKind::Invariant,
    UsageKind::Connector,
];

/// The kinds of usage a usage of `kind` directly specializes in the
/// metamodel (a part usage is an item usage, a state usage an action
/// usage, a requirement usage a constraint usage, …); a message is a
/// flow usage. A kind with none specializes a feature alone, which
/// names no kind.
fn usage_generals(kind: UsageKind) -> &'static [UsageKind] {
    use UsageKind as U;
    match kind {
        U::Enum => &[U::Attribute],
        U::Event | U::Item | U::Port => &[U::Occurrence],
        U::Part | U::Metadata => &[U::Item],
        U::Connection => &[U::Part, U::Connector],
        U::Interface | U::Allocation => &[U::Connection],
        U::View | U::Rendering => &[U::Part],
        U::Flow => &[U::Action, U::Connector],
        U::Message => &[U::Flow],
        U::SuccessionFlow => &[U::Flow, U::Succession],
        U::Action => &[U::Occurrence, U::Step],
        U::Perform => &[U::Action, U::Event],
        U::State
        | U::Transition
        | U::Accept
        | U::Send
        | U::Assign
        | U::Terminate
        | U::IfNode
        | U::WhileLoop
        | U::ForLoop
        | U::Merge
        | U::Decide
        | U::Join
        | U::Fork => &[U::Action],
        U::Exhibit => &[U::State, U::Perform],
        U::Calc => &[U::Action, U::Expr],
        U::Case => &[U::Calc],
        U::Analysis | U::Verification | U::UseCase => &[U::Case],
        U::Include => &[U::UseCase, U::Perform],
        U::Constraint => &[U::Occurrence, U::BoolExpr],
        U::AssertConstraint => &[U::Constraint, U::Invariant],
        U::Requirement => &[U::Constraint],
        U::Satisfy => &[U::Requirement, U::AssertConstraint],
        U::Concern | U::Viewpoint => &[U::Requirement],
        U::Succession | U::Binding => &[U::Connector],
        U::Expr => &[U::Step],
        U::BoolExpr => &[U::Expr],
        U::Invariant => &[U::BoolExpr],
        U::Attribute
        | U::Occurrence
        | U::Ref
        | U::Default
        | U::Extended
        | U::Feature
        | U::Step
        | U::Connector => &[],
    }
}

/// The kinds of usage that are usages of `kind`: `kind`'s own — a
/// message is a flow usage, and a flow usage may be declared as a
/// message — and those of the kinds specializing it in the metamodel:
/// an item usage may be a part usage, an action usage a state or a
/// calculation usage.
pub(crate) fn usages_of(kind: UsageKind) -> (Vec<UsageKind>, Vec<UsageKind>) {
    let kind = if kind == UsageKind::Message {
        UsageKind::Flow
    } else {
        kind
    };
    let own = |k: UsageKind| k == kind || (kind == UsageKind::Flow && k == UsageKind::Message);
    let under = |k: UsageKind| {
        let mut frontier = usage_generals(k).to_vec();
        while let Some(g) = frontier.pop() {
            if g == kind {
                return true;
            }
            frontier.extend_from_slice(usage_generals(g));
        }
        false
    };
    ALL_USAGES
        .iter()
        .copied()
        .filter(|&k| own(k) || under(k))
        .partition(|&k| own(k))
}

/// The metaclasses a definition of `kind` directly specializes in the
/// metamodel (a part definition is an item definition, a calculation
/// definition an action definition and a KerML function, …).
fn generals(kind: DefKind) -> &'static [DefKind] {
    use DefKind as D;
    match kind {
        D::Attribute => &[D::DataType],
        D::Enum => &[D::Attribute],
        D::Occurrence => &[D::Class],
        D::Individual => &[D::Occurrence],
        D::Item => &[D::Occurrence, D::Struct],
        D::Part => &[D::Item],
        D::Port => &[D::Occurrence, D::Struct],
        D::Connection => &[D::Part, D::AssocStruct],
        D::Interface | D::Allocation => &[D::Connection],
        D::Flow => &[D::Action, D::Interaction],
        D::Action => &[D::Occurrence, D::Behavior],
        D::State => &[D::Action],
        D::Calc => &[D::Action, D::Function],
        D::Constraint => &[D::Occurrence, D::Predicate],
        D::Requirement => &[D::Constraint],
        D::Concern | D::Viewpoint => &[D::Requirement],
        D::Case => &[D::Calc],
        D::Analysis | D::Verification | D::UseCase => &[D::Case],
        D::View | D::Rendering => &[D::Part],
        D::Metadata => &[D::Item, D::Metaclass],
        D::Classifier => &[D::Type],
        D::Class | D::DataType | D::Assoc => &[D::Classifier],
        D::Struct | D::Behavior => &[D::Class],
        D::AssocStruct => &[D::Assoc, D::Struct],
        D::Interaction => &[D::Behavior, D::Assoc],
        D::Function => &[D::Behavior],
        D::Predicate => &[D::Function],
        D::Metaclass => &[D::Struct],
        D::Extended | D::Type => &[],
    }
}

/// What a definition of `kind` may specialize: definitions of its own
/// kind first, then those of the kinds its kind specializes, nearest
/// first. A definition of a user-defined kind (`#Kind def`) or a KerML
/// `type` may specialize any type, and an individual definition the
/// occurrence definition it is an individual of, of whatever kind
/// (`individual def Vehicle_1 :> Vehicle`).
pub(crate) fn specializes(kind: DefKind) -> (Vec<DefKind>, Vec<DefKind>) {
    if matches!(kind, DefKind::Extended | DefKind::Type) {
        return (ALL_DEFINITIONS.to_vec(), Vec::new());
    }
    if kind == DefKind::Individual {
        let occurrences = ALL_DEFINITIONS
            .iter()
            .copied()
            .filter(|&k| k != kind && specializes(k).1.contains(&DefKind::Occurrence));
        let above = specializes(DefKind::Occurrence).1;
        return (
            vec![kind],
            [DefKind::Occurrence]
                .into_iter()
                .chain(occurrences)
                .chain(above)
                .collect(),
        );
    }
    let mut compatible: Vec<DefKind> = Vec::new();
    let mut frontier = vec![kind];
    while let Some(k) = frontier.pop() {
        for &g in generals(k) {
            if g != kind && !compatible.contains(&g) {
                compatible.push(g);
                frontier.insert(0, g);
            }
        }
    }
    (vec![kind], compatible)
}

#[cfg(test)]
mod tests {
    use super::{ALL_DEFINITIONS, Decl, declarations, specializes, typed_by, usages_of};
    use crate::position::{Encoding, Mapper};
    use sysmlv2_parser::ast::{DefKind, UsageKind};

    /// The declaration recorded for the element named `name` in `text`.
    fn declared_of(text: &str, name: &str, kerml: bool) -> Option<super::Declared> {
        let parse = if kerml {
            sysmlv2_parser::parser::parse_kerml_source(text)
        } else {
            sysmlv2_parser::parser::parse_source(text)
        };
        let mapper = Mapper::new(text, Encoding::Utf8);
        let decls = declarations(&parse.unit, &mapper);
        let at = (0..text.len())
            .find(|&i| {
                text[i..].starts_with(&format!(" {name}"))
                    && !text[i + 1 + name.len()..].starts_with(|c: char| c.is_alphanumeric())
            })
            .expect("declared name")
            + 1;
        decls
            .get(&mapper.position(crate::position::offset32(at)))
            .cloned()
    }

    /// The kind recorded for the declaration named `name` in `text`.
    fn decl_of(text: &str, name: &str, kerml: bool) -> Option<Decl> {
        declared_of(text, name, kerml).map(|d| d.decl)
    }

    #[test]
    fn declarations_record_their_kind() {
        let text = "package P {\n    part def V {\n        attribute m : Real;\n        \
                    port p : ~F;\n        x : T;\n    }\n    requirement def R {\n        \
                    subject s : V;\n    }\n}\n";
        for (name, decl) in [
            ("P", Decl::Namespace),
            ("V", Decl::Definition(DefKind::Part)),
            ("m", Decl::Usage(UsageKind::Attribute)),
            ("p", Decl::Usage(UsageKind::Port)),
            ("x", Decl::Usage(UsageKind::Default)),
            ("R", Decl::Definition(DefKind::Requirement)),
            ("s", Decl::Usage(UsageKind::Ref)),
        ] {
            assert_eq!(decl_of(text, name, false), Some(decl), "{name}");
        }
        let text = "package K {\n    datatype D;\n    feature f : D;\n    function F;\n}\n";
        assert_eq!(
            decl_of(text, "D", true),
            Some(Decl::Definition(DefKind::DataType))
        );
        assert_eq!(
            decl_of(text, "f", true),
            Some(Decl::Usage(UsageKind::Feature))
        );
        assert_eq!(
            decl_of(text, "F", true),
            Some(Decl::Definition(DefKind::Function))
        );
    }

    /// A declaration records the types it names: a usage's typings, a
    /// definition's specializations.
    #[test]
    fn declarations_record_the_types_they_name() {
        let text = "package U {\n    attribute def ForceUnit :> Units::DerivedUnit, Other;\n    \
                    attribute <N> newton : ForceUnit = kg*m/s^2;\n    part p :> q;\n}\n";
        for (name, types) in [
            ("ForceUnit", vec!["DerivedUnit", "Other"]),
            ("newton", vec!["ForceUnit"]),
            ("p", vec![]),
        ] {
            let declared = declared_of(text, name, false).expect(name);
            assert_eq!(declared.types, types, "{name}");
        }
    }

    /// The measurement-unit types: the root and every definition that
    /// specializes one, however deep; nothing else.
    #[test]
    fn unit_types_follow_specializations() {
        let definitions: Vec<(&str, Vec<String>)> = vec![
            ("ForceUnit", vec!["DerivedUnit".to_string()]),
            ("DerivedUnit", vec!["MeasurementUnit".to_string()]),
            ("MassUnit", vec!["SimpleUnit".to_string()]),
            ("SimpleUnit", vec!["MeasurementUnit".to_string()]),
            ("MassValue", vec!["ScalarQuantityValue".to_string()]),
            ("Unitless", vec![]),
        ];
        let pairs = || definitions.iter().map(|(n, s)| (*n, s.as_slice()));
        let units = super::unit_types(Some("MeasurementUnit"), &Default::default(), pairs());
        for name in [
            "MeasurementUnit",
            "SimpleUnit",
            "DerivedUnit",
            "MassUnit",
            "ForceUnit",
        ] {
            assert!(units.contains(name), "{name}");
        }
        assert!(!units.contains("MassValue") && !units.contains("Unitless"));
        // Extending known unit types with more definitions.
        let more = [("PerMass", vec!["MassUnit".to_string()])];
        let extended =
            super::unit_types(None, &units, more.iter().map(|(n, s)| (*n, s.as_slice())));
        assert!(extended.contains("PerMass") && extended.contains("ForceUnit"));
    }

    #[test]
    fn features_take_their_metaclass_kind() {
        use super::feature_decl;
        assert_eq!(
            feature_decl("AttributeUsage"),
            Decl::Usage(UsageKind::Attribute)
        );
        assert_eq!(feature_decl("ActionUsage"), Decl::Usage(UsageKind::Action));
        assert_eq!(feature_decl("Feature"), Decl::Usage(UsageKind::Feature));
        assert_eq!(feature_decl("Package"), Decl::Other);
    }

    #[test]
    fn typing_follows_the_metamodel() {
        let (exact, compatible) = typed_by(UsageKind::Attribute);
        for k in [DefKind::Attribute, DefKind::Enum, DefKind::DataType] {
            assert!(exact.contains(&k), "{k:?}");
        }
        assert!(!exact.contains(&DefKind::Part) && !compatible.contains(&DefKind::Part));
        let (exact, compatible) = typed_by(UsageKind::Part);
        assert!(exact.contains(&DefKind::Part) && exact.contains(&DefKind::Interface));
        assert_eq!(compatible[0], DefKind::Item);
        assert!(!exact.contains(&DefKind::Attribute));
        assert_eq!(typed_by(UsageKind::Port).0, &[DefKind::Port]);
        assert_eq!(typed_by(UsageKind::Ref).0, ALL_DEFINITIONS);
        assert_eq!(typed_by(UsageKind::Feature).0, ALL_DEFINITIONS);
    }

    /// The metamodel's typing properties: a state usage is typed by any
    /// behavior, an action usage too — constraints and requirements are
    /// predicates, and so functions and behaviors — a calculation by any
    /// function, a connection by an association (the library types
    /// connections by plain ones), and a part by part definitions
    /// alongside any other structure.
    #[test]
    fn typing_admits_what_the_metamodel_allows() {
        let admits = |u: UsageKind, d: DefKind| {
            let (exact, compatible) = typed_by(u);
            exact.contains(&d) || compatible.contains(&d)
        };
        for (u, d) in [
            (UsageKind::State, DefKind::Action),
            (UsageKind::State, DefKind::Constraint),
            (UsageKind::Exhibit, DefKind::Behavior),
            (UsageKind::Action, DefKind::Constraint),
            (UsageKind::Action, DefKind::Requirement),
            (UsageKind::Step, DefKind::Predicate),
            (UsageKind::Calc, DefKind::Predicate),
            (UsageKind::Calc, DefKind::Constraint),
            (UsageKind::Expr, DefKind::Requirement),
            (UsageKind::Connection, DefKind::Assoc),
            (UsageKind::Part, DefKind::Port),
            (UsageKind::Part, DefKind::Struct),
        ] {
            assert!(admits(u, d), "{u:?} typed by {d:?}");
        }
        for (u, d) in [
            (UsageKind::State, DefKind::Part),
            (UsageKind::Calc, DefKind::Action),
            (UsageKind::Part, DefKind::Attribute),
            (UsageKind::Connection, DefKind::Part),
        ] {
            assert!(!admits(u, d), "{u:?} typed by {d:?}");
        }
    }

    /// The usages of a kind are those of the kinds specializing it in the
    /// metamodel: an occurrence may be of any kind but an attribute, a
    /// reference, or a plain connector; an action a state, a calculation,
    /// a case, a flow; a constraint a requirement; a part a connection,
    /// never a plain item.
    #[test]
    fn usages_descend_the_metamodel() {
        use UsageKind as U;
        let all = |k: U| {
            let (own, under) = usages_of(k);
            [own, under].concat()
        };
        let occurrences = all(U::Occurrence);
        for k in [
            U::Item,
            U::Part,
            U::Port,
            U::Action,
            U::Constraint,
            U::Concern,
            U::Event,
        ] {
            assert!(occurrences.contains(&k), "{k:?}");
        }
        for k in [
            U::Attribute,
            U::Enum,
            U::Ref,
            U::Succession,
            U::Binding,
            U::Step,
        ] {
            assert!(!occurrences.contains(&k), "{k:?}");
        }
        let actions = all(U::Action);
        for k in [
            U::State,
            U::Exhibit,
            U::Calc,
            U::UseCase,
            U::Include,
            U::Flow,
            U::Accept,
        ] {
            assert!(actions.contains(&k), "{k:?}");
        }
        assert!(!actions.contains(&U::Constraint) && !actions.contains(&U::Part));
        let constraints = all(U::Constraint);
        for k in [
            U::Requirement,
            U::Satisfy,
            U::Concern,
            U::Viewpoint,
            U::AssertConstraint,
        ] {
            assert!(constraints.contains(&k), "{k:?}");
        }
        assert_eq!(usages_of(U::Attribute), (vec![U::Attribute], vec![U::Enum]));
        assert!(!usages_of(U::Part).1.contains(&U::Item));
        assert_eq!(usages_of(U::Message), usages_of(U::Flow));
        assert_eq!(
            usages_of(U::Flow),
            (vec![U::Flow, U::Message], vec![U::SuccessionFlow])
        );
        assert_eq!(usages_of(U::Port), (vec![U::Port], vec![]));
    }

    #[test]
    fn specialization_climbs_the_metamodel() {
        let (exact, compatible) = specializes(DefKind::Part);
        assert_eq!(exact, vec![DefKind::Part]);
        assert_eq!(
            compatible[0],
            DefKind::Item,
            "nearest first: {compatible:?}"
        );
        assert!(compatible.contains(&DefKind::Occurrence));
        assert!(!compatible.contains(&DefKind::Attribute));
        let (_, compatible) = specializes(DefKind::Attribute);
        assert_eq!(
            compatible,
            vec![DefKind::DataType, DefKind::Classifier, DefKind::Type]
        );
        let (exact, _) = specializes(DefKind::Extended);
        assert_eq!(exact, ALL_DEFINITIONS.to_vec());
        // An individual definition: any occurrence definition, nearest
        // first.
        let (exact, compatible) = specializes(DefKind::Individual);
        assert_eq!(exact, vec![DefKind::Individual]);
        assert_eq!(compatible[0], DefKind::Occurrence);
        for k in [
            DefKind::Part,
            DefKind::Item,
            DefKind::Action,
            DefKind::Class,
        ] {
            assert!(compatible.contains(&k), "{k:?}");
        }
        assert!(!compatible.contains(&DefKind::Attribute));
    }
}
