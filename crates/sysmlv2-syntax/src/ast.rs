//! Syntax-faithful AST for the SysML v2 textual notation.
//!
//! Nodes mirror what the source *says*, not the fully-elaborated abstract
//! syntax: cross-references are kept as qualified names (resolution is a
//! separate phase), and no implied relationships are materialized. This is
//! exactly the information content of the "compact" JSON interchange form.
//!
//! Every node carries a [`Span`] back into the source text.

use crate::span::Span;

/// The textual-notation dialect a source unit was parsed as. KerML and
/// SysML share one lexical structure and expression grammar but differ in
/// structural keywords and reserved words.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Default)]
pub enum Dialect {
    #[default]
    Sysml,
    Kerml,
}

/// A parsed source unit (one `.sysml` / `.kerml` file): the root namespace.
#[derive(Clone, Debug, PartialEq)]
pub struct SourceUnit {
    pub dialect: Dialect,
    pub members: Vec<Member>,
}

/// One member of a namespace or body, with its optional visibility prefix.
#[derive(Clone, Debug, PartialEq)]
pub struct Member {
    pub visibility: Option<Visibility>,
    /// A bare `then` immediately before this (occurrence) member — an
    /// implied succession from the previous member (`EmptySuccessionMember`).
    pub leading_then: bool,
    /// Optional source-end multiplicity carried by the leading succession
    /// shorthand (`then [1] action next;`).
    pub leading_then_multiplicity: Option<Box<Multiplicity>>,
    pub kind: MemberKind,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Visibility {
    Public,
    Private,
    Protected,
}

#[derive(Clone, Debug, PartialEq)]
pub enum MemberKind {
    Package(Package),
    Import(Import),
    Alias(Alias),
    Comment(Comment),
    Doc(Doc),
    TextualRep(TextualRep),
    Definition(Definition),
    Usage(Usage),
    /// `filter <expr> ;` (ElementFilterMembership)
    Filter(Expr),
    /// `dependency <id>? from? a, b to c, d ;`
    Dependency(Dependency),
    /// `first <target> ;` in an action body (initial node membership).
    InitialNode(QualifiedName),
    /// `subject <usage> ;` (SubjectMembership)
    Subject(Usage),
    /// `actor <usage> ;` (ActorMembership, PartUsage)
    Actor(Usage),
    /// `stakeholder <usage> ;` (StakeholderMembership, PartUsage)
    Stakeholder(Usage),
    /// `objective <usage-body>` (ObjectiveMembership, RequirementUsage)
    Objective(Usage),
    /// `require`/`assume` constraint (RequirementConstraintMembership)
    RequirementConstraint {
        kind: RequirementConstraintKind,
        usage: Usage,
    },
    /// `frame <concern>` (FramedConcernMembership)
    FramedConcern(Usage),
    /// `verify <requirement>` (RequirementVerificationMembership)
    RequirementVerification(Usage),
    /// `entry`/`do`/`exit` state sub-action (StateSubactionMembership).
    /// `action` is `None` for the empty form (`entry;`).
    StateSubaction {
        kind: StateSubactionKind,
        action: Option<Usage>,
    },
    /// `expose <import-shape>` in view bodies (Membership/NamespaceExpose)
    Expose(Import),
    /// `render <rendering>` (ViewRenderingMembership)
    Render(Usage),
    /// `return <usage> ;` (ReturnParameterMembership)
    Return(Usage),
    /// Trailing result expression of a calc/case/constraint body
    /// (ResultExpressionMembership).
    Result(Expr),
    /// KerML standalone relationship declaration
    /// (`specialization S subtype A specializes B;`, `disjoint A from B;`, …).
    Relationship(RelationshipDecl),
    /// KerML `multiplicity M subsets N;` / `multiplicity M [bounds];`
    MultiplicityDecl(MultiplicityDecl),
}

/// KerML standalone relationship declarations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RelationshipDeclKind {
    /// `subtype A specializes B` (Specialization)
    Specialization,
    /// `subclassifier A specializes B` (Subclassification)
    Subclassification,
    /// `typing f typed by T` (FeatureTyping)
    FeatureTyping,
    /// `subset f subsets g` (Subsetting)
    Subsetting,
    /// `redefinition f redefines g` (Redefinition)
    Redefinition,
    /// `conjugate A conjugates B` (Conjugation)
    Conjugation,
    /// `disjoint A from B` (Disjoining)
    Disjoining,
    /// `inverse f of g` (FeatureInverting)
    FeatureInverting,
    /// `featuring f by T` (TypeFeaturing)
    TypeFeaturing,
}

#[derive(Clone, Debug, PartialEq)]
pub struct RelationshipDecl {
    pub kind: RelationshipDeclKind,
    pub id: Identification,
    pub source: TargetRef,
    pub target: TargetRef,
}

#[derive(Clone, Debug, PartialEq)]
pub struct MultiplicityDecl {
    pub id: Identification,
    /// `subsets N` form.
    pub subsets: Option<TargetRef>,
    /// `[bounds]` form.
    pub range: Option<Multiplicity>,
    pub body: Option<Vec<Member>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RequirementConstraintKind {
    Assumption,
    Requirement,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StateSubactionKind {
    Entry,
    Do,
    Exit,
}

/// `dependency <id>? from? clients to suppliers`
#[derive(Clone, Debug, PartialEq)]
pub struct Dependency {
    pub metadata: Vec<QualifiedName>,
    pub id: Identification,
    pub clients: Vec<QualifiedName>,
    pub suppliers: Vec<QualifiedName>,
}

/// `<shortName>` and/or name from an element declaration.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct Identification {
    pub short_name: Option<Name>,
    pub name: Option<Name>,
}

impl Identification {
    pub fn is_empty(&self) -> bool {
        self.short_name.is_none() && self.name.is_none()
    }
}

/// A single name: an `ID` or an `'unrestricted name'` (already unescaped).
#[derive(Clone, Debug, PartialEq)]
pub struct Name {
    pub value: String,
    pub span: Span,
}

/// Render a name in KerML textual restricted-name form: bare if it is a
/// basic name (`[a-zA-Z_]\w*`), otherwise single-quoted with
/// `\b \t \n \f \r " ' \` escaped. Used by the printer and by the normative
/// library-ID computation.
pub fn escape_name(name: &str) -> String {
    let basic = !name.is_empty()
        && name
            .chars()
            .next()
            .map(|c| c.is_ascii_alphabetic() || c == '_')
            .unwrap_or(false)
        && name.chars().all(|c| c.is_ascii_alphanumeric() || c == '_');
    if basic {
        return name.to_string();
    }
    let mut out = String::with_capacity(name.len() + 2);
    out.push('\'');
    for c in name.chars() {
        match c {
            '\u{0008}' => out.push_str("\\b"),
            '\t' => out.push_str("\\t"),
            '\n' => out.push_str("\\n"),
            '\u{000C}' => out.push_str("\\f"),
            '\r' => out.push_str("\\r"),
            '"' => out.push_str("\\\""),
            '\'' => out.push_str("\\'"),
            '\\' => out.push_str("\\\\"),
            c => out.push(c),
        }
    }
    out.push('\'');
    out
}

/// `($::)? (Name ::)* Name`
#[derive(Clone, Debug, PartialEq)]
pub struct QualifiedName {
    /// Prefixed with `$::` (resolve from the global root namespace).
    pub is_global: bool,
    pub segments: Vec<Name>,
    pub span: Span,
}

impl QualifiedName {
    /// Dot/colons-free display form, e.g. `Vehicle::engine`.
    pub fn to_display_string(&self) -> String {
        let mut s = String::new();
        if self.is_global {
            s.push_str("$::");
        }
        for (i, seg) in self.segments.iter().enumerate() {
            if i > 0 {
                s.push_str("::");
            }
            s.push_str(&seg.value);
        }
        s
    }

    /// Textual-notation form with restricted names quoted (`A::'..'`) —
    /// the `{"@ref"}` encoding, parsed back by the JSON reader.
    pub fn to_ref_string(&self) -> String {
        let mut s = String::new();
        if self.is_global {
            s.push_str("$::");
        }
        for (i, seg) in self.segments.iter().enumerate() {
            if i > 0 {
                s.push_str("::");
            }
            s.push_str(&escape_name(&seg.value));
        }
        s
    }
}

/// A reference target: a plain qualified name or a feature chain `a.b.c`
/// (each chain link itself a qualified name).
#[derive(Clone, Debug, PartialEq)]
pub enum TargetRef {
    Name(QualifiedName),
    Chain(Vec<QualifiedName>),
}

impl TargetRef {
    pub fn span(&self) -> Span {
        match self {
            TargetRef::Name(qn) => qn.span,
            TargetRef::Chain(links) => links
                .first()
                .map(|f| f.span.join(links.last().unwrap().span))
                .unwrap_or_default(),
        }
    }
}

// ---------------------------------------------------------------------------
// Namespaces
// ---------------------------------------------------------------------------

/// `('standard'? 'library')? '#Meta'* 'package' Identification? Body`
/// (also KerML `namespace` declarations, flagged `is_namespace`).
#[derive(Clone, Debug, PartialEq)]
pub struct Package {
    pub is_library: bool,
    pub is_standard: bool,
    /// KerML `namespace N { … }` rather than a package.
    pub is_namespace: bool,
    /// `#Meta` prefix metadata (metaclass names).
    pub metadata: Vec<QualifiedName>,
    pub id: Identification,
    /// `None` when declared with `;` (no body).
    pub body: Option<Vec<Member>>,
}

/// `import all? <target> (::*)? (::**)? [filters] ;`
#[derive(Clone, Debug, PartialEq)]
pub struct Import {
    pub is_import_all: bool,
    pub target: QualifiedName,
    /// `::*` — import the namespace's members rather than one membership.
    pub is_namespace: bool,
    /// `::**` — recursive.
    pub is_recursive: bool,
    /// `[expr]` filter conditions (each bracket pair is one filter).
    pub filters: Vec<Expr>,
}

/// `alias <short> name for <target> ;`
#[derive(Clone, Debug, PartialEq)]
pub struct Alias {
    pub id: Identification,
    pub target: QualifiedName,
}

// ---------------------------------------------------------------------------
// Annotating elements
// ---------------------------------------------------------------------------

/// `comment <id>? (about e1, e2)? (locale "...")? /* body */`
#[derive(Clone, Debug, PartialEq)]
pub struct Comment {
    pub id: Identification,
    pub about: Vec<QualifiedName>,
    pub locale: Option<String>,
    /// Body text with the `/* */` delimiters stripped.
    pub body: String,
}

/// `doc <id>? (locale "...")? /* body */`
#[derive(Clone, Debug, PartialEq)]
pub struct Doc {
    pub id: Identification,
    pub locale: Option<String>,
    pub body: String,
}

/// `rep <id>? language "lang" /* body */`
#[derive(Clone, Debug, PartialEq)]
pub struct TextualRep {
    pub id: Identification,
    pub language: String,
    pub body: String,
}

// ---------------------------------------------------------------------------
// Definitions and usages
// ---------------------------------------------------------------------------

/// The kind keyword(s) of a SysML definition (`<kind> def`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DefKind {
    Attribute,
    Enum,
    Occurrence,
    /// `individual def` (no other kind keyword).
    Individual,
    Item,
    Metadata,
    Part,
    Port,
    Connection,
    Interface,
    Allocation,
    Flow,
    Action,
    State,
    Calc,
    Constraint,
    Requirement,
    Concern,
    Case,
    Analysis,
    Verification,
    UseCase,
    View,
    Viewpoint,
    Rendering,
    /// User-keyword extended definition (`#UserKw def`); the metaclass is in
    /// the prefix metadata.
    Extended,
    // ---- KerML type kinds ----
    Type,
    Classifier,
    Class,
    Struct,
    DataType,
    Assoc,
    AssocStruct,
    Behavior,
    Interaction,
    Function,
    Predicate,
    Metaclass,
}

/// The kind keyword of a SysML usage.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UsageKind {
    Attribute,
    Enum,
    Occurrence,
    Item,
    Metadata,
    Part,
    Port,
    Connection,
    Interface,
    Allocation,
    Flow,
    Action,
    State,
    Calc,
    Constraint,
    Requirement,
    Concern,
    Case,
    Analysis,
    Verification,
    UseCase,
    View,
    Viewpoint,
    Rendering,
    /// Explicit `ref` usage.
    Ref,
    /// Keyword-less usage (`x : T = v;`) — a reference usage.
    Default,
    /// User-keyword extended usage (`#UserKw x : T;`).
    Extended,
    /// `perform [action]` (PerformActionUsage)
    Perform,
    /// `exhibit [state]` (ExhibitStateUsage)
    Exhibit,
    /// `include [use case]` (IncludeUseCaseUsage)
    Include,
    /// `event [occurrence]` (EventOccurrenceUsage)
    Event,
    /// `[assert] [not] satisfy [requirement]` (SatisfyRequirementUsage)
    Satisfy,
    /// `assert [not] [constraint]` (AssertConstraintUsage)
    AssertConstraint,
    /// `succession` / `first a then b` (SuccessionAsUsage)
    Succession,
    /// `succession flow` (SuccessionFlowUsage)
    SuccessionFlow,
    /// `[binding] bind a = b` (BindingConnectorAsUsage)
    Binding,
    /// `message` (FlowUsage)
    Message,
    /// `transition` and target-transition shorthands (TransitionUsage)
    Transition,
    /// Control nodes.
    Merge,
    Decide,
    Join,
    Fork,
    /// Action nodes.
    Accept,
    Send,
    Assign,
    Terminate,
    IfNode,
    WhileLoop,
    ForLoop,
    // ---- KerML feature kinds ----
    Feature,
    Step,
    Expr,
    BoolExpr,
    /// `inv` (negated via [`UsageDetail::Assert`]).
    Invariant,
    Connector,
}

/// `abstract` / `variation` / `individual` / `#Meta` prefixes on a definition.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct DefPrefix {
    pub is_abstract: bool,
    pub is_variation: bool,
    pub is_individual: bool,
    /// `#Meta` prefix metadata (metaclass names).
    pub metadata: Vec<QualifiedName>,
}

/// `<prefix> <kind> def Identification? (:> supers)? Body`
#[derive(Clone, Debug, PartialEq)]
pub struct Definition {
    pub prefix: DefPrefix,
    pub kind: DefKind,
    pub id: Identification,
    /// `:>` / `specializes` targets.
    pub specializes: Vec<TargetRef>,
    /// `state def S parallel { … }`
    pub is_parallel: bool,
    /// KerML `all` sufficiency marker (`classifier all C …`).
    pub is_sufficient: bool,
    /// KerML type multiplicity (`class C [2] …`).
    pub multiplicity: Option<Multiplicity>,
    /// KerML `~` / `conjugates` target.
    pub conjugates: Vec<TargetRef>,
    /// KerML `disjoint from A, B`.
    pub disjoint_from: Vec<TargetRef>,
    /// KerML `unions A, B`.
    pub unions: Vec<TargetRef>,
    /// KerML `intersects A, B`.
    pub intersects: Vec<TargetRef>,
    /// KerML `differences A, B`.
    pub differences: Vec<TargetRef>,
    pub body: Option<Vec<Member>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FeatureDirection {
    In,
    Out,
    InOut,
}

/// Occurrence portion kind (`snapshot` / `timeslice` prefix).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PortionKind {
    Snapshot,
    Timeslice,
}

/// Prefix modifiers on a usage.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct UsagePrefix {
    pub direction: Option<FeatureDirection>,
    pub is_derived: bool,
    pub is_abstract: bool,
    pub is_variation: bool,
    pub is_constant: bool,
    pub is_ref: bool,
    pub is_end: bool,
    pub is_individual: bool,
    pub portion: Option<PortionKind>,
    /// Member is a variant of an enclosing variation (`variant` member prefix).
    pub is_variant: bool,
    /// `#Meta` prefix metadata (metaclass names).
    pub metadata: Vec<QualifiedName>,
    /// Cross feature after `end` (`end [0..1] item cart : C[1]`).
    pub end_cross: Option<Box<CrossFeature>>,
    // ---- KerML feature prefixes ----
    pub is_composite: bool,
    /// KerML `portion` prefix (distinct from SysML portion kinds).
    pub is_portion: bool,
    /// KerML `var` prefix.
    pub is_variable: bool,
    /// KerML `member` prefix (non-feature membership of a feature element).
    pub is_type_member: bool,
}

/// The cross feature owned by an `end` feature/usage prefix: a declaration
/// carrying its own basic prefix, distinct from the end feature's own
/// prefix (`end in x : T feature y;`, `end derived c : Cart[1] item x;`).
#[derive(Clone, Debug, PartialEq, Default)]
pub struct CrossFeature {
    pub direction: Option<FeatureDirection>,
    pub is_derived: bool,
    pub is_abstract: bool,
    /// SysML `variation`.
    pub is_variation: bool,
    /// `const` (KerML) / `constant` (SysML).
    pub is_constant: bool,
    /// SysML `ref`.
    pub is_ref: bool,
    /// KerML `composite`.
    pub is_composite: bool,
    /// KerML `portion`.
    pub is_portion: bool,
    /// KerML `var`.
    pub is_variable: bool,
    pub decl: FeatureDeclaration,
}

/// One end of a connector (`connect`, `bind`, `first…then`, interface parts):
/// `([mult])? (name ::>)? target`
#[derive(Clone, Debug, PartialEq)]
pub struct ConnectorEnd {
    pub multiplicity: Option<Multiplicity>,
    pub name: Option<Name>,
    pub target: TargetRef,
}

/// A flow/message end: a feature chain whose last step is the flow feature
/// (e.g. `tank.fuelOut`).
#[derive(Clone, Debug, PartialEq)]
pub struct FlowEnd {
    pub target: TargetRef,
}

/// Payload of a flow/message (`of` clause) or an accept action.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct PayloadPart {
    pub id: Identification,
    pub specializations: Vec<FeatureSpecialization>,
    pub multiplicity: Option<Multiplicity>,
    pub is_ordered: bool,
    pub is_nonunique: bool,
    pub value: Option<FeatureValue>,
}

/// Trigger of an accept action: `at`/`after`/`when` expression.
#[derive(Clone, Debug, PartialEq)]
pub struct Trigger {
    pub kind: TriggerKind,
    pub expr: Expr,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TriggerKind {
    At,
    After,
    When,
}

/// Kind-specific parts of a usage beyond the uniform declaration shape.
#[derive(Clone, Debug, PartialEq, Default)]
pub enum UsageDetail {
    #[default]
    None,
    /// `connect a to b` / `allocate a to b` / `connect (a, b, c)` /
    /// interface parts.
    Connector { ends: Vec<ConnectorEnd> },
    /// `bind a = b`
    Binding { ends: Vec<ConnectorEnd> },
    /// `first a then b` (also `then b` target shorthand with no source).
    Succession {
        source: Option<ConnectorEnd>,
        target: ConnectorEnd,
    },
    /// Flow/message: `of` payload, `from a to b` (or bare `a to b`).
    Flow {
        payload: Option<PayloadPart>,
        source: Option<FlowEnd>,
        target: Option<FlowEnd>,
    },
    /// Metadata usage: `@ M about x, y`.
    Metadata { about: Vec<QualifiedName> },
    /// `satisfy … by <target>`; also carries assert/negation flags.
    Satisfy {
        asserted: bool,
        negated: bool,
        by: Option<TargetRef>,
    },
    /// `assert [not]` constraint.
    Assert { negated: bool },
    /// `accept <payload> (via <expr>)?` (+ trigger inside payload).
    Accept {
        payload: PayloadPart,
        trigger: Option<Trigger>,
        via: Option<Expr>,
    },
    /// `send <expr>? (via <expr>)? (to <expr>)?`
    Send {
        payload: Option<Expr>,
        via: Option<Expr>,
        to: Option<Expr>,
    },
    /// `assign <target> := <expr>`
    Assign { target: Expr, value: Expr },
    /// `terminate <expr>?`
    Terminate { target: Option<Expr> },
    /// `if <cond> { … } (else …)?` — bodies are anonymous action usages.
    IfNode {
        cond: Expr,
        then_body: Box<Usage>,
        /// Either an action body or a nested if-node usage.
        else_body: Option<Box<Usage>>,
    },
    /// `while <cond> { … } (until <expr> ;)?` — `cond` is `None` for `loop`.
    WhileLoop {
        cond: Option<Expr>,
        body: Box<Usage>,
        until: Option<Expr>,
    },
    /// `for <var> in <seq> { … }`
    ForLoop {
        var: FeatureDeclaration,
        seq: Expr,
        body: Box<Usage>,
    },
    /// `transition (first)? <source>? trigger? guard? effect? then <target>`
    Transition {
        source: Option<TargetRef>,
        trigger: Option<Box<UsageDetail>>,
        guard: Option<Expr>,
        /// Effect action (`do …`): a performed-action usage.
        effect: Option<Box<Usage>>,
        target: Option<ConnectorEnd>,
        /// `else target ;` default transition.
        is_default: bool,
    },
}

/// One specialization clause in a feature declaration.
#[derive(Clone, Debug, PartialEq)]
pub enum FeatureSpecialization {
    /// `: T1, T2` or `defined by T1, T2`. `conjugated` per entry (`~Port`).
    TypedBy(Vec<TypeRef>),
    /// `:> f1, f2` / `subsets f1, f2`
    Subsets(Vec<TargetRef>),
    /// `:>> f1, f2` / `redefines f1, f2`
    Redefines(Vec<TargetRef>),
    /// `::> f` / `references f`
    References(TargetRef),
    /// `=> f` / `crosses f`
    Crosses(TargetRef),
}

#[derive(Clone, Debug, PartialEq)]
pub struct TypeRef {
    /// `~T` — conjugated (port) type.
    pub is_conjugated: bool,
    pub target: TargetRef,
}

/// `[expr]` or `[expr .. expr]`, with optional `ordered` / `nonunique`.
#[derive(Clone, Debug, PartialEq)]
pub struct Multiplicity {
    /// Lower bound when the `l..u` form is used.
    pub lower: Option<Expr>,
    pub upper: Expr,
    pub span: Span,
}

/// The declaration part of a usage: identification plus any specializations,
/// multiplicity, and ordering markers, in source order.
#[derive(Clone, Debug, PartialEq, Default)]
pub struct FeatureDeclaration {
    pub id: Identification,
    pub specializations: Vec<FeatureSpecialization>,
    pub multiplicity: Option<Multiplicity>,
    pub is_ordered: bool,
    pub is_nonunique: bool,
    /// KerML `all` sufficiency marker.
    pub is_sufficient: bool,
    /// KerML `~` / `conjugates` target.
    pub conjugates: Option<TargetRef>,
    /// KerML `chains a.b.c`.
    pub chains: Option<TargetRef>,
    /// KerML `inverse of f`.
    pub inverse_of: Option<TargetRef>,
    /// KerML `featured by T1, T2`.
    pub featured_by: Vec<TargetRef>,
    /// KerML type-relationship parts on features.
    pub disjoint_from: Vec<TargetRef>,
    pub unions: Vec<TargetRef>,
    pub intersects: Vec<TargetRef>,
    pub differences: Vec<TargetRef>,
}

impl FeatureDeclaration {
    /// True when nothing at all was declared.
    pub fn is_empty(&self) -> bool {
        self.id.is_empty()
            && self.specializations.is_empty()
            && self.multiplicity.is_none()
            && !self.is_ordered
            && !self.is_nonunique
            && !self.is_sufficient
            && self.conjugates.is_none()
            && self.chains.is_none()
            && self.inverse_of.is_none()
            && self.featured_by.is_empty()
            && self.disjoint_from.is_empty()
            && self.unions.is_empty()
            && self.intersects.is_empty()
            && self.differences.is_empty()
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ValueKind {
    /// `= expr`
    Bound,
    /// `:= expr`
    Initial,
    /// `default expr` / `default = expr`
    Default,
    /// `default := expr`
    DefaultInitial,
}

#[derive(Clone, Debug, PartialEq)]
pub struct FeatureValue {
    pub kind: ValueKind,
    pub expr: Expr,
}

/// `<prefix> <kind> <declaration>? <detail>? <value>? Body`
///
/// Reference forms of behavioral usages (`perform a.b`, `exhibit s`, …) store
/// their target as a leading [`FeatureSpecialization::References`] in the
/// declaration, mirroring the grammar's `OwnedReferenceSubsetting`.
#[derive(Clone, Debug, PartialEq)]
pub struct Usage {
    pub prefix: UsagePrefix,
    pub kind: UsageKind,
    pub declaration: FeatureDeclaration,
    pub detail: UsageDetail,
    pub value: Option<FeatureValue>,
    /// `state … parallel { … }`
    pub is_parallel: bool,
    pub body: Option<Vec<Member>>,
}

// ---------------------------------------------------------------------------
// Expressions (KerML Expressions grammar)
// ---------------------------------------------------------------------------

/// Binary / n-ary operators, named as in the abstract syntax `operator`
/// strings.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BinaryOp {
    NullCoalescing, // ??
    Implies,        // implies
    OrBar,          // |
    CondOr,         // or (short-circuit)
    Xor,            // xor
    AndAmp,         // &
    CondAnd,        // and (short-circuit)
    Eq,             // ==
    NotEq,          // !=
    Same,           // ===
    NotSame,        // !==
    Lt,             // <
    Gt,             // >
    LtEq,           // <=
    GtEq,           // >=
    Range,          // ..
    Add,            // +
    Sub,            // -
    Mul,            // *
    Div,            // /
    Rem,            // %
    Pow,            // ** (right-assoc)
    Caret,          // ^  (right-assoc)
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnaryOp {
    Plus,
    Minus,
    Tilde,
    Not,
}

/// `istype` / `hastype` / `@` / `as` / `meta` / `@@` operators.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ClassificationOp {
    IsType,
    HasType,
    AtType,     // @
    MetaAtType, // @@
    As,
    Meta,
}

#[derive(Clone, Debug, PartialEq)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug, PartialEq)]
pub enum ExprKind {
    Literal(Literal),
    /// `null` or `()`
    Null,
    /// Reference to a feature by (qualified) name.
    Ref(QualifiedName),
    /// `if cond ? a else b`
    Conditional {
        cond: Box<Expr>,
        then_branch: Box<Expr>,
        else_branch: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    Unary {
        op: UnaryOp,
        operand: Box<Expr>,
    },
    /// `x istype T`, `istype T` (implicit self), `x meta M`, ...
    Classification {
        op: ClassificationOp,
        /// `None` = implicit self operand.
        operand: Option<Box<Expr>>,
        ty: TargetRef,
    },
    /// `all T` — extent of a type.
    Extent {
        ty: TargetRef,
    },
    /// `target.member` — feature-chain step.
    ChainStep {
        target: Box<Expr>,
        member: TargetRef,
    },
    /// `target#(index)`
    Index {
        target: Box<Expr>,
        index: Box<Expr>,
    },
    /// `target[arg]` — e.g. quantity units: `10 [m]`.
    Bracket {
        target: Box<Expr>,
        arg: Box<Expr>,
    },
    /// `target->Fn(args)` / `target->Fn {body}` / `target->Fn ref`.
    Arrow {
        target: Box<Expr>,
        ty: TargetRef,
        args: ArrowArgs,
    },
    /// `target.{ body }` — collect.
    Collect {
        target: Box<Expr>,
        body: Box<Expr>,
    },
    /// `target.?{ body }` — select.
    Select {
        target: Box<Expr>,
        body: Box<Expr>,
    },
    /// `Type(args)` — invocation.
    Invocation {
        ty: TargetRef,
        args: Vec<Arg>,
    },
    /// `new Type(args)` — constructor.
    Constructor {
        ty: TargetRef,
        args: Vec<Arg>,
    },
    /// `{ in p1 : T1; … ; result-expr }` — expression body (lambda). SysML
    /// expression bodies are full calculation bodies: parameters are
    /// `in`-direction usage members and the trailing expression is a
    /// [`MemberKind::Result`] member.
    Body {
        members: Vec<Member>,
    },
    /// The non-braced SysML `ExpressionBody` alternative, inherited from a
    /// semicolon-bodied `CalculationBody`.
    BodyTerminator,
    /// `(a, b, c)` — sequence.
    Sequence(Vec<Expr>),
    /// `x.metadata` — metadata access.
    MetadataAccess {
        target: QualifiedName,
    },
}

#[derive(Clone, Debug, PartialEq)]
pub enum ArrowArgs {
    /// `->Fn { body }`
    Body(Box<Expr>),
    /// `->Fn functionRef`
    FunctionRef(QualifiedName),
    /// `->Fn (args...)`
    List(Vec<Arg>),
}

/// A positional or named (`param = value`) argument.
#[derive(Clone, Debug, PartialEq)]
pub struct Arg {
    /// Redefined parameter name for named arguments.
    pub name: Option<QualifiedName>,
    pub value: Expr,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Literal {
    Bool(bool),
    /// Raw text preserved; decoded value.
    String(String),
    /// `DECIMAL_VALUE` — kept as raw digits (arbitrary precision).
    Integer(String),
    /// Real literal composed of `DECIMAL? '.' (DECIMAL|EXP) | EXP`; raw text.
    Real(String),
    /// `*` — positive infinity (unbounded multiplicity).
    Infinity,
}
