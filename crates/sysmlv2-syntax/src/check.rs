//! Post-parse validation: body-context legality.
//!
//! The parser deliberately accepts a superset grammar — every member form is
//! recognized in every body so that error recovery and formatting stay
//! robust. This pass closes that gap: it walks a parsed [`SourceUnit`] and
//! reports members that the normative Xtext grammars do not allow in their
//! surrounding body context (a `transition` inside a plain `part` body, an
//! `entry` action outside a state, a `filter` in a definition body, …), plus
//! the variant-membership ownership rule (`variant` members are only allowed
//! inside `variation` definitions/usages).
//!
//! The legality matrix below is transcribed from the `*Body` / `*BodyItem`
//! rules of `spec-refs/SysML.xtext` and `spec-refs/KerML.xtext`. Where the
//! abstract syntax cannot distinguish two textual spellings that the AST also
//! merges (e.g. `transition first a if g then b;` versus the guarded
//! succession `first a if g then b;` — both a `TransitionUsage` with a source
//! and a guard), the check accepts the union of their contexts.

use crate::ast::*;
use crate::diag::Diagnostic;
use std::collections::HashMap;

/// Normative XMI validation rules currently mapped directly to diagnostics
/// by this syntax/structural validation layer. The XMI audit verifies every
/// name against the pinned 2025-02 KerML/SysML metamodel and ratchets the
/// total rule inventory, so coverage cannot drift silently.
pub const IMPLEMENTED_NORMATIVE_VALIDATION_RULES: &[&str] = &[
    "validateCaseDefinitionOnlyOneObjective",
    "validateCaseDefinitionOnlyOneSubject",
    "validateCaseDefinitionSubjectParameterPosition",
    "validateCaseUsageOnlyOneObjective",
    "validateCaseUsageOnlyOneSubject",
    "validateCaseUsageSubjectParameterPosition",
    "validateFlowDefinitionFlowEnds",
    "validateImportTopLevelVisibility",
    "validateObjectiveMembershipOwningType",
    "validateRequirementDefinitionOnlyOneSubject",
    "validateRequirementDefinitionSubjectParameterPosition",
    "validateRequirementUsageOnlyOneSubject",
    "validateRequirementUsageSubjectParameterPosition",
    "validateSubjectMembershipOwningType",
];

/// Validate one parsed source unit; returns all body-context diagnostics.
pub fn validate(unit: &SourceUnit) -> Vec<Diagnostic> {
    let mut v = Validator {
        dialect: unit.dialect,
        diags: Vec::new(),
    };
    // KerML validateImportTopLevelVisibility: a root Namespace is not
    // itself owned through a Membership, so its Imports must be private.
    for member in &unit.members {
        if matches!(member.kind, MemberKind::Import(_))
            && member.visibility != Some(Visibility::Private)
        {
            v.error(
                member,
                "validateImportTopLevelVisibility: a top-level import must be private".into(),
            );
        }
    }
    let root = match unit.dialect {
        Dialect::Sysml => Ctx::Package,
        Dialect::Kerml => Ctx::KRoot,
    };
    v.walk_members(&unit.members, root, false);
    v.diags
}

/// A body context, named for the grammar rule that defines its member set.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Ctx {
    /// SysML `PackageBody` (also the SysML root namespace).
    Package,
    /// SysML `DefinitionBody` / `UsageBody`.
    Definition,
    /// SysML `EnumerationBody`: annotations and enumerated values only.
    Enumeration,
    /// SysML `InterfaceBody`.
    Interface,
    /// SysML `ActionBody`.
    Action,
    /// SysML `StateBodyPart`.
    State,
    /// SysML `CalculationBody` (calc/constraint bodies, expression bodies).
    Calculation,
    /// SysML `RequirementBody` (requirement/concern/viewpoint bodies).
    Requirement,
    /// SysML `CaseBody` (case/analysis/verification/use-case bodies).
    Case,
    /// SysML `ViewDefinitionBody`.
    ViewDef,
    /// SysML `ViewBody` (view usages; adds `expose`).
    View,
    /// `MetadataBody` (both dialects): definitions plus redefining features.
    Metadata,
    /// KerML root namespace / `namespace` declarations (`NamespaceBody`).
    KRoot,
    /// KerML `PackageBody` (adds `filter`).
    KPackage,
    /// KerML `TypeBody`.
    KType,
    /// KerML `FunctionBody` (adds `return` and a result expression).
    KFunction,
}

impl Ctx {
    fn describe(self) -> &'static str {
        match self {
            Ctx::Package => "a package body",
            Ctx::Definition => "a definition or usage body",
            Ctx::Enumeration => "an enumeration definition body",
            Ctx::Interface => "an interface body",
            Ctx::Action => "an action body",
            Ctx::State => "a state body",
            Ctx::Calculation => "a calculation body",
            Ctx::Requirement => "a requirement body",
            Ctx::Case => "a case body",
            Ctx::ViewDef => "a view definition body",
            Ctx::View => "a view usage body",
            Ctx::Metadata => "a metadata body",
            Ctx::KRoot => "a namespace body",
            Ctx::KPackage => "a package body",
            Ctx::KType => "a type body",
            Ctx::KFunction => "a function body",
        }
    }

    fn is_kerml(self) -> bool {
        matches!(
            self,
            Ctx::KRoot | Ctx::KPackage | Ctx::KType | Ctx::KFunction
        )
    }
}

/// Grammar category of a SysML usage member (`NonOccurrenceUsageElement`,
/// `StructureUsageElement`, `BehaviorUsageElement`, `ActionNode`, …).
#[derive(Clone, Copy, PartialEq, Eq)]
enum Cat {
    /// Annotating element (metadata usage): legal wherever annotations are.
    Annotation,
    NonOccurrence,
    Structure,
    Behavior,
    ActionNode,
    /// Bare `then t;` (`TargetSuccession` shorthand).
    TargetSuccession,
    Transition,
    /// KerML feature kinds (uniform member model — no SysML category).
    KFeature,
}

fn usage_cat(u: &Usage) -> Cat {
    use UsageKind::*;
    match u.kind {
        Metadata => Cat::Annotation,
        Ref | Default | Attribute | Enum | Extended | Binding => Cat::NonOccurrence,
        Succession => match &u.detail {
            UsageDetail::Succession { source: None, .. } => Cat::TargetSuccession,
            _ => Cat::NonOccurrence,
        },
        Transition => Cat::Transition,
        Occurrence | Item | Part | View | Rendering | Port | Connection | Interface
        | Allocation | Flow | Message | SuccessionFlow | Event => Cat::Structure,
        Action | Calc | State | Constraint | Requirement | Concern | Case | Analysis
        | Verification | UseCase | Viewpoint | Perform | Exhibit | Include | AssertConstraint
        | Satisfy => Cat::Behavior,
        Accept | Send | Assign | Terminate | IfNode | WhileLoop | ForLoop | Merge | Decide
        | Join | Fork => Cat::ActionNode,
        Feature | Step | Expr | BoolExpr | Invariant | Connector => Cat::KFeature,
    }
}

fn def_kind_keyword(k: DefKind) -> &'static str {
    use DefKind::*;
    match k {
        Attribute => "attribute",
        Enum => "enum",
        Occurrence => "occurrence",
        Individual => "individual",
        Item => "item",
        Metadata => "metadata",
        Part => "part",
        Port => "port",
        Connection => "connection",
        Interface => "interface",
        Allocation => "allocation",
        Flow => "flow",
        Action => "action",
        State => "state",
        Calc => "calc",
        Constraint => "constraint",
        Requirement => "requirement",
        Concern => "concern",
        Case => "case",
        Analysis => "analysis",
        Verification => "verification",
        UseCase => "use case",
        View => "view",
        Viewpoint => "viewpoint",
        Rendering => "rendering",
        Extended => "extended",
        Type => "type",
        Classifier => "classifier",
        Class => "class",
        Struct => "struct",
        DataType => "datatype",
        Assoc => "assoc",
        AssocStruct => "assoc struct",
        Behavior => "behavior",
        Interaction => "interaction",
        Function => "function",
        Predicate => "predicate",
        Metaclass => "metaclass",
    }
}

fn usage_kind_desc(k: UsageKind) -> &'static str {
    use UsageKind::*;
    match k {
        Attribute => "an attribute usage",
        Enum => "an enumeration usage",
        Occurrence => "an occurrence usage",
        Item => "an item usage",
        Metadata => "a metadata usage",
        Part => "a part usage",
        Port => "a port usage",
        Connection => "a connection usage",
        Interface => "an interface usage",
        Allocation => "an allocation usage",
        Flow => "a flow usage",
        Action => "an action usage",
        State => "a state usage",
        Calc => "a calculation usage",
        Constraint => "a constraint usage",
        Requirement => "a requirement usage",
        Concern => "a concern usage",
        Case => "a case usage",
        Analysis => "an analysis case usage",
        Verification => "a verification case usage",
        UseCase => "a use case usage",
        View => "a view usage",
        Viewpoint => "a viewpoint usage",
        Rendering => "a rendering usage",
        Ref => "a reference usage",
        Default => "a keyword-less usage",
        Extended => "an extended usage",
        Perform => "a perform action usage",
        Exhibit => "an exhibit state usage",
        Include => "an include use case usage",
        Event => "an event occurrence usage",
        Satisfy => "a satisfy requirement usage",
        AssertConstraint => "an assert constraint usage",
        Succession => "a succession usage",
        SuccessionFlow => "a succession flow usage",
        Binding => "a binding connector usage",
        Message => "a message usage",
        Transition => "a transition usage",
        Merge => "a merge node",
        Decide => "a decision node",
        Join => "a join node",
        Fork => "a fork node",
        Accept => "an accept action node",
        Send => "a send action node",
        Assign => "an assignment action node",
        Terminate => "a terminate action node",
        IfNode => "an if node",
        WhileLoop => "a while-loop node",
        ForLoop => "a for-loop node",
        Feature => "a feature",
        Step => "a step",
        Expr => "an expression feature",
        BoolExpr => "a boolean expression feature",
        Invariant => "an invariant",
        Connector => "a connector",
    }
}

fn member_desc(k: &MemberKind) -> String {
    match k {
        MemberKind::Package(p) if p.is_namespace => "a namespace".into(),
        MemberKind::Package(_) => "a package".into(),
        MemberKind::Import(_) => "an import".into(),
        MemberKind::Alias(_) => "an alias".into(),
        MemberKind::Comment(_) => "a comment".into(),
        MemberKind::Doc(_) => "a documentation comment".into(),
        MemberKind::TextualRep(_) => "a textual representation".into(),
        MemberKind::Definition(d) => format!("a `{}` definition", def_kind_keyword(d.kind)),
        MemberKind::Usage(u) => match usage_cat(u) {
            Cat::TargetSuccession => "a target succession (`then`)".into(),
            _ => usage_kind_desc(u.kind).into(),
        },
        MemberKind::Filter(_) => "a `filter` member".into(),
        MemberKind::Dependency(_) => "a dependency".into(),
        MemberKind::InitialNode(_) => "an initial-node member (`first`)".into(),
        MemberKind::Subject(_) => "a `subject` member".into(),
        MemberKind::Actor(_) => "an `actor` member".into(),
        MemberKind::Stakeholder(_) => "a `stakeholder` member".into(),
        MemberKind::Objective(_) => "an `objective` member".into(),
        MemberKind::RequirementConstraint { kind, .. } => match kind {
            RequirementConstraintKind::Assumption => "an `assume` constraint member".into(),
            RequirementConstraintKind::Requirement => "a `require` constraint member".into(),
        },
        MemberKind::FramedConcern(_) => "a `frame` member".into(),
        MemberKind::RequirementVerification(_) => "a `verify` member".into(),
        MemberKind::StateSubaction { kind, .. } => match kind {
            StateSubactionKind::Entry => "an `entry` action member".into(),
            StateSubactionKind::Do => "a `do` action member".into(),
            StateSubactionKind::Exit => "an `exit` action member".into(),
        },
        MemberKind::Expose(_) => "an `expose` member".into(),
        MemberKind::Render(_) => "a `render` member".into(),
        MemberKind::Return(_) => "a `return` parameter member".into(),
        MemberKind::Result(_) => "a result expression member".into(),
        MemberKind::Relationship(_) => "a relationship declaration".into(),
        MemberKind::MultiplicityDecl(_) => "a multiplicity declaration".into(),
    }
}

/// The identification a member contributes to its owning namespace, if any.
fn member_identification(k: &MemberKind) -> Option<&Identification> {
    match k {
        MemberKind::Package(p) => Some(&p.id),
        MemberKind::Alias(a) => Some(&a.id),
        MemberKind::Comment(c) => Some(&c.id),
        MemberKind::Doc(d) => Some(&d.id),
        MemberKind::TextualRep(r) => Some(&r.id),
        MemberKind::Definition(d) => Some(&d.id),
        MemberKind::Dependency(d) => Some(&d.id),
        MemberKind::Relationship(r) => Some(&r.id),
        MemberKind::MultiplicityDecl(m) => Some(&m.id),
        MemberKind::Usage(u)
        | MemberKind::Subject(u)
        | MemberKind::Actor(u)
        | MemberKind::Stakeholder(u)
        | MemberKind::Objective(u)
        | MemberKind::FramedConcern(u)
        | MemberKind::RequirementVerification(u)
        | MemberKind::Render(u)
        | MemberKind::Return(u) => Some(&u.declaration.id),
        MemberKind::RequirementConstraint { usage, .. } => Some(&usage.declaration.id),
        MemberKind::StateSubaction { action, .. } => action.as_ref().map(|u| &u.declaration.id),
        MemberKind::Import(_)
        | MemberKind::Filter(_)
        | MemberKind::InitialNode(_)
        | MemberKind::Expose(_)
        | MemberKind::Result(_) => None,
    }
}

/// Static element-metaclass identity used by the syntax-stage portion of
/// KerML `Membership::isDistinguishableFrom`. Concrete sibling metaclasses
/// are distinguishable even when they have the same name; identical
/// metaclasses are not. Alias targets need resolution, so aliases remain
/// conservative here and the model-stage namespace check refines them.
#[derive(Clone, Copy, PartialEq, Eq)]
enum NamedMetaclass {
    UnknownAliasTarget,
    Package,
    Definition(DefKind),
    Usage(UsageKind),
    Comment,
    Documentation,
    TextualRepresentation,
    Dependency,
    Relationship,
    Multiplicity,
}

fn member_metaclass(k: &MemberKind) -> Option<NamedMetaclass> {
    Some(match k {
        MemberKind::Package(_) => NamedMetaclass::Package,
        MemberKind::Alias(_) => NamedMetaclass::UnknownAliasTarget,
        MemberKind::Comment(_) => NamedMetaclass::Comment,
        MemberKind::Doc(_) => NamedMetaclass::Documentation,
        MemberKind::TextualRep(_) => NamedMetaclass::TextualRepresentation,
        MemberKind::Definition(d) => NamedMetaclass::Definition(d.kind),
        MemberKind::Dependency(_) => NamedMetaclass::Dependency,
        MemberKind::Relationship(_) => NamedMetaclass::Relationship,
        MemberKind::MultiplicityDecl(_) => NamedMetaclass::Multiplicity,
        MemberKind::Usage(u) => NamedMetaclass::Usage(u.kind),
        MemberKind::Subject(_) | MemberKind::Actor(_) | MemberKind::Stakeholder(_) => {
            NamedMetaclass::Usage(UsageKind::Part)
        }
        MemberKind::Objective(_) => NamedMetaclass::Usage(UsageKind::Requirement),
        MemberKind::RequirementConstraint { usage, .. }
        | MemberKind::FramedConcern(usage)
        | MemberKind::RequirementVerification(usage)
        | MemberKind::Render(usage)
        | MemberKind::Return(usage) => NamedMetaclass::Usage(usage.kind),
        MemberKind::StateSubaction { action, .. } => {
            NamedMetaclass::Usage(action.as_ref().map_or(UsageKind::Action, |u| u.kind))
        }
        MemberKind::Import(_)
        | MemberKind::Filter(_)
        | MemberKind::InitialNode(_)
        | MemberKind::Expose(_)
        | MemberKind::Result(_) => return None,
    })
}

fn metaclasses_are_distinguishable(a: NamedMetaclass, b: NamedMetaclass) -> bool {
    fn def_conforms(specific: DefKind, general: DefKind) -> bool {
        use DefKind::*;
        specific == general
            || general == Extended
            || matches!(
                (specific, general),
                (Part, Item | Occurrence)
                    | (Item | Port, Occurrence)
                    | (Analysis | Verification | UseCase, Case)
                    | (Concern | Viewpoint, Requirement)
                    | (Struct, Class | Classifier | Type)
                    | (
                        Class | DataType | Assoc | Behavior | Metaclass,
                        Classifier | Type
                    )
                    | (AssocStruct, Struct | Class | Assoc | Classifier | Type)
                    | (Interaction, Behavior | Class | Classifier | Type)
                    | (Function, Behavior | Class | Classifier | Type)
                    | (Predicate, Function | Behavior | Class | Classifier | Type)
                    | (Classifier, Type)
            )
    }
    fn usage_conforms(specific: UsageKind, general: UsageKind) -> bool {
        use UsageKind::*;
        specific == general
            || matches!((specific, general), (Ref, Default) | (Default, Ref))
            || general == Extended
            || matches!(
                (specific, general),
                (Part, Item | Occurrence)
                    | (Item | Port | Event, Occurrence)
                    | (Analysis | Verification | UseCase | Include, Case)
                    | (Concern | Viewpoint | Satisfy, Requirement)
                    | (Perform, Action)
                    | (Exhibit, State)
                    | (AssertConstraint, Constraint)
                    | (Message | SuccessionFlow, Flow)
                    | (
                        Accept
                            | Send
                            | Assign
                            | Terminate
                            | IfNode
                            | WhileLoop
                            | ForLoop
                            | Merge
                            | Decide
                            | Join
                            | Fork,
                        Action
                    )
                    | (Step | Expr | BoolExpr | Invariant | Connector, Feature)
                    | (BoolExpr | Invariant, Expr)
            )
    }
    if matches!(
        (a, b),
        (NamedMetaclass::UnknownAliasTarget, _) | (_, NamedMetaclass::UnknownAliasTarget)
    ) {
        return false;
    }
    let conforms = match (a, b) {
        (NamedMetaclass::Definition(x), NamedMetaclass::Definition(y)) => {
            def_conforms(x, y) || def_conforms(y, x)
        }
        (NamedMetaclass::Usage(x), NamedMetaclass::Usage(y)) => {
            usage_conforms(x, y) || usage_conforms(y, x)
        }
        _ => a == b,
    };
    !conforms
}

struct Validator {
    dialect: Dialect,
    diags: Vec<Diagnostic>,
}

impl Validator {
    /// Body context of a definition's body, per its kind.
    fn ctx_for_def(&self, k: DefKind) -> Ctx {
        use DefKind::*;
        if self.dialect == Dialect::Kerml {
            return match k {
                Function | Predicate => Ctx::KFunction,
                _ => Ctx::KType,
            };
        }
        match k {
            Enum => Ctx::Enumeration,
            Interface => Ctx::Interface,
            Action => Ctx::Action,
            State => Ctx::State,
            Calc | Constraint => Ctx::Calculation,
            Requirement | Concern | Viewpoint => Ctx::Requirement,
            Case | Analysis | Verification | UseCase => Ctx::Case,
            View => Ctx::ViewDef,
            // KerML kinds are unreachable in a SysML parse.
            _ => Ctx::Definition,
        }
    }

    /// Body context of a usage's body, per its kind.
    fn ctx_for_usage(&self, k: UsageKind) -> Ctx {
        use UsageKind::*;
        if self.dialect == Dialect::Kerml {
            return match k {
                Expr | BoolExpr | Invariant => Ctx::KFunction,
                Metadata => Ctx::Metadata,
                _ => Ctx::KType,
            };
        }
        match k {
            Interface => Ctx::Interface,
            Action | Perform | Accept | Send | Assign | Terminate | IfNode | WhileLoop
            | ForLoop | Merge | Decide | Join | Fork | Transition => Ctx::Action,
            State | Exhibit => Ctx::State,
            Calc | Constraint | AssertConstraint => Ctx::Calculation,
            Requirement | Concern | Viewpoint | Satisfy => Ctx::Requirement,
            Case | Analysis | Verification | UseCase | Include => Ctx::Case,
            View => Ctx::View,
            Metadata => Ctx::Metadata,
            Expr | BoolExpr | Invariant => Ctx::KFunction,
            Feature | Step | Connector => Ctx::KType,
            _ => Ctx::Definition,
        }
    }

    /// Context for members of a `{ … }` expression body.
    fn expr_body_ctx(&self) -> Ctx {
        match self.dialect {
            Dialect::Sysml => Ctx::Calculation,
            Dialect::Kerml => Ctx::KFunction,
        }
    }

    fn error(&mut self, m: &Member, message: String) {
        self.diags.push(Diagnostic::error(m.span, message));
    }

    fn walk_members(&mut self, members: &[Member], ctx: Ctx, owner_is_variation: bool) {
        self.check_duplicate_names(members);
        let mut target_succession_run = false;
        for m in members {
            let is_target_succession = matches!(
                &m.kind,
                MemberKind::Usage(u) if usage_cat(u) == Cat::TargetSuccession
            );
            if is_target_succession {
                // SysML.xtext does not admit TargetSuccessionMember as an
                // independent ActionBodyItem. It is a suffix of an initial
                // node, behavior usage, or action node, and further target
                // successions may immediately follow in the same suffix
                // run. Any intervening body member ends that run.
                if matches!(ctx, Ctx::Action | Ctx::Calculation | Ctx::Case | Ctx::State)
                    && !target_succession_run
                {
                    self.error(
                        m,
                        "a target succession (`then`) must immediately follow \
                         an initial node, behavior usage, action node, or \
                         another target succession"
                            .into(),
                    );
                }
            }
            self.check_member(ctx, owner_is_variation, m);
            self.walk_member_children(ctx, m);
            target_succession_run = if is_target_succession
                || matches!(
                    m.kind,
                    MemberKind::Comment(_) | MemberKind::Doc(_) | MemberKind::TextualRep(_)
                ) {
                target_succession_run
            } else {
                matches!(
                    m.kind,
                    MemberKind::InitialNode(_) | MemberKind::StateSubaction { .. }
                ) || matches!(
                    &m.kind,
                    MemberKind::Usage(u)
                        if matches!(
                            usage_cat(u),
                            Cat::Structure | Cat::Behavior | Cat::ActionNode | Cat::Transition
                        )
                )
            };
        }
    }

    fn check_one_subject(&mut self, members: &[Member], rule: &str) {
        let mut subjects = members
            .iter()
            .filter(|m| matches!(m.kind, MemberKind::Subject(_)));
        let _ = subjects.next();
        for duplicate in subjects {
            self.error(
                duplicate,
                format!("{rule}: a requirement or case may own at most one subject"),
            );
        }
    }

    fn check_one_objective(&mut self, members: &[Member], rule: &str) {
        let mut objectives = members
            .iter()
            .filter(|m| matches!(m.kind, MemberKind::Objective(_)));
        let _ = objectives.next();
        for duplicate in objectives {
            self.error(
                duplicate,
                format!("{rule}: a case may own at most one objective"),
            );
        }
    }

    fn check_subject_position(&mut self, members: &[Member], rule: &str) {
        let Some((subject_index, subject)) = members
            .iter()
            .enumerate()
            .find(|(_, m)| matches!(m.kind, MemberKind::Subject(_)))
        else {
            return;
        };
        let first_input = members.iter().position(|member| match &member.kind {
            MemberKind::Subject(_) | MemberKind::Actor(_) | MemberKind::Stakeholder(_) => true,
            MemberKind::Usage(usage) => matches!(
                usage.prefix.direction,
                Some(FeatureDirection::In | FeatureDirection::InOut)
            ),
            _ => false,
        });
        if first_input != Some(subject_index) {
            self.error(
                subject,
                format!("{rule}: the subject parameter must be the first input"),
            );
        }
    }

    fn check_definition_cardinality(&mut self, kind: DefKind, members: &[Member]) {
        if matches!(
            kind,
            DefKind::Requirement | DefKind::Concern | DefKind::Viewpoint
        ) {
            self.check_one_subject(members, "validateRequirementDefinitionOnlyOneSubject");
            self.check_subject_position(
                members,
                "validateRequirementDefinitionSubjectParameterPosition",
            );
        }
        if matches!(
            kind,
            DefKind::Case | DefKind::Analysis | DefKind::Verification | DefKind::UseCase
        ) {
            self.check_one_subject(members, "validateCaseDefinitionOnlyOneSubject");
            self.check_one_objective(members, "validateCaseDefinitionOnlyOneObjective");
            self.check_subject_position(members, "validateCaseDefinitionSubjectParameterPosition");
        }
        if kind == DefKind::Flow {
            let mut ends = members.iter().filter(|member| {
                matches!(
                    &member.kind,
                    MemberKind::Usage(usage) if usage.prefix.is_end
                )
            });
            let _ = ends.next();
            let _ = ends.next();
            for excess in ends {
                self.error(
                    excess,
                    "validateFlowDefinitionFlowEnds: a flow definition may not \
                     have more than two flow ends"
                        .into(),
                );
            }
        }
    }

    fn check_usage_cardinality(&mut self, kind: UsageKind, members: &[Member]) {
        if matches!(
            kind,
            UsageKind::Requirement | UsageKind::Concern | UsageKind::Viewpoint | UsageKind::Satisfy
        ) {
            self.check_one_subject(members, "validateRequirementUsageOnlyOneSubject");
            self.check_subject_position(
                members,
                "validateRequirementUsageSubjectParameterPosition",
            );
        }
        if matches!(
            kind,
            UsageKind::Case
                | UsageKind::Analysis
                | UsageKind::Verification
                | UsageKind::UseCase
                | UsageKind::Include
        ) {
            self.check_one_subject(members, "validateCaseUsageOnlyOneSubject");
            self.check_one_objective(members, "validateCaseUsageOnlyOneObjective");
            self.check_subject_position(members, "validateCaseUsageSubjectParameterPosition");
        }
    }

    /// Namespace distinguishability (KerML 8.2.3.5, owned members only).
    /// Equal names are legal when neither member element's metaclass
    /// conforms to the other; this syntax-stage check handles concrete
    /// sibling metaclasses and leaves imported/inherited membership
    /// expansion to the resolved-model stage.
    fn check_duplicate_names(&mut self, members: &[Member]) {
        let mut seen: HashMap<&str, Vec<NamedMetaclass>> = HashMap::new();
        for m in members {
            let Some(id) = member_identification(&m.kind) else {
                continue;
            };
            let Some(metaclass) = member_metaclass(&m.kind) else {
                continue;
            };
            let mut names: Vec<&Name> = Vec::new();
            names.extend(&id.short_name);
            // An element whose short name equals its name only declares one
            // distinguishable name.
            names.extend(id.name.iter().filter(|n| {
                id.short_name.as_ref().map(|s| s.value.as_str()) != Some(n.value.as_str())
            }));
            for name in names {
                let prior = seen.entry(name.value.as_str()).or_default();
                if prior
                    .iter()
                    .copied()
                    .any(|p| !metaclasses_are_distinguishable(p, metaclass))
                {
                    self.diags.push(Diagnostic::error(
                        name.span,
                        format!(
                            "the name `{}` is already used by an earlier member \
                             of the same namespace whose metaclass is not \
                             distinguishable from this member",
                            name.value
                        ),
                    ));
                }
                prior.push(metaclass);
            }
        }
    }

    fn check_member(&mut self, ctx: Ctx, owner_is_variation: bool, m: &Member) {
        if let Some(mult) = &m.leading_then_multiplicity {
            self.walk_multiplicity(mult);
        }
        // Empty-succession shorthand (`then <member>`): only before
        // occurrence-category usage members, and never at package level
        // (`EmptySuccessionMember` in the *Body grammar rules).
        if m.leading_then {
            let ok = matches!(
                ctx,
                Ctx::Definition
                    | Ctx::Interface
                    | Ctx::Action
                    | Ctx::State
                    | Ctx::Calculation
                    | Ctx::Requirement
                    | Ctx::Case
                    | Ctx::ViewDef
                    | Ctx::View
            ) && matches!(
                &m.kind,
                MemberKind::Usage(u)
                    if matches!(usage_cat(u), Cat::Structure | Cat::Behavior | Cat::ActionNode)
            );
            if !ok {
                self.error(
                    m,
                    format!(
                        "an implied succession (`then`) may not precede {} in {}",
                        member_desc(&m.kind),
                        ctx.describe()
                    ),
                );
            }
        }

        // `ImportPrefix` requires an explicit visibility indicator in both
        // dialects (`visibility = VisibilityIndicator`, not optional).
        // `expose` members are exempt: the keyword itself is the indicator.
        if matches!(m.kind, MemberKind::Import(_)) && m.visibility.is_none() {
            self.error(
                m,
                "an import must declare an explicit visibility \
                 (`public`, `private`, or `protected`)"
                    .into(),
            );
        }

        // Variant members are only legal inside a variation definition/usage.
        if let MemberKind::Usage(u) = &m.kind {
            if u.prefix.is_variant && !owner_is_variation {
                self.error(
                    m,
                    "a `variant` member is only allowed in the body of a \
                     `variation` definition or usage"
                        .into(),
                );
                return;
            }
        }

        let ok = match &m.kind {
            // Annotating elements are legal in every body.
            MemberKind::Comment(_) | MemberKind::Doc(_) | MemberKind::TextualRep(_) => true,
            // Imports, aliases, and definition elements: everywhere except
            // enumeration bodies (annotations + enumerated values only).
            MemberKind::Import(_) | MemberKind::Alias(_) => ctx != Ctx::Enumeration,
            MemberKind::Package(_) | MemberKind::Definition(_) | MemberKind::Dependency(_) => {
                ctx != Ctx::Enumeration
            }
            // KerML standalone relationships / multiplicities are
            // `NonFeatureElement`s (KerML has no enumeration bodies).
            MemberKind::Relationship(_) | MemberKind::MultiplicityDecl(_) => {
                ctx != Ctx::Enumeration
            }
            MemberKind::Filter(_) => {
                matches!(ctx, Ctx::Package | Ctx::ViewDef | Ctx::View | Ctx::KPackage)
            }
            MemberKind::InitialNode(_) => {
                matches!(ctx, Ctx::Action | Ctx::Calculation | Ctx::Case)
            }
            MemberKind::Subject(_) | MemberKind::Actor(_) => {
                matches!(ctx, Ctx::Requirement | Ctx::Case)
            }
            MemberKind::Stakeholder(_)
            | MemberKind::RequirementConstraint { .. }
            | MemberKind::FramedConcern(_)
            | MemberKind::RequirementVerification(_) => ctx == Ctx::Requirement,
            MemberKind::Objective(_) => ctx == Ctx::Case,
            MemberKind::StateSubaction { .. } => ctx == Ctx::State,
            MemberKind::Expose(_) => ctx == Ctx::View,
            MemberKind::Render(_) => matches!(ctx, Ctx::ViewDef | Ctx::View),
            MemberKind::Return(_) | MemberKind::Result(_) => {
                matches!(ctx, Ctx::Calculation | Ctx::Case | Ctx::KFunction)
            }
            MemberKind::Usage(u) => self.usage_ok(ctx, u),
        };
        if !ok {
            let rule = match m.kind {
                MemberKind::Subject(_) => Some("validateSubjectMembershipOwningType: "),
                MemberKind::Objective(_) => Some("validateObjectiveMembershipOwningType: "),
                _ => None,
            };
            self.error(
                m,
                format!(
                    "{}{} is not allowed in {}",
                    rule.unwrap_or(""),
                    member_desc(&m.kind),
                    ctx.describe()
                ),
            );
        }
    }

    fn usage_ok(&self, ctx: Ctx, u: &Usage) -> bool {
        // KerML bodies have a uniform feature-member model.
        if ctx.is_kerml() {
            return true;
        }
        match usage_cat(u) {
            Cat::Annotation | Cat::KFeature => true,
            Cat::NonOccurrence => match ctx {
                Ctx::Package
                | Ctx::Definition
                | Ctx::Action
                | Ctx::State
                | Ctx::Calculation
                | Ctx::Requirement
                | Ctx::Case
                | Ctx::ViewDef
                | Ctx::View => true,
                // `InterfaceNonOccurrenceUsageElement` excludes keyword-less
                // and extended usages — unless declared as an interface end
                // (`DefaultInterfaceEnd`).
                Ctx::Interface => {
                    !matches!(u.kind, UsageKind::Default | UsageKind::Extended) || u.prefix.is_end
                }
                // `EnumeratedValue`: optionally `enum`-keyword or extended.
                Ctx::Enumeration => matches!(
                    u.kind,
                    UsageKind::Enum | UsageKind::Default | UsageKind::Extended
                ),
                // `MetadataBodyUsage`: (`ref`) redefining reference usages.
                Ctx::Metadata => matches!(u.kind, UsageKind::Ref | UsageKind::Default),
                Ctx::KRoot | Ctx::KPackage | Ctx::KType | Ctx::KFunction => true,
            },
            Cat::Structure | Cat::Behavior => matches!(
                ctx,
                Ctx::Package
                    | Ctx::Definition
                    | Ctx::Interface
                    | Ctx::Action
                    | Ctx::State
                    | Ctx::Calculation
                    | Ctx::Requirement
                    | Ctx::Case
                    | Ctx::ViewDef
                    | Ctx::View
            ),
            Cat::ActionNode => matches!(ctx, Ctx::Action | Ctx::Calculation | Ctx::Case),
            Cat::TargetSuccession => {
                matches!(ctx, Ctx::Action | Ctx::Calculation | Ctx::Case | Ctx::State)
            }
            Cat::Transition => {
                let UsageDetail::Transition {
                    trigger,
                    effect,
                    guard,
                    is_default,
                    ..
                } = &u.detail
                else {
                    return true;
                };
                match ctx {
                    // Full transition usages (with triggers/effects/sources)
                    // belong to state bodies; `else t;` default targets do
                    // not (they are `DefaultTargetSuccession`s).
                    Ctx::State => !is_default,
                    // Action bodies (and calc/case bodies, which include
                    // `ActionBodyItem`) take the guarded/default succession
                    // shorthands: no trigger, no effect.
                    Ctx::Action | Ctx::Calculation | Ctx::Case => {
                        trigger.is_none() && effect.is_none() && (guard.is_some() || *is_default)
                    }
                    _ => false,
                }
            }
        }
    }

    fn walk_member_children(&mut self, ctx: Ctx, m: &Member) {
        match &m.kind {
            MemberKind::Package(p) => {
                let child = match self.dialect {
                    Dialect::Sysml => Ctx::Package,
                    Dialect::Kerml if p.is_namespace => Ctx::KRoot,
                    Dialect::Kerml => Ctx::KPackage,
                };
                if let Some(body) = &p.body {
                    self.walk_members(body, child, false);
                }
            }
            MemberKind::Import(i) | MemberKind::Expose(i) => {
                for f in &i.filters {
                    self.walk_expr(f);
                }
            }
            MemberKind::Alias(_)
            | MemberKind::Comment(_)
            | MemberKind::Doc(_)
            | MemberKind::TextualRep(_)
            | MemberKind::Dependency(_)
            | MemberKind::InitialNode(_)
            | MemberKind::Relationship(_) => {}
            MemberKind::MultiplicityDecl(d) => {
                if let Some(mult) = &d.range {
                    self.walk_multiplicity(mult);
                }
                if let Some(body) = &d.body {
                    // KerML `RelationshipBody`: annotations and owned elements.
                    self.walk_members(body, Ctx::KType, false);
                }
            }
            MemberKind::Definition(d) => {
                if let Some(mult) = &d.multiplicity {
                    self.walk_multiplicity(mult);
                }
                if let Some(body) = &d.body {
                    self.check_definition_cardinality(d.kind, body);
                    self.walk_members(body, self.ctx_for_def(d.kind), d.prefix.is_variation);
                }
            }
            MemberKind::Usage(u) => self.walk_usage(u, self.ctx_for_usage(u.kind)),
            MemberKind::Filter(e) | MemberKind::Result(e) => self.walk_expr(e),
            // Grammar-fixed body contexts of the special usage members.
            MemberKind::Subject(u) | MemberKind::Actor(u) | MemberKind::Stakeholder(u) => {
                self.walk_usage(u, Ctx::Definition)
            }
            MemberKind::Objective(u) => self.walk_usage(u, Ctx::Requirement),
            MemberKind::RequirementConstraint { usage, .. } => {
                self.walk_usage(usage, Ctx::Calculation)
            }
            MemberKind::FramedConcern(u) | MemberKind::RequirementVerification(u) => {
                self.walk_usage(u, Ctx::Requirement)
            }
            MemberKind::StateSubaction { action, .. } => {
                if let Some(u) = action {
                    self.walk_usage(u, Ctx::Action);
                }
            }
            MemberKind::Render(u) => self.walk_usage(u, Ctx::Definition),
            MemberKind::Return(u) => {
                let ctx = match self.dialect {
                    Dialect::Sysml => Ctx::Definition,
                    Dialect::Kerml => Ctx::KType,
                };
                self.walk_usage(u, ctx);
            }
        }
        let _ = ctx;
    }

    fn walk_usage(&mut self, u: &Usage, body_ctx: Ctx) {
        self.walk_declaration(&u.declaration);
        if let Some(v) = &u.value {
            self.walk_expr(&v.expr);
        }
        self.walk_detail(&u.detail);
        if let Some(body) = &u.body {
            self.check_usage_cardinality(u.kind, body);
            self.walk_members(body, body_ctx, u.prefix.is_variation);
        }
    }

    fn walk_declaration(&mut self, d: &FeatureDeclaration) {
        if let Some(m) = &d.multiplicity {
            self.walk_multiplicity(m);
        }
    }

    fn walk_multiplicity(&mut self, m: &Multiplicity) {
        if let Some(l) = &m.lower {
            self.walk_expr(l);
        }
        self.walk_expr(&m.upper);
    }

    fn walk_connector_end(&mut self, e: &ConnectorEnd) {
        if let Some(m) = &e.multiplicity {
            self.walk_multiplicity(m);
        }
    }

    fn walk_payload(&mut self, p: &PayloadPart) {
        if let Some(m) = &p.multiplicity {
            self.walk_multiplicity(m);
        }
        if let Some(v) = &p.value {
            self.walk_expr(&v.expr);
        }
    }

    fn walk_detail(&mut self, d: &UsageDetail) {
        match d {
            UsageDetail::None | UsageDetail::Metadata { .. } | UsageDetail::Satisfy { .. } => {}
            UsageDetail::Assert { .. } => {}
            UsageDetail::Connector { ends } | UsageDetail::Binding { ends } => {
                for e in ends {
                    self.walk_connector_end(e);
                }
            }
            UsageDetail::Succession { source, target } => {
                if let Some(s) = source {
                    self.walk_connector_end(s);
                }
                self.walk_connector_end(target);
            }
            UsageDetail::Flow {
                payload,
                source: _,
                target: _,
            } => {
                if let Some(p) = payload {
                    self.walk_payload(p);
                }
            }
            UsageDetail::Accept {
                payload,
                trigger,
                via,
            } => {
                self.walk_payload(payload);
                if let Some(t) = trigger {
                    self.walk_expr(&t.expr);
                }
                if let Some(v) = via {
                    self.walk_expr(v);
                }
            }
            UsageDetail::Send { payload, via, to } => {
                for e in [payload, via, to].into_iter().flatten() {
                    self.walk_expr(e);
                }
            }
            UsageDetail::Assign { target, value } => {
                self.walk_expr(target);
                self.walk_expr(value);
            }
            UsageDetail::Terminate { target } => {
                if let Some(e) = target {
                    self.walk_expr(e);
                }
            }
            UsageDetail::IfNode {
                cond,
                then_body,
                else_body,
            } => {
                self.walk_expr(cond);
                self.walk_usage(then_body, self.ctx_for_usage(then_body.kind));
                if let Some(e) = else_body {
                    self.walk_usage(e, self.ctx_for_usage(e.kind));
                }
            }
            UsageDetail::WhileLoop { cond, body, until } => {
                if let Some(c) = cond {
                    self.walk_expr(c);
                }
                self.walk_usage(body, self.ctx_for_usage(body.kind));
                if let Some(u) = until {
                    self.walk_expr(u);
                }
            }
            UsageDetail::ForLoop { var, seq, body } => {
                self.walk_declaration(var);
                self.walk_expr(seq);
                self.walk_usage(body, self.ctx_for_usage(body.kind));
            }
            UsageDetail::Transition {
                source: _,
                trigger,
                guard,
                effect,
                target,
                is_default: _,
            } => {
                if let Some(t) = trigger {
                    self.walk_detail(t);
                }
                if let Some(g) = guard {
                    self.walk_expr(g);
                }
                if let Some(e) = effect {
                    self.walk_usage(e, self.ctx_for_usage(e.kind));
                }
                if let Some(t) = target {
                    self.walk_connector_end(t);
                }
            }
        }
    }

    fn walk_expr(&mut self, e: &Expr) {
        match &e.kind {
            ExprKind::Literal(_)
            | ExprKind::Null
            | ExprKind::BodyTerminator
            | ExprKind::Ref(_)
            | ExprKind::MetadataAccess { .. }
            | ExprKind::Extent { .. } => {}
            ExprKind::Conditional {
                cond,
                then_branch,
                else_branch,
            } => {
                self.walk_expr(cond);
                self.walk_expr(then_branch);
                self.walk_expr(else_branch);
            }
            ExprKind::Binary { lhs, rhs, .. } => {
                self.walk_expr(lhs);
                self.walk_expr(rhs);
            }
            ExprKind::Unary { operand, .. } => self.walk_expr(operand),
            ExprKind::Classification { operand, .. } => {
                if let Some(o) = operand {
                    self.walk_expr(o);
                }
            }
            ExprKind::ChainStep { target, .. } => self.walk_expr(target),
            ExprKind::Index { target, index } => {
                self.walk_expr(target);
                self.walk_expr(index);
            }
            ExprKind::Bracket { target, arg } => {
                self.walk_expr(target);
                self.walk_expr(arg);
            }
            ExprKind::Arrow { target, args, .. } => {
                self.walk_expr(target);
                match args {
                    ArrowArgs::Body(b) => self.walk_expr(b),
                    ArrowArgs::FunctionRef(_) => {}
                    ArrowArgs::List(list) => {
                        for a in list {
                            self.walk_expr(&a.value);
                        }
                    }
                }
            }
            ExprKind::Collect { target, body } | ExprKind::Select { target, body } => {
                self.walk_expr(target);
                self.walk_expr(body);
            }
            ExprKind::Invocation { args, .. } | ExprKind::Constructor { args, .. } => {
                for a in args {
                    self.walk_expr(&a.value);
                }
            }
            ExprKind::Body { members } => {
                self.walk_members(members, self.expr_body_ctx(), false);
            }
            ExprKind::Sequence(items) => {
                for i in items {
                    self.walk_expr(i);
                }
            }
        }
    }
}
