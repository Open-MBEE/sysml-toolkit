//! Query-local, bounded evidence for stored type specialization.
//!
//! Positive witnesses use declaration identities. Negative facts require a
//! complete stored/provider walk and audited required library bases at every
//! visited non-conjugated type. Other families remain unknown; no unsupported
//! base omission is a negative fact.
use super::{Builder, provider_completeness::ProviderCompleteness, semantic_ownership};
use crate::lift::usage_kind_of;
use crate::metaclass::conforms;
use crate::metaclass::is_a;
use std::collections::{HashMap, HashSet};
use sysmlv2_syntax::ast::Dialect;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SupertypesFailure {
    Incomplete,
    UnsupportedConfiguration,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum FeatureRequirementsFailure {
    Unsupported,
    InvalidRelationship,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum RelationFact {
    Yes,
    No,
    Unknown,
}

impl RelationFact {
    /// A complete universal condition is refuted by any decisive negative,
    /// even when another member's compatibility remains unproved.
    pub(super) fn all(facts: impl IntoIterator<Item = Self>) -> Self {
        let mut unknown = false;
        for fact in facts {
            match fact {
                Self::Yes => {}
                Self::No => return Self::No,
                Self::Unknown => unknown = true,
            }
        }
        if unknown { Self::Unknown } else { Self::Yes }
    }
}

#[derive(Clone)]
struct Bases {
    targets: Vec<usize>,
    complete: bool,
}

struct StoredBases {
    targets: Vec<usize>,
    target_set: HashSet<usize>,
    complete: bool,
    conjugated: bool,
    final_chain: Option<usize>,
    duplicate_targets: bool,
    feature_chain_complete: bool,
}

/// Reuse only within one query over an unchanged model.
#[derive(Default)]
pub(super) struct TypeRelations {
    publication: Option<super::publication::Revision>,
    rows: Option<crate::layered::Revision>,
    metadata: Option<Option<std::sync::Arc<()>>>,
    providers: ProviderCompleteness,
    planner_state: Option<(bool, bool)>,
    retained_plan: Option<std::sync::Arc<super::implied::SupportedImpliedSpecializations>>,
    bases: HashMap<usize, Bases>,
    // allSupertypes reachability only; receiver conjugation normalization is
    // separate and must never reuse a reflexive closure fact as specializes.
    known: HashMap<(usize, usize, usize), bool>,
    conjugations: HashMap<usize, Option<usize>>,
    owned_feature_witness: HashMap<usize, bool>,
    evidence: FeaturingEvidence,
    required_library: Option<HashMap<&'static str, Option<usize>>>,
}

/// Positive type-kind facts for a composition's Feature owner. Checked readers
/// supply these only after a complete projection; static planning uses validated
/// owned typing witnesses and therefore cannot infer absent facts.
#[derive(Clone, Copy, Debug, Default)]
pub(super) struct CompositionOwner {
    pub(super) object: bool,
    pub(super) occurrence: bool,
}

/// Conditional composition requirements, including certified Feature owners.
pub(super) fn composite_roles(
    kind: &str,
    owner: &str,
    object: bool,
    occurrence: bool,
    composite: bool,
    portion: bool,
    owner_types: CompositionOwner,
) -> Vec<&'static str> {
    let mut roles = Vec::new();
    let occurrence_owner =
        conforms(owner, "Class") || owner_types.occurrence || conforms(owner, "OccurrenceUsage");
    let occurrence_typed = occurrence || conforms(kind, "OccurrenceUsage");
    // A portion typed by a Class in a Class or a Class-typed feature (KerML
    // `checkFeaturePortionSpecialization`).
    if portion && occurrence_typed && occurrence_owner {
        roles.push("Occurrences::Occurrence::portions");
    }
    // The composition roles are a composite's.
    if !composite {
        return roles;
    }
    if occurrence_owner && occurrence_typed {
        roles.push("Occurrences::Occurrence::suboccurrences");
    }
    if (conforms(owner, "Structure") || owner_types.object) && object {
        roles.push("Objects::Object::subobjects");
    }
    if conforms(owner, "ItemDefinition") || conforms(owner, "ItemUsage") {
        if conforms(kind, "ItemUsage") {
            roles.push("Items::Item::subitems");
        }
        if conforms(kind, "PartUsage") {
            roles.push("Items::Item::subparts");
        }
    }
    roles
}

/// The owner contexts under which a composite member's typing adds the
/// conditional composition roles (`composite_roles`): the planner plans
/// them for a member under an exact FeatureMembership of one of these
/// owners and for no other (`implied.rs`, `owned_typing_requirements`),
/// so the checked audit requires them there and nowhere else.
pub(super) fn composite_owner_context(owner: &str) -> bool {
    matches!(
        owner,
        "Type"
            | "Classifier"
            | "Class"
            | "Structure"
            | "DataType"
            | "Definition"
            | "AttributeDefinition"
            | "OccurrenceDefinition"
            | "ItemDefinition"
            | "PartDefinition"
            | "Feature"
            | "OccurrenceUsage"
            | "ItemUsage"
            | "PartUsage"
    )
}

/// The library roles the audits name, each with the metaclass its
/// declaration conforms to: the root types and features of the Kernel
/// Semantic Library, the definitions and usage roles of the Systems
/// Library (`implicit_def_bases`, `implicit_usage_bases`) and the
/// conditional composition, flow, invariant and binary roles. A role is
/// resolved among the loaded library's element names by its declared
/// qualified name, once, under the same bounded identity authority as the
/// rest of the proof; a replacement library that spells a role with
/// another kind, twice or not at all leaves every audit naming it
/// incomplete.
const ROLE_KINDS: &[(&str, &str)] = &[
    ("Base::Anything", "Classifier"),
    ("Base::DataValue", "DataType"),
    ("Base::things", "Feature"),
    ("Base::dataValues", "Feature"),
    ("Base::naturals", "Feature"),
    ("Base::exactlyOne", "Feature"),
    ("Base::zeroOrOne", "Feature"),
    ("Occurrences::Occurrence", "Class"),
    ("Occurrences::HappensLink", "Association"),
    ("Occurrences::occurrences", "Feature"),
    ("Occurrences::happensBeforeLinks", "Feature"),
    ("Occurrences::Occurrence::suboccurrences", "Feature"),
    ("Occurrences::Occurrence::snapshots", "Feature"),
    ("Occurrences::Occurrence::timeSlices", "Feature"),
    ("Occurrences::Occurrence::portions", "Feature"),
    (
        "Occurrences::Occurrence::timeEnclosedOccurrences",
        "Feature",
    ),
    ("Occurrences::Life", "Class"),
    ("Objects::Object", "Structure"),
    ("Objects::LinkObject", "AssociationStructure"),
    ("Objects::objects", "Feature"),
    ("Objects::Object::subobjects", "Feature"),
    ("Links::Link", "Association"),
    ("Links::BinaryLink", "Association"),
    ("Links::SelfLink", "Association"),
    ("Links::links", "Feature"),
    ("Links::binaryLinks", "Feature"),
    ("Performances::Performance", "Behavior"),
    ("Performances::Evaluation", "Function"),
    ("Performances::BooleanEvaluation", "Predicate"),
    ("Performances::performances", "Step"),
    ("Performances::evaluations", "Expression"),
    ("Performances::booleanEvaluations", "Expression"),
    ("Performances::trueEvaluations", "Expression"),
    ("Performances::falseEvaluations", "Expression"),
    ("Performances::literalEvaluations", "Expression"),
    ("Performances::literalBooleanEvaluations", "Expression"),
    ("Performances::literalIntegerEvaluations", "Expression"),
    ("Performances::literalRationalEvaluations", "Expression"),
    ("Performances::literalStringEvaluations", "Expression"),
    ("Performances::nullEvaluations", "Expression"),
    ("Performances::metadataAccessEvaluations", "Expression"),
    ("Performances::constructorEvaluations", "Expression"),
    ("Transfers::Transfer", "Interaction"),
    ("Transfers::transfers", "Step"),
    ("Transfers::flowTransfers", "Step"),
    ("Transfers::flowTransfersBefore", "Step"),
    ("Metaobjects::Metaobject", "Metaclass"),
    ("Metaobjects::metaobjects", "Feature"),
    ("Items::Item", "ItemDefinition"),
    ("Items::items", "ItemUsage"),
    ("Items::Item::subitems", "ItemUsage"),
    ("Items::Item::subparts", "PartUsage"),
    ("Items::Item::checkedConstraints", "ConstraintUsage"),
    ("Parts::Part", "PartDefinition"),
    ("Parts::parts", "PartUsage"),
    ("Ports::Port", "PortDefinition"),
    ("Ports::ports", "PortUsage"),
    ("Actions::Action", "ActionDefinition"),
    ("Actions::actions", "ActionUsage"),
    ("Actions::acceptActions", "ActionUsage"),
    ("Actions::sendActions", "ActionUsage"),
    ("Actions::assignmentActions", "ActionUsage"),
    ("Actions::terminateActions", "ActionUsage"),
    ("Actions::ifThenActions", "ActionUsage"),
    ("Actions::ifThenElseActions", "ActionUsage"),
    ("Actions::whileLoopActions", "ActionUsage"),
    ("Actions::forLoopActions", "ActionUsage"),
    ("Actions::Action::merges", "ActionUsage"),
    ("Actions::Action::decisions", "ActionUsage"),
    ("Actions::Action::joins", "ActionUsage"),
    ("Actions::Action::forks", "ActionUsage"),
    ("Actions::Action::subactions", "ActionUsage"),
    ("Actions::Action::whileLoops", "ActionUsage"),
    ("Actions::Action::forLoops", "ActionUsage"),
    ("Actions::Action::ifSubactions", "ActionUsage"),
    ("Actions::Action::assignments", "ActionUsage"),
    ("Actions::Action::sendSubactions", "ActionUsage"),
    ("Actions::Action::acceptSubactions", "ActionUsage"),
    ("Actions::Action::terminateSubactions", "ActionUsage"),
    ("Actions::Action::decisionTransitions", "ActionUsage"),
    ("Actions::TransitionAction::accepter", "ActionUsage"),
    ("Actions::TransitionAction::effect", "ActionUsage"),
    (
        "TransitionPerformances::TransitionPerformance::guard",
        "BooleanExpression",
    ),
    ("Actions::transitionActions", "ActionUsage"),
    ("States::StateAction", "StateDefinition"),
    ("States::stateActions", "StateUsage"),
    ("States::StateAction::substates", "ActionUsage"),
    ("States::StateAction::exclusiveStates", "StateUsage"),
    ("States::StateAction::stateTransitions", "ActionUsage"),
    ("States::StateAction::entryAction", "ActionUsage"),
    ("States::StateAction::doAction", "ActionUsage"),
    ("States::StateAction::exitAction", "ActionUsage"),
    ("Parts::Part::ownedActions", "ActionUsage"),
    ("Parts::Part::performedActions", "ActionUsage"),
    ("Parts::Part::ownedStates", "StateUsage"),
    ("Parts::Part::exhibitedStates", "StateUsage"),
    ("Parts::Part::ownedPorts", "PortUsage"),
    ("Ports::Port::subports", "PortUsage"),
    ("Calculations::Calculation", "CalculationDefinition"),
    ("Calculations::calculations", "CalculationUsage"),
    (
        "Calculations::Calculation::subcalculations",
        "CalculationUsage",
    ),
    ("Constraints::ConstraintCheck", "ConstraintDefinition"),
    ("Constraints::constraintChecks", "ConstraintUsage"),
    ("Constraints::assertedConstraintChecks", "ConstraintUsage"),
    ("Constraints::negatedConstraintChecks", "ConstraintUsage"),
    ("Requirements::RequirementCheck", "RequirementDefinition"),
    (
        "Requirements::RequirementCheck::subrequirements",
        "RequirementUsage",
    ),
    ("Requirements::RequirementCheck::concerns", "ConcernUsage"),
    (
        "Requirements::RequirementCheck::assumptions",
        "ConstraintUsage",
    ),
    (
        "Requirements::RequirementCheck::constraints",
        "ConstraintUsage",
    ),
    ("Requirements::RequirementCheck::actors", "PartUsage"),
    ("Requirements::RequirementCheck::stakeholders", "PartUsage"),
    ("Requirements::ConcernCheck", "ConcernDefinition"),
    ("Requirements::requirementChecks", "RequirementUsage"),
    ("Requirements::concernChecks", "ConcernUsage"),
    (
        "Requirements::satisfiedRequirementChecks",
        "RequirementUsage",
    ),
    (
        "Requirements::notSatisfiedRequirementChecks",
        "RequirementUsage",
    ),
    ("Cases::Case", "CaseDefinition"),
    ("Cases::cases", "CaseUsage"),
    ("Cases::Case::subcases", "CaseUsage"),
    ("Cases::Case::actors", "PartUsage"),
    ("AnalysisCases::AnalysisCase", "AnalysisCaseDefinition"),
    ("AnalysisCases::analysisCases", "AnalysisCaseUsage"),
    (
        "AnalysisCases::AnalysisCase::subAnalysisCases",
        "AnalysisCaseUsage",
    ),
    (
        "VerificationCases::VerificationCase",
        "VerificationCaseDefinition",
    ),
    (
        "VerificationCases::verificationCases",
        "VerificationCaseUsage",
    ),
    (
        "VerificationCases::VerificationCase::subVerificationCases",
        "VerificationCaseUsage",
    ),
    (
        "VerificationCases::VerificationCase::obj::requirementVerifications",
        "RequirementUsage",
    ),
    ("UseCases::UseCase", "UseCaseDefinition"),
    ("UseCases::useCases", "UseCaseUsage"),
    ("UseCases::UseCase::subUseCases", "UseCaseUsage"),
    ("UseCases::UseCase::includedUseCases", "UseCaseUsage"),
    ("Views::View", "ViewDefinition"),
    ("Views::ViewpointCheck", "ViewpointDefinition"),
    ("Views::Rendering", "RenderingDefinition"),
    ("Views::views", "ViewUsage"),
    ("Views::viewpointChecks", "ViewpointUsage"),
    ("Views::renderings", "RenderingUsage"),
    ("Views::View::subviews", "ViewUsage"),
    ("Views::View::viewRendering", "RenderingUsage"),
    ("Views::View::viewpointSatisfactions", "ViewpointUsage"),
    ("Views::Rendering::subrenderings", "RenderingUsage"),
    ("Connections::Connection", "ConnectionDefinition"),
    ("Connections::BinaryConnection", "ConnectionDefinition"),
    ("Connections::connections", "ConnectionUsage"),
    ("Connections::binaryConnections", "ConnectionUsage"),
    ("Interfaces::Interface", "InterfaceDefinition"),
    ("Interfaces::BinaryInterface", "InterfaceDefinition"),
    ("Interfaces::interfaces", "InterfaceUsage"),
    ("Interfaces::binaryInterfaces", "InterfaceUsage"),
    ("Allocations::Allocation", "AllocationDefinition"),
    ("Allocations::allocations", "AllocationUsage"),
    ("Flows::MessageAction", "FlowDefinition"),
    ("Flows::messages", "FlowUsage"),
    ("Flows::flows", "FlowUsage"),
    ("Flows::successionFlows", "FlowUsage"),
    ("Metadata::MetadataItem", "MetadataDefinition"),
    ("Metadata::metadataItems", "ItemUsage"),
];

/// The library heritage a definition or plain Kernel type of `kind`
/// implicitly has (SysML 8.4.2 Table 31, KerML Table 10), its own implied
/// base first (`implicit_def_bases`) and then the bases that base declares
/// in the standard library, down to `Base::Anything`: the audited
/// obligations of a negative specialization proof, verified through the
/// shared graph rather than assumed of a replacement library. A kind
/// outside the table (a conjugated port definition) has no audited chain.
fn definition_chain(kind: &str) -> Option<&'static [&'static str]> {
    const ANYTHING: &[&str] = &["Base::Anything"];
    const OCCURRENCE: &[&str] = &["Occurrences::Occurrence", "Base::Anything"];
    const OBJECT: &[&str] = &[
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const DATA: &[&str] = &["Base::DataValue", "Base::Anything"];
    const ITEM: &[&str] = &[
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const PART: &[&str] = &[
        "Parts::Part",
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const PORT: &[&str] = &[
        "Ports::Port",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const METACLASS: &[&str] = &[
        "Metaobjects::Metaobject",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const METADATA: &[&str] = &[
        "Metadata::MetadataItem",
        "Metaobjects::Metaobject",
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const PERFORMANCE: &[&str] = &[
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const EVALUATION: &[&str] = &[
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const BOOLEAN_EVALUATION: &[&str] = &[
        "Performances::BooleanEvaluation",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const LINK: &[&str] = &["Links::Link", "Base::Anything"];
    const LINK_OBJECT: &[&str] = &[
        "Objects::LinkObject",
        "Links::Link",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const TRANSFER: &[&str] = &[
        "Transfers::Transfer",
        "Performances::Performance",
        "Links::BinaryLink",
        "Links::Link",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const ACTION: &[&str] = &[
        "Actions::Action",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const STATE: &[&str] = &[
        "States::StateAction",
        "Actions::Action",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const CALCULATION: &[&str] = &[
        "Calculations::Calculation",
        "Actions::Action",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const CONSTRAINT: &[&str] = &[
        "Constraints::ConstraintCheck",
        "Performances::BooleanEvaluation",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const REQUIREMENT: &[&str] = &[
        "Requirements::RequirementCheck",
        "Constraints::ConstraintCheck",
        "Performances::BooleanEvaluation",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const CONCERN: &[&str] = &[
        "Requirements::ConcernCheck",
        "Requirements::RequirementCheck",
        "Constraints::ConstraintCheck",
        "Performances::BooleanEvaluation",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const CASE: &[&str] = &[
        "Cases::Case",
        "Calculations::Calculation",
        "Actions::Action",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const ANALYSIS: &[&str] = &[
        "AnalysisCases::AnalysisCase",
        "Cases::Case",
        "Calculations::Calculation",
        "Actions::Action",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const VERIFICATION: &[&str] = &[
        "VerificationCases::VerificationCase",
        "Cases::Case",
        "Calculations::Calculation",
        "Actions::Action",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const USE_CASE: &[&str] = &[
        "UseCases::UseCase",
        "Cases::Case",
        "Calculations::Calculation",
        "Actions::Action",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const CONNECTION: &[&str] = &[
        "Connections::Connection",
        "Objects::LinkObject",
        "Links::Link",
        "Parts::Part",
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const INTERFACE: &[&str] = &[
        "Interfaces::Interface",
        "Connections::Connection",
        "Objects::LinkObject",
        "Links::Link",
        "Parts::Part",
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const ALLOCATION: &[&str] = &[
        "Allocations::Allocation",
        "Connections::BinaryConnection",
        "Links::BinaryLink",
        "Connections::Connection",
        "Objects::LinkObject",
        "Links::Link",
        "Parts::Part",
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const FLOW: &[&str] = &[
        "Flows::MessageAction",
        "Actions::Action",
        "Performances::Performance",
        "Links::Link",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const VIEW: &[&str] = &[
        "Views::View",
        "Parts::Part",
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const VIEWPOINT: &[&str] = &[
        "Views::ViewpointCheck",
        "Requirements::RequirementCheck",
        "Constraints::ConstraintCheck",
        "Performances::BooleanEvaluation",
        "Performances::Evaluation",
        "Performances::Performance",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    const RENDERING: &[&str] = &[
        "Views::Rendering",
        "Parts::Part",
        "Items::Item",
        "Objects::Object",
        "Occurrences::Occurrence",
        "Base::Anything",
    ];
    Some(match kind {
        "Type" | "Classifier" | "Definition" => ANYTHING,
        "Class" | "OccurrenceDefinition" => OCCURRENCE,
        "Structure" => OBJECT,
        "DataType" | "AttributeDefinition" | "EnumerationDefinition" => DATA,
        "ItemDefinition" => ITEM,
        "PartDefinition" => PART,
        "PortDefinition" => PORT,
        "Metaclass" => METACLASS,
        "MetadataDefinition" => METADATA,
        "Behavior" => PERFORMANCE,
        "Function" => EVALUATION,
        "Predicate" => BOOLEAN_EVALUATION,
        "Association" => LINK,
        "AssociationStructure" => LINK_OBJECT,
        "Interaction" => TRANSFER,
        "ActionDefinition" => ACTION,
        "StateDefinition" => STATE,
        "CalculationDefinition" => CALCULATION,
        "ConstraintDefinition" => CONSTRAINT,
        "RequirementDefinition" => REQUIREMENT,
        "ConcernDefinition" => CONCERN,
        "CaseDefinition" => CASE,
        "AnalysisCaseDefinition" => ANALYSIS,
        "VerificationCaseDefinition" => VERIFICATION,
        "UseCaseDefinition" => USE_CASE,
        "ConnectionDefinition" => CONNECTION,
        "InterfaceDefinition" => INTERFACE,
        "AllocationDefinition" => ALLOCATION,
        "FlowDefinition" => FLOW,
        "ViewDefinition" => VIEW,
        "ViewpointDefinition" => VIEWPOINT,
        "RenderingDefinition" => RENDERING,
        _ => return None,
    })
}

pub(super) const COMPOSITE_ROLES: [&str; 5] = [
    "Occurrences::Occurrence::suboccurrences",
    "Objects::Object::subobjects",
    "Items::Item::subitems",
    "Items::Item::subparts",
    "Occurrences::Occurrence::portions",
];

fn charge(steps: &mut usize, amount: usize) -> Option<()> {
    *steps = steps.saturating_add(amount);
    (*steps <= crate::eval::MAX_STEPS).then_some(())
}

impl TypeRelations {
    /// Discard query-local facts after the caller's semantic stamp changes.
    /// Charge owned containers before traversing or releasing their contents.
    pub(super) fn reset_with_budget(&mut self, steps: &mut usize) -> Option<()> {
        charge(
            steps,
            1usize
                .saturating_add(self.bases.capacity())
                .saturating_add(self.known.capacity())
                .saturating_add(self.conjugations.capacity())
                .saturating_add(self.owned_feature_witness.capacity())
                .saturating_add(self.required_library.as_ref().map_or(0, HashMap::capacity))
                .saturating_add(self.evidence.owners.capacity())
                .saturating_add(self.evidence.featuring.capacity()),
        )?;
        for bases in self.bases.values() {
            charge(steps, bases.targets.len())?;
        }
        for features in self.evidence.featuring.values() {
            charge(steps, features.len())?;
        }
        self.providers.reset_with_budget(steps)?;
        *self = Self::default();
        Some(())
    }

    fn refresh_planner_state(&mut self, b: &mut Builder, steps: &mut usize) -> Option<()> {
        if b.positional_planning {
            return None;
        }
        b.refresh_supported_chain_evidence(Some(&mut *steps))?;
        b.certify_materialized_static_prefix(steps)?;
        let state = (b.semantic_ready, b.positional_redefinitions.is_some());
        let same_plan = match (&self.retained_plan, &b.supported_implied) {
            (None, None) => true,
            (Some(old), Some(current)) => std::sync::Arc::ptr_eq(old, current),
            _ => false,
        };
        if self.planner_state != Some(state) || !same_plan {
            charge(
                steps,
                self.bases
                    .capacity()
                    .saturating_add(self.known.capacity())
                    .saturating_add(self.required_library.as_ref().map_or(0, HashMap::capacity)),
            )?;
            self.bases.clear();
            self.known.clear();
            self.required_library = None;
            self.planner_state = Some(state);
            self.retained_plan = b.supported_implied.clone();
        }
        Some(())
    }

    fn current(&mut self, b: &mut Builder) -> bool {
        if let Some(previous) = &self.metadata {
            let unchanged = match (previous, &b.metadata_association_generation) {
                (None, None) => true,
                (Some(a), Some(z)) => std::sync::Arc::ptr_eq(a, z),
                _ => false,
            };
            if !unchanged {
                return false;
            }
        } else {
            self.metadata = Some(b.metadata_association_generation.clone());
        }
        let rows = b.elements.observe_revision();
        if self
            .rows
            .as_ref()
            .is_some_and(|previous| !previous.same_as(&rows))
        {
            return false;
        }
        self.rows.get_or_insert(rows);
        let epoch = b.publication.revision();
        match &self.publication {
            Some(previous) => previous.same_as(&epoch),
            None => {
                self.publication = Some(epoch);
                true
            }
        }
    }

    /// The features `feature` directly redefines, in order: the checked
    /// targets of its owned Redefinitions, then the positional redefinition
    /// targets the specification implies for a parameter, result or end
    /// (the implied Redefinitions a complete model materializes). `None`
    /// when a Redefinition endpoint is unchecked.
    pub(super) fn direct_redefinitions(
        &mut self,
        b: &mut Builder,
        feature: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        charge(steps, 1)?;
        if !conforms(b.elements.get(feature)?.ty, "Feature") {
            return None;
        }
        let relationships = self.evidence.relationships(b, feature, steps)?;
        let mut targets = Vec::new();
        for relationship in relationships {
            charge(steps, 1)?;
            if !conforms(b.elements.get(relationship)?.ty, "Redefinition") {
                continue;
            }
            let target = endpoint(
                b,
                feature,
                relationship,
                &["redefiningFeature", "subsettingFeature", "specific"],
                &["redefinedFeature", "subsettedFeature", "general"],
                "Feature",
                steps,
            )?;
            if !targets.contains(&target) {
                targets.push(target);
            }
        }
        if let Some(owner) = b.owner_elem(feature) {
            let positional = b.positional_redefinition_targets(feature, owner);
            charge(steps, positional.len())?;
            for target in positional {
                if target != feature && !targets.contains(&target) {
                    targets.push(target);
                }
            }
        }
        Some(targets)
    }

    /// Every feature `feature` redefines, directly or transitively
    /// (KerML `Feature::allRedefinedFeatures()` without `feature` itself),
    /// direct targets first. `None` when any step is unchecked.
    pub(super) fn checked_redefinition_closure(
        &mut self,
        b: &mut Builder,
        feature: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        let mut closure = Vec::new();
        let mut seen = HashSet::from([feature]);
        let mut queue = std::collections::VecDeque::from([feature]);
        while let Some(current) = queue.pop_front() {
            charge(steps, 1)?;
            if closure.len() > super::MAX_RESOLUTION_DEPTH * 64 {
                return None;
            }
            for target in self.direct_redefinitions(b, current, steps)? {
                if seen.insert(target) {
                    closure.push(target);
                    queue.push_back(target);
                }
            }
        }
        Some(closure)
    }

    pub(super) fn specializes(
        &mut self,
        b: &mut Builder,
        specific: usize,
        general: usize,
        steps: &mut usize,
    ) -> RelationFact {
        if !self.current(b) || self.refresh_planner_state(b, steps).is_none() {
            return RelationFact::Unknown;
        }
        // KerML Type::specializes delegates a conjugated RECEIVER to its
        // original type before asking for reflexive allSupertypes membership.
        // This is not the same operation as normalizing every node in that
        // closure: an ordinary type specializing a conjugated type still
        // specializes that intermediate type itself.
        let mut receiver = specific;
        let mut active = HashSet::new();
        for depth in 0..=super::MAX_RESOLUTION_DEPTH {
            if charge(steps, 1).is_none()
                || !b.elements.get(general).is_some_and(|e| is_a!(e, "Type"))
                || !active.insert(receiver)
            {
                return RelationFact::Unknown;
            }
            match self.owned_conjugation(b, receiver, steps) {
                Some(Some(original)) => receiver = original,
                Some(None) => {
                    return self.walk(b, receiver, general, depth, &mut HashSet::new(), steps);
                }
                None => return RelationFact::Unknown,
            }
        }
        RelationFact::Unknown
    }

    /// Complete local receiver classification. Unrelated specialization
    /// endpoint failure does not remove ordinary reflexivity, but a missing,
    /// conflicting or cyclic conjugator cannot bypass receiver normalization.
    pub(super) fn owned_conjugation(
        &mut self,
        b: &mut Builder,
        specific: usize,
        steps: &mut usize,
    ) -> Option<Option<usize>> {
        if !self.current(b) {
            return None;
        }
        charge(steps, 1)?;
        if let Some(&known) = self.conjugations.get(&specific) {
            return Some(known);
        }
        if !conforms(b.elements.get(specific)?.ty, "Type") {
            return None;
        }
        let relationships = self.evidence.relationships(b, specific, steps)?;
        let mut seen = HashSet::new();
        let mut conjugation = None;
        for relation in relationships {
            if !seen.insert(relation) {
                return None;
            }
            if conforms(b.elements.get(relation)?.ty, "Conjugation")
                && conjugation.replace(relation).is_some()
            {
                return None;
            }
        }
        if b.elements[specific]
            .props
            .get("isConjugated")
            .is_some_and(|value| value.as_bool() != Some(conjugation.is_some()))
        {
            return None;
        }
        let original = if let Some(relation) = conjugation {
            self.evidence.index(b, steps)?;
            if self.evidence.incomplete()
                || self.evidence.carrier(b, relation, steps)? != Some(specific)
            {
                return None;
            }
            Some(endpoint(
                b,
                specific,
                relation,
                &["conjugatedType"],
                &["originalType"],
                "Type",
                steps,
            )?)
        } else {
            None
        };
        self.conjugations.insert(specific, original);
        Some(original)
    }

    /// Feature compatibility includes a further shared-redefinition/access
    /// clause. Until that clause has complete evidence, failure to specialize
    /// two Features is unknown, rather than a negative compatibility fact.
    pub(super) fn compatible(
        &mut self,
        b: &mut Builder,
        specific: usize,
        general: usize,
        steps: &mut usize,
    ) -> RelationFact {
        if !self.current(b) {
            return RelationFact::Unknown;
        }
        let fact = self.specializes(b, specific, general, steps);
        if fact == RelationFact::No
            && b.elements
                .get(specific)
                .is_some_and(|e| is_a!(e, "Feature"))
            && b.elements.get(general).is_some_and(|e| is_a!(e, "Feature"))
        {
            // The shared-redefinition clause requires both owned-feature
            // sets to be empty. One reciprocal membership witness refutes it.
            if self.has_owned_feature(b, specific, steps) == Some(true)
                || self.has_owned_feature(b, general, steps) == Some(true)
            {
                RelationFact::No
            } else {
                RelationFact::Unknown
            }
        } else {
            fact
        }
    }

    pub(super) fn has_owned_feature(
        &mut self,
        b: &mut Builder,
        owner: usize,
        steps: &mut usize,
    ) -> Option<bool> {
        charge(steps, 1)?;
        if let Some(&found) = self.owned_feature_witness.get(&owner) {
            return Some(found);
        }
        let relations = self.evidence.relationships(b, owner, steps)?;
        let mut found = false;
        for relation in relations {
            let member = b.elements.get(relation)?;
            if !is_a!(member, "FeatureMembership") {
                continue;
            }
            charge(steps, member.children.len())?;
            let children = member.children.to_vec();
            for child in children {
                if conforms(b.elements.get(child)?.ty, "Feature")
                    && self.evidence.owning_type(b, child, steps) == Some(Some(owner))
                {
                    found = true;
                    break;
                }
            }
            if found {
                break;
            }
        }
        charge(steps, 0)?;
        if !found && !semantic_ownership::owned_feature_projection_complete(b, owner) {
            return None;
        }
        self.owned_feature_witness.insert(owner, found);
        Some(found)
    }

    /// Select an audited evidence domain before candidate selection. A known
    /// unsupported family selects the unchanged compatibility provider; broken
    /// evidence is None and must never trigger that compatibility fallback.
    pub(super) fn audited_featuring_domain(
        &mut self,
        b: &mut Builder,
        roots: &[usize],
        steps: &mut usize,
    ) -> Option<bool> {
        if !self.current(b) {
            return None;
        }
        let semantic = b.semantically_annotated();
        fn ordinary(
            b: &Builder,
            semantic: &crate::layered::IdSet<usize>,
            e: usize,
        ) -> Option<bool> {
            if semantic.contains(&e) {
                return Some(false);
            }
            let e = b.elements.get(e)?;
            if e.ty != "Feature" {
                return Some(false);
            }
            match e.props.get("isVariable") {
                None => Some(true),
                Some(value) => value.as_bool().map(|variable| !variable),
            }
        }
        charge(steps, roots.len())?;
        for &root in roots {
            if !ordinary(b, &semantic, root)? {
                return Some(false);
            }
        }
        let mut stack = roots.to_vec();
        let mut seen = HashSet::new();
        while let Some(feature) = stack.pop() {
            charge(steps, 1)?;
            if !seen.insert(feature) {
                continue;
            }
            if !ordinary(b, &semantic, feature)? {
                return Some(false);
            }
            self.evidence.index(b, steps)?;
            if let Some(rel) = b.elements[feature].owning_relationship {
                if !conforms(b.elements.get(rel)?.ty, "FeatureMembership") {
                    if let Some(owner) = self.evidence.carrier(b, rel, steps)? {
                        if is_a!(b.elements[owner], "Feature") {
                            return Some(false);
                        }
                    }
                }
            }
            let owners = self
                .evidence
                .featuring_types(b, feature, &mut HashSet::new(), steps)?;
            for owner in owners {
                if is_a!(b.elements[owner], "Feature") {
                    stack.push(owner);
                } else if !matches!(
                    b.elements[owner].ty,
                    "Type" | "Classifier" | "Class" | "Structure" | "DataType"
                ) {
                    return Some(false);
                }
            }
            let relationships = self.evidence.relationships(b, feature, steps)?;
            for relationship in relationships {
                if is_a!(b.elements[relationship], "FeatureChaining") {
                    stack.push(endpoint(
                        b,
                        feature,
                        relationship,
                        &["featureChained"],
                        &["chainingFeature"],
                        "Feature",
                        steps,
                    )?);
                }
            }
        }
        Some(true)
    }

    pub(super) fn owning_type(
        &mut self,
        b: &mut Builder,
        feature: usize,
        steps: &mut usize,
    ) -> Option<Option<usize>> {
        if !self.current(b) {
            return None;
        }
        self.evidence.owning_type(b, feature, steps)
    }

    pub(super) fn featuring_types(
        &mut self,
        b: &mut Builder,
        feature: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        if !self.current(b) {
            return None;
        }
        self.evidence
            .featuring_types(b, feature, &mut HashSet::new(), steps)
    }

    /// The first chaining feature of a feature chain, `Some(None)` for a
    /// feature that is not a chain, `None` where the chainings are not
    /// checked.
    pub(super) fn first_chaining_feature(
        &mut self,
        b: &mut Builder,
        feature: usize,
        steps: &mut usize,
    ) -> Option<Option<usize>> {
        if !self.current(b) {
            return None;
        }
        self.evidence.first_chaining_feature(b, feature, steps)
    }

    /// Applicability and canonical obligations shared by typing and negative
    /// specialization proofs. These are required witnessed paths, never edges.
    ///
    /// The obligations mirror the planner's implied specializations
    /// (`implied.rs`, `required_implied_plan`): the generic feature role
    /// (`Base::naturals` for a multiplicity, else `Base::things`), the step
    /// and expression roles, the roles the feature's typing adds, the roles
    /// of its SysML usage kind (`implicit_usage_bases`) and of the
    /// occurrence, item and part families it conforms to, the flow,
    /// succession, invariant and binary-connector roles, and the
    /// composition roles under the planner's composite owner contexts
    /// (`composite_owner_context`). A positional feature — an end, or a
    /// parameter by direction or by membership kind — takes its positional
    /// redefinition targets from its owner's membership certificate.
    #[allow(clippy::too_many_arguments)]
    pub(super) fn feature_requirements(
        &mut self,
        b: &mut Builder,
        feature: usize,
        owned: &[usize],
        typings: &[usize],
        original: Option<usize>,
        owner_types: Option<CompositionOwner>,
        steps: &mut usize,
    ) -> Result<(Vec<usize>, Vec<usize>), FeatureRequirementsFailure> {
        use FeatureRequirementsFailure::{InvalidRelationship, Unsupported};
        if !self.current(b) || !b.dynamic_evidence_current(feature) {
            return Err(Unsupported);
        }
        self.refresh_planner_state(b, steps).ok_or(Unsupported)?;
        charge(steps, 1).ok_or(Unsupported)?;
        let structure = super::structural_index::StoredStructure::for_annotations(b, steps)
            .ok_or(InvalidRelationship)?;
        // Plain metadata adds no base; semantic metadata adds one the
        // planner does not write (KerML 9.2), so its targets stay out.
        let semantic = b.semantically_annotated();
        let e = b.elements.get(feature).ok_or(InvalidRelationship)?;
        let ty = e.ty;
        // A constructor's typing by its constructed type is on its result,
        // the dynamic family's row the static audit does not see: its bases
        // stay unaudited until the binding provider certifies them. The
        // other instantiation expressions' callee typings are the planner's
        // rows, required below.
        if !conforms(ty, "Feature")
            || conforms(ty, "ConstructorExpression")
            || original.is_some()
            || b.metadata_associations_incomplete
            || structure.annotations_incomplete
            || semantic.contains(&feature)
        {
            return Err(Unsupported);
        }
        let portion = match e.props.get("isPortion") {
            None => false,
            Some(value) => value.as_bool().ok_or(Unsupported)?,
        };
        let composite = match e.props.get("isComposite") {
            None => false,
            Some(value) => value.as_bool().ok_or(Unsupported)?,
        };
        let is_end = match e.props.get("isEnd") {
            None => false,
            Some(v) => v.as_bool().ok_or(Unsupported)?,
        };
        let directed = match e.props.get("direction") {
            None => false,
            Some(value) if value.is_null() => false,
            Some(value) => {
                if !matches!(value.as_str(), Some("in" | "out" | "inout")) {
                    return Err(Unsupported);
                }
                true
            }
        };
        // Usage redefines isVariable as a derived property. Its Boolean value
        // changes featuring, not the specialization obligations audited here.
        if e.props.get("isVariable").is_some_and(|v| {
            v.as_bool().is_none() || (!conforms(ty, "Usage") && v.as_bool() != Some(false))
        }) {
            return Err(Unsupported);
        }
        let negated = if conforms(ty, "Invariant") {
            Some(super::implied::invariant_negation(e).ok_or(Unsupported)?)
        } else {
            None
        };
        let positional = is_end || b.is_parameter(feature);
        let membership = e.owning_relationship.ok_or(Unsupported)?;
        self.evidence.index(b, steps).ok_or(InvalidRelationship)?;
        let membership_kind = b.elements[membership].ty;
        let carrier = if conforms(membership_kind, "Specialization") {
            self.specialization_owner(b, membership, steps)
                .ok_or(InvalidRelationship)?
        } else {
            self.evidence
                .carrier(b, membership, steps)
                .ok_or(InvalidRelationship)?
                .ok_or(InvalidRelationship)?
        };
        let owner_kind = b.elements.get(carrier).ok_or(InvalidRelationship)?.ty;
        let namespace = matches!(owner_kind, "Namespace" | "Package" | "LibraryPackage");
        if namespace {
            if self.evidence.owning_type(b, feature, steps) != Some(None) {
                return Err(InvalidRelationship);
            }
        } else if !conforms(membership_kind, "FeatureMembership") {
            // A feature a type owns outside a feature membership — a feature
            // value's expression, a multiplicity range and its bounds, a
            // chain a subsetting, reference or expression names, an end's
            // cross feature — is not one of the type's features: its roles
            // are the plain ones of its kind and it carries no positional
            // role. A variant is owned otherwise and stays outside.
            if !conforms(owner_kind, "Type")
                || !(matches!(
                    membership_kind,
                    "FeatureValue" | "OwningMembership" | "VariantMembership"
                ) || conforms(membership_kind, "Specialization"))
                || positional
            {
                return Err(Unsupported);
            }
            if self.evidence.owning_type(b, feature, steps) != Some(None) {
                return Err(InvalidRelationship);
            }
        } else {
            // A feature of a Type of any kind under a feature membership of
            // any kind: the plain memberships, the positional ones (end,
            // parameter, return, subject, actor, stakeholder) and the SysML
            // body memberships (state subaction, transition feature,
            // requirement constraint, objective, result expression). A
            // variant is owned otherwise and stays outside. A composite under
            // a Feature that is one of the planner's composite owner contexts
            // needs that owner's decided type facts.
            if !conforms(membership_kind, "FeatureMembership")
                || !conforms(owner_kind, "Type")
                || (membership_kind == "EndFeatureMembership" && !is_end)
            {
                return Err(Unsupported);
            }
            if composite
                && membership_kind == "FeatureMembership"
                && composite_owner_context(owner_kind)
                && is_a!(b.elements[carrier], "Feature")
                && owner_types.is_none()
            {
                return Err(Unsupported);
            }
            if self.evidence.owning_type(b, feature, steps) != Some(Some(carrier)) {
                return Err(InvalidRelationship);
            }
        }
        charge(steps, owned.len()).ok_or(Unsupported)?;
        let mut has_owned_typing = false;
        for &relationship in owned {
            let kind = b.elements.get(relationship).ok_or(InvalidRelationship)?.ty;
            has_owned_typing |= conforms(kind, "FeatureTyping");
            // A FeatureValue binds the feature's value and adds no typing or
            // specialization obligation; its expression is an owned member
            // the membership proof admits on its own terms. A chain's one
            // obligation is its last chaining feature, which the stored base
            // projection carries as the final chain target. A cross
            // subsetting is a stored base like any subsetting (the crossed
            // chain): the crossing rules constrain the cross feature, not
            // the end that crosses. A unioning, a differencing or a feature
            // inverting places no specialization on the feature that owns
            // it, and the resolver reads none of them as a base; the
            // planner plans no role for any of these.
            if kind == "Intersecting" {
                // An intersection on an end or a directed feature stays
                // outside; any other Kernel feature kind's is audited
                // against its subsettings below.
                if is_end || directed {
                    return Err(Unsupported);
                }
                if self.evidence.carrier(b, relationship, steps) != Some(Some(feature)) {
                    return Err(InvalidRelationship);
                }
                // Intersections add no new typing dependency only when every
                // target is already an exact owned Subsetting target. Never
                // synthesize missing specializations from an intersection.
                let target = endpoint(
                    b,
                    feature,
                    relationship,
                    &["typeIntersected"],
                    &["intersectingType"],
                    "Feature",
                    steps,
                )
                .ok_or(InvalidRelationship)?;
                let mut witnessed = false;
                for &candidate in owned {
                    charge(steps, 1).ok_or(Unsupported)?;
                    if is_a!(b.elements[candidate], "Subsetting")
                        && !is_a!(b.elements[candidate], "CrossSubsetting")
                        && endpoint(
                            b,
                            feature,
                            candidate,
                            &["specific", "subsettingFeature"],
                            &["general", "subsettedFeature"],
                            "Feature",
                            steps,
                        ) == Some(target)
                    {
                        witnessed = true;
                    }
                }
                if !witnessed {
                    return Err(Unsupported);
                }
            }
        }
        // This composition audit covers the occurrence usage families and
        // Kernel features (a feature, a step, an expression) with explicit
        // owned typing, which the planner's typing requirements read alike.
        // Inherited-only Kernel typing and other composite usage kinds
        // remain qualified.
        if composite
            && !conforms(ty, "OccurrenceUsage")
            && (conforms(ty, "Usage") || !has_owned_typing)
        {
            return Err(Unsupported);
        }
        charge(steps, typings.len()).ok_or(Unsupported)?;
        let (mut object, mut occurrence, mut data) = (false, false, false);
        for &target in typings {
            let target_ty = b.elements.get(target).ok_or(InvalidRelationship)?.ty;
            if !conforms(target_ty, "Classifier") {
                return Err(Unsupported);
            }
            object |= conforms(target_ty, "Structure");
            occurrence |= conforms(target_ty, "Class");
            data |= conforms(target_ty, "DataType");
        }
        let mut names: Vec<&'static str> = Vec::new();
        let generic = if conforms(ty, "Multiplicity")
            && self.required_role(b, "Base::naturals", steps).is_some()
        {
            "Base::naturals"
        } else {
            "Base::things"
        };
        names.push(generic);
        // A synthesized default multiplicity's range (the planner's
        // `default_multiplicity_role`): `exactlyOne` under a SysML usage,
        // `zeroOrOne` under an individual definition.
        if let Some(role) = b.default_multiplicity_role(feature) {
            names.push(role);
        }
        if conforms(ty, "Step") {
            names.push("Performances::performances");
        }
        if let Some(name) = super::implied::expression_implied_base(ty) {
            names.push(name);
            names.push("Performances::evaluations");
        }
        if let Some(name) = super::implied::additional_expression_base(ty) {
            names.push(name);
        }
        if conforms(ty, "Expression") && super::implied::is_transition_guard(b, feature) {
            names.push(super::implied::TRANSITION_GUARD);
        }
        // The roles a feature's own typing adds are planned on the canonical
        // graph format only (`owned_typing_requirements`); the roles of the
        // usage families below hold on both.
        if b.graph_format == crate::model::GraphFormat::CanonicalV3 {
            if object {
                names.push("Objects::objects");
            }
            if occurrence {
                names.push("Occurrences::occurrences");
            }
            if data {
                names.push("Base::dataValues");
            }
        }
        if conforms(ty, "OccurrenceUsage") {
            names.push("Occurrences::occurrences");
        }
        if conforms(ty, "ItemUsage") {
            names.push("Items::items");
        }
        if conforms(ty, "PartUsage") {
            names.push("Parts::parts");
        }
        // Kernel Flow and Succession are not SysML usages; their bases follow.
        // A usage's kind roles and owner roles come from the planner's one
        // list (`implied::usage_roles`); a usage a namespace owns has kind
        // roles alone.
        if usage_kind_of(ty, Dialect::Sysml)
            .filter(|_| !matches!(ty, "Flow" | "SuccessionFlow"))
            .is_some()
        {
            let owner = (!namespace).then_some((membership, carrier));
            b.ensure_ids();
            names.extend(super::implied::usage_roles(b, feature, owner));
            names.extend(super::implied::usage_redefinition_roles(b, feature, owner));
        }
        let owns_end = (conforms(ty, "Flow") || conforms(ty, "FlowUsage"))
            && b.owned_member_elems(feature, true).into_iter().any(|end| {
                b.elements[end].props.get("isEnd").and_then(|v| v.as_bool()) == Some(true)
            });
        if conforms(ty, "Flow") {
            names.push("Transfers::transfers");
            if owns_end {
                names.push("Transfers::flowTransfers");
            }
        }
        if conforms(ty, "FlowUsage") && owns_end {
            names.push("Flows::flows");
        }
        if conforms(ty, "SuccessionFlow") {
            names.push("Transfers::flowTransfersBefore");
        }
        if conforms(ty, "Succession") {
            names.push("Occurrences::happensBeforeLinks");
        }
        if let Some(negated) = negated {
            names.push(super::implied::invariant_implied_base(negated));
            if conforms(ty, "AssertConstraintUsage") {
                names.push(super::implied::assertion_implied_base(negated));
            }
            if conforms(ty, "SatisfyRequirementUsage") {
                names.push(super::implied::satisfaction_implied_base(negated));
            }
        }
        if let Some((base, false)) = b.binary_owned_base(feature) {
            names.push(base);
        }
        charge(steps, names.len()).ok_or(Unsupported)?;
        let mut required = Vec::with_capacity(names.len());
        let mut seen = HashSet::new();
        for name in names {
            if seen.insert(name) {
                required.push(self.required_role(b, name, steps).ok_or(Unsupported)?);
            }
        }
        // A variant specializes the variation it belongs to (a typing by
        // the variation definition, a subsetting of the variation usage),
        // which the planner plans unless it is written.
        if membership_kind == "VariantMembership" {
            required.push(carrier);
        }
        // Semantic metadata's base (KerML 9.2): the planner's row.
        for target in b.semantic_base_targets(feature, 0) {
            charge(steps, 1).ok_or(Unsupported)?;
            required.push(target);
        }
        // An instantiation expression's callee (KerML 8.3.4.8): the
        // planner's row; an expression whose callee does not resolve stays
        // out.
        let mut required_types = Vec::new();
        if conforms(ty, "InstantiationExpression") {
            charge(steps, 2).ok_or(Unsupported)?;
            let names = b.implied_names();
            let callee = b.instantiation_callee(feature, &names).ok_or(Unsupported)?;
            if is_a!(b.elements[callee], "Feature") {
                required.push(callee);
            } else {
                required_types.push(callee);
            }
        }
        if (composite || portion)
            && membership_kind == "FeatureMembership"
            && composite_owner_context(owner_kind)
        {
            for name in composite_roles(
                ty,
                owner_kind,
                object,
                occurrence,
                composite,
                portion,
                owner_types.unwrap_or_default(),
            ) {
                let role = self.required_role(b, name, steps).ok_or(Unsupported)?;
                // The library's own `portions` is the root of its role.
                if role != feature {
                    required.push(role);
                }
            }
        }
        if positional && !namespace {
            // This is the same complete Membership/positional certificate used
            // by Type.feature. Its generated targets are required witnesses in
            // the shared semantic graph, never a second set of implicit edges.
            let mut sequence = b
                .checked_type_memberships(carrier, steps)
                .map_err(|_| Unsupported)?;
            charge(steps, sequence.owned.len()).ok_or(Unsupported)?;
            if !sequence.owned.iter().any(|m| {
                m.member == feature && is_a!(b.elements[m.relationship], "FeatureMembership")
            }) {
                return Err(InvalidRelationship);
            }
            if is_end {
                // An ordinary end with an owned crossing Feature activates
                // separate crossing obligations. Do not certify their absence
                // from a flag.
                let domains = structure.membership_domains(b, steps).ok_or(Unsupported)?;
                if !domains.owner_complete(feature) {
                    return Err(InvalidRelationship);
                }
                for &relationship in owned {
                    charge(steps, 1).ok_or(Unsupported)?;
                    let kind = b.elements[relationship].ty;
                    if conforms(kind, "OwningMembership") && !conforms(kind, "FeatureMembership") {
                        let member = super::membership_evidence::member(
                            b,
                            &structure,
                            feature,
                            relationship,
                            steps,
                        )
                        .ok_or(InvalidRelationship)?;
                        let kind = b.elements[member].ty;
                        if conforms(kind, "Feature")
                            && !conforms(kind, "Multiplicity")
                            && !conforms(kind, "MetadataFeature")
                        {
                            return Err(Unsupported);
                        }
                    }
                }
            }
            if let Some(targets) = sequence.required_positional.remove(&feature) {
                charge(steps, targets.len()).ok_or(Unsupported)?;
                required.extend(targets);
            }
        }
        let anything = self
            .required_role(b, "Base::Anything", steps)
            .ok_or(Unsupported)?;
        required_types.push(anything);
        Ok((required, required_types))
    }

    // Audited family obligations for complete negative specialization paths.
    // Verify inherited family requirements, rather than assuming a partial
    // replacement library supplies its own ancestor heritage correctly. These
    // targets are obligations to prove through the shared graph, not new edges.
    fn required_bases(
        &mut self,
        b: &mut Builder,
        specific: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        let element = b.elements.get(specific)?;
        if conforms(element.ty, "Feature") {
            let owned = self.evidence.relationships(b, specific, steps)?;
            let mut typings = Vec::new();
            for &relation in &owned {
                charge(steps, 1)?;
                if conforms(b.elements.get(relation)?.ty, "FeatureTyping") {
                    typings.push(endpoint(
                        b,
                        specific,
                        relation,
                        &["typedFeature", "specific"],
                        &["type", "general"],
                        "Type",
                        steps,
                    )?);
                }
            }
            let owner_types = self.composition_owner(b, specific, steps)?;
            let (mut feature_bases, type_bases) = self
                .feature_requirements(b, specific, &owned, &typings, None, owner_types, steps)
                .ok()?;
            feature_bases.extend(type_bases);
            return Some(feature_bases);
        }
        // An individual definition is a Life (the planner plans it); a
        // variation adds no base of its own (its variants specialize it).
        let individual = is_a!(element, "Definition") && super::implied::is_individual(element);
        let names = definition_chain(element.ty)?;
        charge(steps, names.len())?;
        let mut required = names
            .iter()
            .map(|name| self.required_role(b, name, steps))
            .collect::<Option<Vec<_>>>()?;
        if individual {
            required.push(self.required_role(b, super::implied::INDIVIDUAL_BASE, steps)?);
        }
        // Semantic metadata's base (KerML 9.2): the planner's row — a
        // feature base stands for its declared types on a classifier.
        for target in b.semantic_base_targets(specific, 0) {
            charge(steps, 1)?;
            if is_a!(b.elements[target], "Feature") {
                let types = b.direct_typing_elems(target);
                charge(steps, types.len())?;
                required.extend(
                    types
                        .into_iter()
                        .filter(|&ty| is_a!(b.elements[ty], "Classifier")),
                );
            } else {
                required.push(target);
            }
        }
        // A connection or interface definition with two owned ends is binary
        // (the planner counts the owned ends the same way).
        if let Some((base, true)) = b.binary_owned_base(specific) {
            required.push(self.required_role(b, base, steps)?);
        }
        Some(required)
    }

    /// The owner of an element a Specialization owns (the chain a subsetting,
    /// redefinition, typing or reference names): the specialization's owning
    /// related element, which must own the specialization in turn.
    fn specialization_owner(
        &mut self,
        b: &mut Builder,
        relationship: usize,
        steps: &mut usize,
    ) -> Option<usize> {
        charge(steps, 1)?;
        self.evidence.index(b, steps)?;
        if !self.evidence.ids_unique {
            return None;
        }
        let relation = b.elements.get(relationship)?;
        if !conforms(relation.ty, "Specialization") {
            return None;
        }
        // The owning related element where the row spells it, else the
        // specialization's source end: an owned specialization's owner.
        let mut id = relation
            .props
            .get("owningRelatedElement")
            .and_then(|value| value.as_reference());
        if id.is_none() {
            for key in [
                "specific",
                "subsettingFeature",
                "redefiningFeature",
                "referencingFeature",
                "typedFeature",
                "subclassifier",
            ] {
                if let Some(value) = relation
                    .props
                    .get(key)
                    .and_then(|value| value.as_reference())
                {
                    id = Some(value);
                    break;
                }
            }
        }
        let owner = b.element_index_of_uuid(id?)?;
        let rows = self.evidence.relationships(b, owner, steps)?;
        rows.contains(&relationship).then_some(owner)
    }

    /// The body scope whose provider certifies an element's implied bases:
    /// its own, or for an element the lowering gives no scope of its own (a
    /// multiplicity range, a literal or other expression, the chain a
    /// subsetting or reference names) the nearest enclosing one, reached
    /// through the checked owners.
    fn provider_scope(
        &mut self,
        b: &mut Builder,
        element: usize,
        steps: &mut usize,
    ) -> Option<usize> {
        let mut current = element;
        for _ in 0..=super::MAX_RESOLUTION_DEPTH {
            charge(steps, 1)?;
            if let Some(&scope) = b.elem_scope.get(&current) {
                return Some(scope);
            }
            let relationship = b.elements.get(current)?.owning_relationship?;
            current = if conforms(b.elements[relationship].ty, "Specialization") {
                self.specialization_owner(b, relationship, steps)?
            } else {
                self.evidence.index(b, steps)?;
                self.evidence.carrier(b, relationship, steps)??
            };
        }
        None
    }

    /// The composition-owner facts of a composite occurrence usage owned by
    /// a Feature, for the conditional composition roles: whether the owner
    /// decidedly specializes the library's object and occurrence classes,
    /// through the same shared proof the roles are later verified by. Not
    /// a composite under a Feature: no facts are needed. An undecided owner
    /// leaves the usage's bases incomplete rather than guessing a role away.
    fn composition_owner(
        &mut self,
        b: &mut Builder,
        feature: usize,
        steps: &mut usize,
    ) -> Option<Option<CompositionOwner>> {
        let element = b.elements.get(feature)?;
        if !is_a!(element, "OccurrenceUsage")
            || element.props.get("isComposite").and_then(|v| v.as_bool()) != Some(true)
        {
            return Some(None);
        }
        let Some(owner) = self
            .evidence
            .owning_type(b, feature, steps)?
            .filter(|&owner| is_a!(b.elements[owner], "Feature"))
        else {
            return Some(None);
        };
        charge(steps, 2)?;
        let mut facts = CompositionOwner::default();
        for (name, fact) in [
            ("Objects::Object", &mut facts.object),
            ("Occurrences::Occurrence", &mut facts.occurrence),
        ] {
            let role = self.required_role(b, name, steps)?;
            *fact = match self.specializes(b, owner, role, steps) {
                RelationFact::Yes => true,
                RelationFact::No => false,
                RelationFact::Unknown => return None,
            };
        }
        Some(Some(facts))
    }

    /// Resolve a canonical loaded library role under the same bounded identity
    /// authority used by required specialization-family certificates.
    pub(super) fn library_role(
        &mut self,
        b: &mut Builder,
        name: &'static str,
        steps: &mut usize,
    ) -> Option<usize> {
        if !self.current(b) {
            return None;
        }
        self.refresh_planner_state(b, steps)?;
        self.evidence.index(b, steps)?;
        if !self.evidence.ids_unique {
            return None;
        }
        self.required_role(b, name, steps)
    }

    fn required_role(
        &mut self,
        b: &mut Builder,
        name: &'static str,
        steps: &mut usize,
    ) -> Option<usize> {
        charge(steps, 1)?;
        if self.required_library.is_none() {
            charge(steps, b.lib_qnames.len())?;
            let mut by_last: HashMap<&'static str, Vec<(&'static str, &'static str)>> =
                HashMap::new();
            for &(role, kind) in ROLE_KINDS {
                let last = role.rsplit("::").next().expect("a qualified role name");
                by_last.entry(last).or_default().push((role, kind));
            }
            let mut ids: HashMap<&'static str, Option<uuid::Uuid>> = HashMap::new();
            for (id, segments) in b.lib_qnames.iter() {
                let Some(candidates) = segments.last().and_then(|last| by_last.get(last.as_str()))
                else {
                    continue;
                };
                for &(role, _) in candidates {
                    let mut parts = role.split("::");
                    let matched = segments.iter().all(|s| parts.next() == Some(s.as_str()))
                        && parts.next().is_none();
                    if !matched {
                        continue;
                    }
                    ids.entry(role)
                        .and_modify(|known| {
                            if *known != Some(*id) {
                                *known = None;
                            }
                        })
                        .or_insert(Some(*id));
                }
            }
            let mut resolved = HashMap::new();
            for &(role, kind) in ROLE_KINDS {
                let target = ids
                    .get(role)
                    .copied()
                    .flatten()
                    .and_then(|id| b.element_index_of_uuid(id))
                    .filter(|&e| e < b.lib_boundary && b.elements[e].conforms(kind));
                resolved.insert(role, target);
            }
            self.required_library = Some(resolved);
        }
        self.required_library.as_ref()?.get(name).copied().flatten()
    }

    fn walk(
        &mut self,
        b: &mut Builder,
        specific: usize,
        general: usize,
        depth: usize,
        active: &mut HashSet<usize>,
        steps: &mut usize,
    ) -> RelationFact {
        if charge(steps, 1).is_none()
            || depth > super::MAX_RESOLUTION_DEPTH
            || !b.elements.get(specific).is_some_and(|e| is_a!(e, "Type"))
            || !b.elements.get(general).is_some_and(|e| is_a!(e, "Type"))
        {
            return RelationFact::Unknown;
        }
        if specific == general {
            return RelationFact::Yes;
        }
        if let Some(&known) = self.known.get(&(specific, general, depth)) {
            return if known {
                RelationFact::Yes
            } else {
                RelationFact::No
            };
        }
        if !active.insert(specific) {
            return RelationFact::Unknown;
        }
        let fact = match self.direct_bases(b, specific, steps) {
            None => RelationFact::Unknown,
            Some(bases) => {
                let mut complete = bases.complete;
                let mut positive = false;
                for target in bases.targets {
                    match self.walk(b, target, general, depth + 1, active, steps) {
                        RelationFact::Yes => {
                            positive = true;
                            break;
                        }
                        RelationFact::Unknown => complete = false,
                        RelationFact::No => {}
                    }
                }
                if positive {
                    RelationFact::Yes
                } else if complete {
                    RelationFact::No
                } else {
                    RelationFact::Unknown
                }
            }
        };
        active.remove(&specific);
        if let RelationFact::Yes | RelationFact::No = fact {
            self.known
                .insert((specific, general, depth), fact == RelationFact::Yes);
        }
        fact
    }

    /// The direct stored reader shared by exact explicit-only operations and
    /// qualified specialization evidence. No implied provider is invoked here.
    fn stored_base_projection(
        &mut self,
        b: &mut Builder,
        specific: usize,
        exclude_implied: bool,
        steps: &mut usize,
    ) -> Option<StoredBases> {
        if !self.current(b) || !b.dynamic_evidence_current(specific) {
            return None;
        }
        self.refresh_planner_state(b, steps)?;
        charge(steps, 1)?;
        if !conforms(b.elements.get(specific)?.ty, "Type") {
            return None;
        }
        if b.id_index.is_none() || b.id_index_built_for != b.elements.len() {
            charge(steps, b.elements.len())?;
        }
        self.evidence.index(b, steps)?;
        if self.evidence.incomplete()
            || self.evidence.bad_bases.contains(&specific)
            || self.evidence.bad_chains.contains(&specific)
        {
            return None;
        }
        let relationships = self.evidence.relationships(b, specific, steps)?;
        let mut unique = HashSet::new();
        if relationships
            .iter()
            .any(|&r| !unique.insert(r) || b.elements.get(r).is_none())
        {
            return None;
        }
        for &relationship in &relationships {
            if self.evidence.carrier(b, relationship, steps)? != Some(specific) {
                return None;
            }
        }
        let conjugations: Vec<_> = relationships
            .iter()
            .copied()
            .filter(|&r| is_a!(b.elements[r], "Conjugation"))
            .collect();
        let mut targets = Vec::new();
        let mut target_set = HashSet::new();
        let mut complete = true;
        let mut duplicate_targets = false;
        let mut final_chain = None;
        let mut feature_chain_complete = true;
        if b.elements[specific]
            .props
            .get("isConjugated")
            .is_some_and(|value| value.as_bool() != Some(!conjugations.is_empty()))
        {
            return None;
        }
        let conjugated = !conjugations.is_empty();
        if conjugated {
            self.owned_conjugation(b, specific, steps)??;
            // Conjugation replaces ordinary owned specializations, even if
            // they appear earlier in declaration order.
            if conjugations.len() != 1 {
                return None;
            }
            let target = endpoint(
                b,
                specific,
                conjugations[0],
                &["conjugatedType"],
                &["originalType"],
                "Type",
                steps,
            )?;
            target_set.insert(target);
            targets.push(target);
        } else {
            for &r in &relationships {
                if !is_a!(b.elements[r], "Specialization") {
                    continue;
                }
                let relation = &b.elements[r];
                if let (true, Some(value)) = (exclude_implied, relation.props.get("isImplied")) {
                    match value.as_bool() {
                        Some(true) => continue,
                        Some(false) => {}
                        None => {
                            complete = false;
                            continue;
                        }
                    }
                }
                // Keep independent old result Subsetting witnesses usable, but
                // never traverse a stale optional result Redefinition row.
                if !b.result_redefinition_row_current(r) || !b.static_chain_row_current(r) {
                    complete = false;
                    continue;
                }
                let (source_kind, target_kind) = if is_a!(relation, "Subsetting") {
                    ("Feature", "Feature")
                } else if is_a!(relation, "FeatureTyping") {
                    ("Feature", "Type")
                } else if is_a!(relation, "Subclassification") {
                    ("Classifier", "Classifier")
                } else {
                    ("Type", "Type")
                };
                let target = conforms(b.elements[specific].ty, source_kind)
                    .then(|| {
                        endpoint(
                            b,
                            specific,
                            r,
                            &[
                                "specific",
                                "subclassifier",
                                "typedFeature",
                                "subsettingFeature",
                                "redefiningFeature",
                                "referencingFeature",
                                "crossingFeature",
                            ],
                            &[
                                "general",
                                "superclassifier",
                                "type",
                                "subsettedFeature",
                                "redefinedFeature",
                                "referencedFeature",
                                "crossedFeature",
                            ],
                            target_kind,
                            steps,
                        )
                    })
                    .flatten();
                match target {
                    Some(target) if target_set.insert(target) => targets.push(target),
                    Some(_) => duplicate_targets = true,
                    None => complete = false,
                }
            }
        }
        // Feature::supertypes appends the final chaining feature to the Type
        // result. Do not let a missing link masquerade as an unchained feature.
        if is_a!(b.elements[specific], "Feature") {
            let raw = super::structural_index::StoredStructure::for_query(b, steps)?;
            match checked_feature_target(b, &raw, specific, &relationships, b.elements.len(), steps)
            {
                Some(last) => {
                    if let Some(target) = last.filter(|&target| target != specific) {
                        final_chain = Some(target);
                        duplicate_targets |= target_set.contains(&target);
                    }
                }
                None => feature_chain_complete = false,
            }
        }

        charge(steps, 0)?;
        Some(StoredBases {
            targets,
            target_set,
            complete,
            conjugated,
            final_chain,
            duplicate_targets,
            feature_chain_complete,
        })
    }

    /// Checked direct supertypes. The conjugated Type branch ignores the
    /// argument; ordinary false requires implied-family evidence not provided
    /// here. Feature still appends its complete, one-hop featureTarget.
    pub(super) fn checked_supertypes(
        &mut self,
        b: &mut Builder,
        specific: usize,
        exclude_implied: bool,
        steps: &mut usize,
    ) -> Result<Vec<usize>, SupertypesFailure> {
        // Filtering ordinary Specializations is immaterial for conjugation.
        // Using the explicit projection avoids interpreting unaudited implied
        // families even when a nonconjugated false request is rejected below.
        let mut projection = self
            .stored_base_projection(b, specific, true, steps)
            .ok_or(SupertypesFailure::Incomplete)?;
        if !projection.complete
            || !projection.feature_chain_complete
            || projection.duplicate_targets
        {
            return Err(SupertypesFailure::Incomplete);
        }
        if !exclude_implied && !projection.conjugated {
            return Err(SupertypesFailure::UnsupportedConfiguration);
        }
        if let Some(target) = projection.final_chain {
            projection.targets.push(target);
        }
        charge(steps, projection.targets.len()).ok_or(SupertypesFailure::Incomplete)?;
        Ok(projection.targets)
    }

    #[cfg(test)]
    fn explicit_supertypes(
        &mut self,
        b: &mut Builder,
        specific: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        self.checked_supertypes(b, specific, true, steps).ok()
    }

    /// Complete ordered bases from the shared current-row/provider authority.
    /// A partial positive path is not a certificate of absent additional bases.
    pub(super) fn complete_direct_bases(
        &mut self,
        b: &mut Builder,
        specific: usize,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        let bases = self.direct_bases(b, specific, steps)?;
        bases.complete.then_some(bases.targets)
    }

    fn direct_bases(
        &mut self,
        b: &mut Builder,
        specific: usize,
        steps: &mut usize,
    ) -> Option<Bases> {
        if !self.current(b) || !b.dynamic_evidence_current(specific) {
            return None;
        }
        self.refresh_planner_state(b, steps)?;
        charge(steps, 1)?;
        if let Some(bases) = self.bases.get(&specific) {
            charge(steps, bases.targets.len())?;
            return Some(bases.clone());
        }
        let projection = self.stored_base_projection(b, specific, false, steps)?;
        let mut targets = projection.targets;
        let mut target_set = projection.target_set;
        let mut complete = projection.complete;
        let mut required = Vec::new();
        if !projection.conjugated {
            // The provider establishes the supported implied/positional base
            // evidence and preserves caller lookup state. An incomplete
            // provider does not invalidate an already proven explicit path.
            let provider = self
                .provider_scope(b, specific, steps)
                .is_some_and(|scope| self.providers.scope(b, scope, steps));
            if provider && complete {
                match b.value_context_bases(specific, steps) {
                    Some(bases) => {
                        for target in bases {
                            charge(steps, 1)?;
                            if target_set.insert(target) {
                                targets.push(target);
                            }
                        }
                    }
                    None => complete = false,
                }
            } else {
                complete = false;
            }
            match self.required_bases(b, specific, steps) {
                Some(targets) => required = targets,
                None => complete = false,
            }
        }
        if let Some(target) = projection.final_chain {
            if target_set.insert(target) {
                targets.push(target);
            }
        }
        complete &= projection.feature_chain_complete;
        charge(steps, targets.len())?;
        self.refresh_planner_state(b, steps)?;
        // Publish only a provisional nonnegative row while verifying required
        // paths through the same stored/shared graph. Never invent a second
        // set of implicit edges here.
        self.bases.insert(
            specific,
            Bases {
                targets: targets.clone(),
                complete: false,
            },
        );
        if complete {
            for target in required {
                if self.walk(b, specific, target, 0, &mut HashSet::new(), steps)
                    != RelationFact::Yes
                {
                    complete = false;
                    break;
                }
            }
        }
        if *steps > crate::eval::MAX_STEPS {
            self.bases.remove(&specific);
            return None;
        }
        let bases = Bases { targets, complete };
        if complete {
            self.bases.insert(specific, bases.clone());
        } else {
            // Missing cold provider evidence can become available on retry.
            self.bases.remove(&specific);
        }
        Some(bases)
    }
}

pub(super) fn endpoint(
    b: &mut Builder,
    source: usize,
    relationship: usize,
    source_keys: &[&str],
    target_keys: &[&str],
    target_kind: &str,
    steps: &mut usize,
) -> Option<usize> {
    endpoint_with_carrier(
        b,
        source,
        Some(source),
        relationship,
        source_keys,
        target_keys,
        target_kind,
        steps,
    )
}

/// Typed endpoint identity and relationship carrier are distinct for inverse
/// FeatureTyping/Subsetting. The caller admits carrier cardinality using the
/// shared structural/semantic ownership view before invoking this validator.
#[allow(clippy::too_many_arguments)] // Source identity and carrier are independent roles.
pub(super) fn endpoint_with_carrier(
    b: &mut Builder,
    source: usize,
    carrier: Option<usize>,
    relationship: usize,
    source_keys: &[&str],
    target_keys: &[&str],
    target_kind: &str,
    steps: &mut usize,
) -> Option<usize> {
    let target = endpoint_id(b, source, carrier, relationship, source_keys, target_keys)?;
    let target = b.element_index_of_uuid(target)?;
    checked_endpoint_target(b, source, relationship, target, target_kind, steps)
}

/// Shared typed alias reader; endpoint identity lookup is supplied by the caller.
fn endpoint_id(
    b: &Builder,
    source: usize,
    carrier: Option<usize>,
    relationship: usize,
    source_keys: &[&str],
    target_keys: &[&str],
) -> Option<uuid::Uuid> {
    let relation = b.elements.get(relationship)?;
    let source_id = b.elements.get(source)?.id;
    if relation
        .props
        .get("owningRelatedElement")
        .is_some_and(|value| {
            value.as_reference() != carrier.and_then(|owner| b.elements.get(owner).map(|e| e.id))
        })
    {
        return None;
    }
    for &key in source_keys {
        if relation
            .props
            .get(key)
            .is_some_and(|v| v.as_reference() != Some(source_id))
        {
            return None;
        }
    }
    let mut target = None;
    for &key in target_keys {
        if let Some(value) = relation.props.get(key) {
            let id = value.as_reference()?;
            if target.is_some_and(|previous| previous != id) {
                return None;
            }
            target = Some(id);
        }
    }
    target
}

fn checked_endpoint_target(
    b: &Builder,
    source: usize,
    relationship: usize,
    target: usize,
    target_kind: &str,
    steps: &mut usize,
) -> Option<usize> {
    if !conforms(b.elements.get(target)?.ty, target_kind) {
        return None;
    }
    validate_relationship_arrays(b, relationship, source, target, steps)?;
    Some(target)
}

/// Project the owned TypeFeaturing source without inventing a compact property.
/// Explicit source identity and the carrier are distinct for standalone rows.
/// Present aliases must agree; only genuine absence permits carrier fallback.
pub(super) fn type_featuring_source(
    b: &mut Builder,
    relationship: usize,
    steps: &mut usize,
) -> Option<uuid::Uuid> {
    charge(steps, 1)?;
    if b.positional_planning || b.elements.get(relationship)?.ty != "TypeFeaturing" {
        return None;
    }
    let raw = super::structural_index::StoredStructure::for_query(b, steps)?;
    let carrier = semantic_ownership::checked_relationship_carrier(b, &raw, relationship, steps)?;
    let side = |typed: &str, generic: &str, steps: &mut usize| -> Option<Option<uuid::Uuid>> {
        charge(steps, 2)?;
        let relation = &b.elements[relationship];
        let mut value = match relation.props.get(typed) {
            Some(value) => Some(value.as_reference()?),
            None => None,
        };
        if let Some(array) = relation.props.get(generic) {
            let array = array.as_array()?;
            charge(steps, array.len())?;
            if array.len() != 1 {
                return None;
            }
            let id = array[0].as_reference()?;
            if value.is_some_and(|value| value != id) {
                return None;
            }
            value = Some(id);
        }
        Some(value)
    };
    let source = side("featureOfType", "source", steps)?
        .or_else(|| carrier.map(|owner| b.elements[owner].id))?;
    charge(steps, 1)?;
    // Preserve explicit external UUIDs, as ordinary checked owned properties
    // do. A carrier fallback always names a known local Feature.
    if let Some(index) = raw.element_for_uuid(b, source) {
        if !is_a!(b.elements[index], "Feature") {
            return None;
        }
    }
    if let Some(value) = b.elements[relationship].props.get("owningFeatureOfType") {
        charge(steps, 1)?;
        let owner = carrier
            .filter(|&owner| b.elements[owner].id == source && is_a!(b.elements[owner], "Feature"));
        if match owner {
            Some(owner) => value.as_reference() != Some(b.elements[owner].id),
            None => !value.is_null(),
        } {
            return None;
        }
    }
    validate_single_relationship_end(b, relationship, "source", source, steps)?;
    // Reading the source does not require resolving the unrelated target. The
    // generic ordered endpoints may nevertheless not contradict this source.
    // Only the first position is read: target multiplicity belongs to its own
    // checked property, and no tail scan or copy is needed for source identity.
    if let Some(value) = b.elements[relationship].props.get("relatedElement") {
        let values = value.as_array()?;
        charge(steps, 1)?;
        if values.first().and_then(|value| value.as_reference()) != Some(source) {
            return None;
        }
    }
    Some(source)
}

fn validate_single_relationship_end(
    b: &Builder,
    relationship: usize,
    key: &str,
    expected: uuid::Uuid,
    steps: &mut usize,
) -> Option<()> {
    if let Some(value) = b.elements.get(relationship)?.props.get(key) {
        let values = value.as_array()?;
        charge(steps, values.len())?;
        if values.len() != 1 || values[0].as_reference() != Some(expected) {
            return None;
        }
    }
    Some(())
}

/// Derived one-hop bases retained by the common static planner. This is an
/// input certificate inside that authority, not a separate semantic cache.
#[derive(Default)]
pub(super) struct FeatureChainBases {
    pub(super) targets: HashMap<usize, usize>,
    pub(super) incomplete: HashSet<usize>,
}

impl Builder {
    pub(super) fn checked_chain_bases(
        &mut self,
        boundary: usize,
        steps: Option<&mut usize>,
    ) -> Option<std::sync::Arc<FeatureChainBases>> {
        let chained = self
            .elements
            .iter()
            .take(boundary)
            .any(|e| is_a!(e, "FeatureChaining"));
        self.checked_chain_bases_from(0, boundary, chained, steps)
    }

    /// [`Self::checked_chain_bases`] of the features from row `start` on, for
    /// rows below `boundary` that hold a chaining exactly when `chained` does:
    /// a build extending a prepared library's plans reads the library's own
    /// features' chain bases from them.
    pub(super) fn checked_chain_bases_from(
        &mut self,
        start: usize,
        boundary: usize,
        chained: bool,
        mut steps: Option<&mut usize>,
    ) -> Option<std::sync::Arc<FeatureChainBases>> {
        fn budget(steps: &mut Option<&mut usize>, amount: usize) -> Option<()> {
            if let Some(steps) = steps {
                charge(steps, amount)?;
            }
            Some(())
        }
        let mut result = FeatureChainBases::default();
        if !chained {
            // The one pass over the rows found no chaining: it is the work.
            budget(&mut steps, boundary.saturating_sub(start))?;
            return Some(std::sync::Arc::new(result));
        }
        // With chainings the loop below charges the pass, a row at a time.
        let mut local = 0;
        let raw = super::structural_index::StoredStructure::for_query(
            self,
            steps.as_deref_mut().unwrap_or(&mut local),
        );
        let Some(raw) = raw else {
            if steps.is_some() {
                return None;
            }
            // The legacy unbounded planner must not panic when its bounded
            // identity reader cannot certify an unusually large/malformed graph.
            // Preserve qualification for every potentially affected Feature.
            for feature in start..boundary {
                if is_a!(self.elements[feature], "Feature") {
                    result.incomplete.insert(feature);
                }
            }
            return Some(std::sync::Arc::new(result));
        };
        for feature in start..boundary {
            budget(&mut steps, 1)?;
            if !is_a!(self.elements[feature], "Feature") {
                continue;
            }
            let relationships = &self.elements[feature].owned_relationships;
            budget(&mut steps, relationships.len())?;
            if raw.incomplete() {
                result.incomplete.insert(feature);
                continue;
            }
            if !raw.bad_chains.contains(&feature)
                && !relationships.iter().any(|&r| {
                    self.elements
                        .get(r)
                        .is_none_or(|e| is_a!(e, "FeatureChaining"))
                })
            {
                continue;
            }
            local = 0;
            match checked_feature_target(
                self,
                &raw,
                feature,
                relationships,
                boundary,
                steps.as_deref_mut().unwrap_or(&mut local),
            ) {
                Some(Some(target)) if target != feature => {
                    result.targets.insert(feature, target);
                }
                Some(_) => {}
                None => {
                    result.incomplete.insert(feature);
                }
            }
            budget(&mut steps, 0)?;
        }
        Some(std::sync::Arc::new(result))
    }
}

/// Checked one-hop Feature::featureTarget input. The caller supplies its complete
/// stored or semantic owned-relationship projection. Every chaining endpoint is
/// validated even though only the last contributes a base. No recursive flattening
/// or fabricated Specialization relationship is performed here.
pub(super) fn checked_feature_target(
    b: &Builder,
    raw: &super::structural_index::StoredStructure,
    feature: usize,
    relationships: &[usize],
    endpoint_boundary: usize,
    steps: &mut usize,
) -> Option<Option<usize>> {
    charge(steps, 1)?;
    if !raw.ids_unique
        || !raw.is_current(b)
        || raw.bad_chains.contains(&feature)
        || !conforms(b.elements.get(feature)?.ty, "Feature")
    {
        return None;
    }
    charge(steps, relationships.len())?;
    let mut seen = HashSet::new();
    let mut last = None;
    for &relationship in relationships {
        if !seen.insert(relationship) {
            return None;
        }
        let relation = b.elements.get(relationship)?;
        if !is_a!(relation, "FeatureChaining") {
            continue;
        }
        if relationship >= endpoint_boundary
            || semantic_ownership::checked_relationship_carrier(b, raw, relationship, steps)?
                != Some(feature)
        {
            return None;
        }
        let id = endpoint_id(
            b,
            feature,
            Some(feature),
            relationship,
            &["featureChained"],
            &["chainingFeature"],
        )?;
        let target = raw.element_for_uuid(b, id)?;
        let target = checked_endpoint_target(b, feature, relationship, target, "Feature", steps)?;
        if target >= endpoint_boundary {
            return None;
        }
        last = Some(target);
    }
    Some(last)
}

/// Redundant generic Relationship ends must agree with the typed endpoints.
/// The actual owning element is deliberately separate from `source`: a valid
/// standalone TypeFeaturing can be carried by a package while featuring a
/// Feature declared elsewhere. relatedElement is a non-unique Sequence.
pub(super) fn validate_relationship_arrays(
    b: &Builder,
    relationship: usize,
    source: usize,
    target: usize,
    steps: &mut usize,
) -> Option<()> {
    charge(steps, 1)?;
    let relation = b.elements.get(relationship)?;
    let source = b.elements.get(source)?.id;
    let target = b.elements.get(target)?.id;
    for (key, expected) in [("source", source), ("target", target)] {
        validate_single_relationship_end(b, relationship, key, expected, steps)?;
    }
    if let Some(value) = relation.props.get("relatedElement") {
        let values = value.as_array()?;
        charge(steps, values.len())?;
        if values.len() != 2
            || values[0].as_reference() != Some(source)
            || values[1].as_reference() != Some(target)
        {
            return None;
        }
    }
    charge(steps, relation.children.len())?;
    let mut owned = HashSet::new();
    for &child in &relation.children {
        if !owned.insert(child) {
            return None;
        }
        let child = b.elements.get(child)?;
        if child.owning_relationship != Some(relationship)
            || (child.id != source && child.id != target)
        {
            return None;
        }
    }
    if let Some(value) = relation.props.get("ownedRelatedElement") {
        let values = value.as_array()?;
        charge(steps, values.len())?;
        if values.len() != relation.children.len()
            || values
                .iter()
                .zip(relation.children.iter())
                .any(|(value, &child)| value.as_reference() != Some(b.elements[child].id))
        {
            return None;
        }
    }
    Some(())
}

#[cfg(test)]
mod tests {
    #[test]
    fn held_positive_refuses_replaced_retained_plan_with_identical_boolean_state() {
        let mut model = crate::model::Model::new();
        model.add_library_source(
            "roles.kerml",
            "standard library package Occurrences {class Occurrence;}",
        );
        model.add_source("name-generation.kerml", "class C;");
        let mut r = crate::json::ResolvedModel::build(&model);
        let c = r.resolve_qualified("C").unwrap().0;
        let occurrence = r.resolve_qualified("Occurrences::Occurrence").unwrap().0;
        let mut proof = TypeRelations::default();
        assert_eq!(
            proof.specializes(&mut r.b, c, occurrence, &mut 0),
            RelationFact::Yes
        );
        let state = proof.planner_state;
        let retained = proof.retained_plan.clone().unwrap();
        let rows = r.b.elements.len();
        r.set_library_names(&HashMap::from([(
            uuid::Uuid::new_v4().to_string(),
            vec!["Occurrences".into(), "Occurrence".into()],
        )]));
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert_eq!(rows, r.b.elements.len());
        assert_eq!(
            state,
            Some((r.b.semantic_ready, r.b.positional_redefinitions.is_some()))
        );
        assert!(!std::sync::Arc::ptr_eq(
            &retained,
            r.b.supported_implied.as_ref().unwrap()
        ));
        let mut steps = crate::eval::MAX_STEPS;
        assert_eq!(
            proof.specializes(&mut r.b, c, occurrence, &mut steps),
            RelationFact::Unknown
        );
        assert!(
            std::sync::Arc::ptr_eq(&retained, proof.retained_plan.as_ref().unwrap()),
            "refused invalidation must not refresh its authority"
        );
        assert_eq!(
            proof.specializes(&mut r.b, c, occurrence, &mut 0),
            RelationFact::Unknown
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, c, occurrence, &mut 0),
            RelationFact::Unknown
        );
    }

    #[test]
    fn held_relation_query_rechecks_after_positional_preparation() {
        let mut model = crate::model::Model::new();
        model.add_library_source(
            "planner-library.kerml",
            "standard library package Occurrences {class Occurrence;}",
        );
        model.add_source("planner-state.kerml", "class C;");
        let mut r = crate::json::ResolvedModel::build(&model);
        let p = r.resolve_qualified("Occurrences::Occurrence").unwrap().0;
        let q = r.resolve_qualified("C").unwrap().0;
        r.b.positional_redefinitions = None;
        r.b.semantic_ready = false;
        let mut proof = TypeRelations::default();
        assert_eq!(proof.specializes(&mut r.b, q, p, &mut 0), RelationFact::Yes);
        assert!(!proof.known.is_empty());
        r.b.semantic_ready = true;
        assert!(r.b.ensure_positional_redefinitions_with_budget(&mut 0));
        assert!(proof.refresh_planner_state(&mut r.b, &mut 0).is_some());
        assert!(
            proof.known.is_empty(),
            "the old positive requires fresh evidence"
        );
        assert_eq!(proof.specializes(&mut r.b, q, p, &mut 0), RelationFact::Yes);
    }

    #[test]
    fn a_decisive_negative_refutes_universal_compatibility_in_either_order() {
        use RelationFact::*;
        assert_eq!(RelationFact::all([]), Yes);
        assert_eq!(RelationFact::all([Yes, Yes]), Yes);
        assert_eq!(RelationFact::all([Yes, Unknown]), Unknown);
        assert_eq!(RelationFact::all([Unknown, No]), No);
        assert_eq!(RelationFact::all([No, Unknown]), No);
        assert_eq!(RelationFact::all([Yes, Unknown, No, Yes]), No);
    }

    use super::*;
    use crate::{
        json::{ResolvedModel, id_ref},
        model::Model,
    };

    fn fixture(source: &str) -> ResolvedModel {
        let mut model = Model::new();
        model.add_library_source("bases.kerml", "standard library package Base {classifier Anything; datatype DataValue specializes Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;} standard library package Objects {struct Object specializes Occurrences::Occurrence;}");
        let unit = model.add_source("relations.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&model)
    }

    #[test]
    fn conjugation_precedence_and_chain_target_use_stored_identities() {
        let mut r = fixture(
            "class A; class B; class C conjugates A; class D conjugates C; class E specializes C; class T { feature b; } feature a : T; feature chain chains a.b;",
        );
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let c = r.resolve_qualified("C").unwrap().0;
        let d = r.resolve_qualified("D").unwrap().0;
        let e = r.resolve_qualified("E").unwrap().0;
        let chain = r.resolve_qualified("chain").unwrap().0;
        let end = r.resolve_qualified("T::b").unwrap().0;
        let mut proof = TypeRelations::default();
        assert_eq!(proof.specializes(&mut r.b, c, a, &mut 0), RelationFact::Yes);
        assert_eq!(proof.specializes(&mut r.b, c, b, &mut 0), RelationFact::No);
        assert_eq!(proof.specializes(&mut r.b, c, c, &mut 0), RelationFact::No);
        assert_eq!(proof.specializes(&mut r.b, d, c, &mut 0), RelationFact::No);
        assert_eq!(proof.specializes(&mut r.b, d, a, &mut 0), RelationFact::Yes);
        assert_eq!(proof.specializes(&mut r.b, e, c, &mut 0), RelationFact::Yes);
        assert_eq!(proof.specializes(&mut r.b, e, a, &mut 0), RelationFact::Yes);
        // Reusing closure facts for E must not restore C receiver reflexivity.
        assert_eq!(proof.specializes(&mut r.b, c, c, &mut 0), RelationFact::No);
        assert_eq!(proof.specializes(&mut r.b, d, c, &mut 0), RelationFact::No);
        assert_eq!(
            proof.specializes(&mut r.b, chain, end, &mut 0),
            RelationFact::Yes
        );
        // Manufacture mixed stored evidence without relying on invalid syntax:
        // conjugation must still take precedence over the extra specialization.
        let extra = r.b.new_relationship("Specialization", c, "extra");
        let b_id = r.b.elem_id(b);
        r.b.set(extra, "general", id_ref(b_id));
        let mut proof = TypeRelations::default();
        assert_eq!(proof.specializes(&mut r.b, c, b, &mut 0), RelationFact::No);
        assert_eq!(proof.specializes(&mut r.b, c, a, &mut 0), RelationFact::Yes);
    }

    #[test]
    fn missing_conflicting_and_cyclic_evidence_never_proves_absence() {
        let mut r = fixture(
            "class A; class B; class C specializes A, Missing; class Cycle specializes Cycle; class Good specializes A;",
        );
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let c = r.resolve_qualified("C").unwrap().0;
        let cycle = r.resolve_qualified("Cycle").unwrap().0;
        let good = r.resolve_qualified("Good").unwrap().0;
        let mut proof = TypeRelations::default();
        assert_eq!(proof.specializes(&mut r.b, c, a, &mut 0), RelationFact::Yes);
        assert_eq!(
            proof.specializes(&mut r.b, c, b, &mut 0),
            RelationFact::Unknown
        );
        assert_eq!(
            proof.specializes(&mut r.b, cycle, b, &mut 0),
            RelationFact::Unknown
        );
        let relation = r.b.elements[good]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| is_a!(r.b.elements[rel], "Specialization"))
            .unwrap();
        let b_id = r.b.elem_id(b);
        r.b.set(relation, "general", id_ref(b_id));
        let mut proof = TypeRelations::default();
        assert_eq!(
            proof.specializes(&mut r.b, good, a, &mut 0),
            RelationFact::Unknown
        );
        assert_eq!(
            proof.specializes(&mut r.b, good, b, &mut 0),
            RelationFact::Unknown
        );
    }

    #[test]
    fn conjugator_failure_precedes_reflexivity_but_unrelated_base_failure_does_not() {
        let mut r = fixture(
            "class MissingOriginal conjugates Missing; class Loop conjugates Loop; class Ordinary specializes Missing;",
        );
        for name in ["MissingOriginal", "Loop"] {
            let element = r.resolve_qualified(name).unwrap().0;
            assert_eq!(
                TypeRelations::default().specializes(&mut r.b, element, element, &mut 0),
                RelationFact::Unknown
            );
        }
        let ordinary = r.resolve_qualified("Ordinary").unwrap().0;
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, ordinary, ordinary, &mut 0),
            RelationFact::Yes
        );
    }

    #[test]
    fn budget_exhaustion_does_not_poison_a_later_query() {
        let mut r = fixture("class A; class B specializes A;");
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let mut proof = TypeRelations::default();
        let mut exhausted = crate::eval::MAX_STEPS;
        assert_eq!(
            proof.specializes(&mut r.b, b, a, &mut exhausted),
            RelationFact::Unknown
        );
        assert_eq!(proof.specializes(&mut r.b, b, a, &mut 0), RelationFact::Yes);
        exhausted = crate::eval::MAX_STEPS;
        assert_eq!(
            proof.specializes(&mut r.b, b, a, &mut exhausted),
            RelationFact::Unknown
        );
    }
}

/// Query-local semantic witnesses over a shared immutable stored graph index.
#[derive(Default)]
struct FeaturingEvidence {
    structure: std::sync::Arc<super::structural_index::StoredStructure>,
    owners: HashMap<usize, Option<Option<usize>>>,
    featuring: HashMap<usize, Vec<usize>>,
}
impl std::ops::Deref for FeaturingEvidence {
    type Target = super::structural_index::StoredStructure;
    fn deref(&self) -> &Self::Target {
        &self.structure
    }
}
impl FeaturingEvidence {
    fn carrier(&self, b: &Builder, relation: usize, steps: &mut usize) -> Option<Option<usize>> {
        semantic_ownership::checked_relationship_carrier(b, &self.structure, relation, steps)
    }
    fn relationships(&self, b: &Builder, owner: usize, steps: &mut usize) -> Option<Vec<usize>> {
        let rows = semantic_ownership::owned_relationships(b, owner)?;
        charge(steps, rows.len())?;
        Some(rows.iter().collect())
    }
    fn index(&mut self, b: &mut Builder, steps: &mut usize) -> Option<()> {
        if self.structure.is_current(b) {
            charge(steps, 1)?;
            return Some(());
        }
        self.structure = super::structural_index::StoredStructure::get(b, steps)?;
        self.owners.clear();
        self.featuring.clear();
        Some(())
    }

    fn owning_type(
        &mut self,
        b: &mut Builder,
        feature: usize,
        steps: &mut usize,
    ) -> Option<Option<usize>> {
        self.index(b, steps)?;
        if self.incomplete() {
            return None;
        }
        if let Some(&owner) = self.owners.get(&feature) {
            return owner;
        }
        let result = self.inspect_owner(b, feature, steps);
        if *steps <= crate::eval::MAX_STEPS {
            self.owners.insert(feature, result);
        }
        result
    }

    fn inspect_owner(
        &self,
        b: &Builder,
        feature: usize,
        steps: &mut usize,
    ) -> Option<Option<usize>> {
        charge(steps, 1)?;
        let e = b.elements.get(feature)?;
        if !is_a!(e, "Feature") {
            return None;
        }
        let rel = match e.owning_relationship {
            Some(rel) => rel,
            None => return Some(None),
        };
        let membership = b.elements.get(rel)?;
        if !is_a!(membership, "OwningMembership") {
            // The chain a specialization names (`:> a.b`): a feature the
            // specialization owns has no owning feature membership, so no
            // owning type.
            if conforms(membership.ty, "Specialization") && *membership.children == [feature] {
                self.carrier(b, rel, steps)??;
                return Some(None);
            }
            return None;
        }
        let owner = self.carrier(b, rel, steps)??;
        if *membership.children != [feature] {
            return None;
        }
        validate_relationship_arrays(b, rel, owner, feature, steps)?;
        for key in ["memberElement", "ownedMemberElement", "ownedMemberFeature"] {
            if membership
                .props
                .get(key)
                .is_some_and(|value| value.as_reference() != Some(e.id))
            {
                return None;
            }
        }
        for key in ["membershipOwningNamespace", "owningType"] {
            if membership
                .props
                .get(key)
                .is_some_and(|value| value.as_reference() != Some(b.elements[owner].id))
            {
                return None;
            }
        }
        if is_a!(membership, "FeatureMembership") {
            is_a!(b.elements[owner], "Type").then_some(Some(owner))
        } else {
            Some(None)
        }
    }

    fn first_chaining_feature(
        &mut self,
        b: &mut Builder,
        feature: usize,
        steps: &mut usize,
    ) -> Option<Option<usize>> {
        self.index(b, steps)?;
        if self.incomplete() {
            return None;
        }
        for rel in self.relationships(b, feature, steps)? {
            if !conforms(b.elements.get(rel)?.ty, "FeatureChaining") {
                continue;
            }
            if self.carrier(b, rel, steps)? != Some(feature) {
                return None;
            }
            return Some(Some(endpoint(
                b,
                feature,
                rel,
                &["featureChained"],
                &["chainingFeature"],
                "Feature",
                steps,
            )?));
        }
        Some(None)
    }
    fn featuring_types(
        &mut self,
        b: &mut Builder,
        feature: usize,
        active: &mut HashSet<usize>,
        steps: &mut usize,
    ) -> Option<Vec<usize>> {
        if !b.local_featuring_evidence_current(feature) {
            return None;
        }
        self.index(b, steps)?;
        if self.incomplete()
            || self.bad_chains.contains(&feature)
            || active.len() > super::MAX_RESOLUTION_DEPTH
        {
            return None;
        }
        charge(steps, 1)?;
        if let Some(known) = self.featuring.get(&feature) {
            charge(steps, known.len())?;
            return Some(known.clone());
        }
        if !active.insert(feature) {
            return None;
        }
        let result = (|| {
            let mut out: Vec<_> = self.owning_type(b, feature, steps)?.into_iter().collect();
            let mut seen: HashSet<_> = out.iter().copied().collect();
            let owned = self.relationships(b, feature, steps)?;
            let inverse_count = self.type_featurings.get(&feature).map_or(0, Vec::len);
            charge(steps, inverse_count)?;
            let mut featurings = self
                .type_featurings
                .get(&feature)
                .cloned()
                .unwrap_or_default();
            let mut featuring_relations: HashSet<_> = featurings.iter().copied().collect();
            for &rel in &owned {
                if conforms(b.elements.get(rel)?.ty, "TypeFeaturing")
                    && featuring_relations.insert(rel)
                {
                    featurings.push(rel);
                }
            }
            charge(steps, featurings.len().saturating_sub(inverse_count))?;
            for rel in featurings {
                self.carrier(b, rel, steps)?;
                let relation = &b.elements[rel];
                if let Some(source) = relation.props.get("featureOfType") {
                    if source.as_reference() != Some(b.elements[feature].id) {
                        return None;
                    }
                } else if self.carrier(b, rel, steps)? != Some(feature) {
                    return None;
                }
                let id = relation.props.get("featuringType")?.as_reference()?;
                let target = b.element_index_of_uuid(id)?;
                if !is_a!(b.elements[target], "Type") {
                    return None;
                }
                validate_relationship_arrays(b, rel, feature, target, steps)?;
                if seen.insert(target) {
                    out.push(target);
                }
            }
            let mut first = None;
            for rel in owned {
                if !conforms(b.elements.get(rel)?.ty, "FeatureChaining") {
                    continue;
                }
                if self.carrier(b, rel, steps)? != Some(feature) {
                    return None;
                }
                let target = endpoint(
                    b,
                    feature,
                    rel,
                    &["featureChained"],
                    &["chainingFeature"],
                    "Feature",
                    steps,
                )?;
                first.get_or_insert(target);
            }
            if let Some(first) = first {
                for target in self.featuring_types(b, first, active, steps)? {
                    if seen.insert(target) {
                        out.push(target);
                    }
                }
            }
            Some(out)
        })();
        active.remove(&feature);
        if let Some(ref out) = result {
            self.featuring.insert(feature, out.clone());
        }
        result
    }
}

#[cfg(test)]
mod featuring_evidence_tests {
    use super::*;
    use crate::{
        json::{ResolvedModel, id_ref},
        model::Model,
    };

    fn model(source: &str) -> ResolvedModel {
        let mut model = Model::new();
        model.add_library_source("bases.kerml","standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;}");
        let parsed = model.add_source("evidence.kerml", source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        ResolvedModel::build(&model)
    }

    #[test]
    fn inverse_featuring_and_reciprocal_membership_are_observed() {
        let mut r = model("class B; class A {feature x;} featuring A::x by B;");
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let x = r.resolve_qualified("A::x").unwrap().0;
        let mut proof = TypeRelations::default();
        assert_eq!(proof.featuring_types(&mut r.b, x, &mut 0), Some(vec![a, b]));
        let membership = r.b.elements[x].owning_relationship.unwrap();
        let wrong = r.b.elem_id(b);
        r.b.set(membership, "memberElement", id_ref(wrong));
        assert_eq!(
            TypeRelations::default().featuring_types(&mut r.b, x, &mut 0),
            None
        );
    }

    #[test]
    fn out_of_range_owning_relationship_refuses_domain_without_panicking() {
        let mut r = model("class A {feature x;}");
        let x = r.resolve_qualified("A::x").unwrap().0;
        r.b.elements[x].owning_relationship = Some(r.b.elements.len());
        assert_eq!(
            TypeRelations::default().audited_featuring_domain(&mut r.b, &[x], &mut 0),
            None
        );
    }

    #[test]
    fn contradictory_stored_carrier_cannot_supply_ownership_witness() {
        let mut r = model("class A {feature container {feature x;}} class B;");
        let owner = r.resolve_qualified("A::container").unwrap().0;
        let x = r.resolve_qualified("A::container::x").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let membership = r.b.elements[x].owning_relationship.unwrap();
        let wrong = r.b.elem_id(b);
        r.b.set(membership, "owningRelatedElement", id_ref(wrong));
        let mut proof = TypeRelations::default();
        assert_eq!(proof.featuring_types(&mut r.b, x, &mut 0), None);
        assert_ne!(proof.has_owned_feature(&mut r.b, owner, &mut 0), Some(true));
    }

    #[test]
    fn contradictory_generic_specialization_and_conjugation_arrays_are_unknown() {
        for declaration in ["class C specializes A;", "class C conjugates A;"] {
            for key in ["source", "target", "relatedElement", "ownedRelatedElement"] {
                let mut r = model(&format!("class A; class B; {declaration}"));
                let a = r.resolve_qualified("A").unwrap().0;
                let b = r.resolve_qualified("B").unwrap().0;
                let c = r.resolve_qualified("C").unwrap().0;
                let relation = r.b.elements[c]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&r0| {
                        is_a!(r.b.elements[r0], "Specialization")
                            || is_a!(r.b.elements[r0], "Conjugation")
                    })
                    .unwrap();
                let wrong = r.b.elements[b].id;
                r.b.elements[relation]
                    .props
                    .insert(key, serde_json::json!([{"@id":wrong.to_string()}]));
                assert_eq!(
                    TypeRelations::default().specializes(&mut r.b, c, a, &mut 0),
                    RelationFact::Unknown,
                    "{declaration} {key}"
                );
            }
        }
    }

    #[test]
    fn standalone_featuring_generic_source_is_feature_not_actual_carrier() {
        let mut r = model("class B; class A {feature x;} featuring A::x by B;");
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let x = r.resolve_qualified("A::x").unwrap().0;
        let relation =
            r.b.elements
                .iter()
                .position(|e| is_a!(e, "TypeFeaturing"))
                .unwrap();
        let x_id = r.b.elements[x].id;
        let b_id = r.b.elements[b].id;
        r.b.elements[relation]
            .props
            .insert("source", serde_json::json!([{"@id":x_id.to_string()}]));
        r.b.elements[relation]
            .props
            .insert("target", serde_json::json!([{"@id":b_id.to_string()}]));
        r.b.elements[relation].props.insert(
            "relatedElement",
            serde_json::json!([{"@id":x_id.to_string()},{"@id":b_id.to_string()}]),
        );
        r.b.elements[relation]
            .props
            .insert("ownedRelatedElement", serde_json::json!([]));
        assert_eq!(
            TypeRelations::default().featuring_types(&mut r.b, x, &mut 0),
            Some(vec![a, b])
        );
        let wrong = r.b.elements[a].id;
        r.b.elements[relation]
            .props
            .insert("target", serde_json::json!([{"@id":wrong.to_string()}]));
        assert_eq!(
            TypeRelations::default().featuring_types(&mut r.b, x, &mut 0),
            None
        );
    }

    #[test]
    fn authored_implied_flags_do_not_bypass_endpoint_checks() {
        let mut r = model("class A; class B; class C specializes A;");
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let c = r.resolve_qualified("C").unwrap().0;
        let relation = r.b.elements[c]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| is_a!(r.b.elements[rel], "Specialization"))
            .unwrap();
        let wrong = r.b.elements[b].id;
        r.b.elements[relation]
            .props
            .insert("isImplied", serde_json::json!(true));
        r.b.elements[relation]
            .props
            .insert("target", serde_json::json!([{"@id":wrong.to_string()}]));
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, c, a, &mut 0),
            RelationFact::Unknown
        );
    }

    #[test]
    fn duplicate_owned_related_children_are_not_a_unique_ownership_set() {
        let mut r = model("class A; class C specializes A;");
        let a = r.resolve_qualified("A").unwrap().0;
        let c = r.resolve_qualified("C").unwrap().0;
        let relation = r.b.elements[c]
            .owned_relationships
            .iter()
            .copied()
            .find(|&r0| is_a!(r.b.elements[r0], "Specialization"))
            .unwrap();
        r.b.elements[relation].children = vec![a, a].into();
        r.b.elements[a].owning_relationship = Some(relation);
        let id = r.b.elements[a].id;
        r.b.elements[relation].props.insert(
            "ownedRelatedElement",
            serde_json::json!([{"@id":id.to_string()},{"@id":id.to_string()}]),
        );
        assert_eq!(
            validate_relationship_arrays(&r.b, relation, c, a, &mut 0),
            None
        );
    }

    #[test]
    fn contradictory_generic_membership_array_cannot_supply_owning_type() {
        let mut r = model("class A {feature x;} class B;");
        let x = r.resolve_qualified("A::x").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let membership = r.b.elements[x].owning_relationship.unwrap();
        let wrong = r.b.elements[b].id;
        r.b.elements[membership]
            .props
            .insert("target", serde_json::json!([{"@id":wrong.to_string()}]));
        assert_eq!(
            TypeRelations::default().owning_type(&mut r.b, x, &mut 0),
            None
        );
    }

    #[test]
    fn unaudited_named_expressions_never_supply_negative_specialization_facts() {
        let mut r = model("expr expression; bool boolean; class Other;");
        let other = r.resolve_qualified("Other").unwrap().0;
        for name in ["expression", "boolean"] {
            let expression = r.resolve_qualified(name).unwrap().0;
            assert_eq!(
                TypeRelations::default().specializes(&mut r.b, expression, other, &mut 0),
                RelationFact::Unknown
            );
        }
    }

    #[test]
    fn missing_required_library_identity_prevents_negative_type_fact() {
        let mut model = Model::new();
        model.add_source("missing.kerml", "class A; class B;");
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, a, b, &mut 0),
            RelationFact::Unknown
        );
    }
    #[test]
    fn owned_feature_budget_retry_does_not_cache_a_false_witness() {
        let mut r = model("class A {feature x;}");
        let a = r.resolve_qualified("A").unwrap().0;
        let mut proof = TypeRelations::default();
        let mut exhausted = crate::eval::MAX_STEPS - 5;
        assert_eq!(proof.has_owned_feature(&mut r.b, a, &mut exhausted), None);
        assert_eq!(proof.has_owned_feature(&mut r.b, a, &mut 0), Some(true));
    }

    #[test]
    fn required_names_without_a_shared_ancestor_path_are_incomplete() {
        let mut model = Model::new();
        model.add_library_source(
            "partial.kerml",
            "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence;}",
        );
        model.add_source("uses.kerml", "class A; class B;");
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let occurrence = r.resolve_qualified("Occurrences::Occurrence").unwrap().0;
        let anything = r.resolve_qualified("Base::Anything").unwrap().0;
        assert_eq!(
            TypeRelations::default().required_bases(&mut r.b, a, &mut 0),
            Some(vec![occurrence, anything])
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, a, b, &mut 0),
            RelationFact::Unknown
        );
    }
}
#[cfg(test)]
mod owned_result_projection_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};

    fn fixture() -> (ResolvedModel, usize, usize) {
        let mut model = Model::new();
        model.add_source("results.kerml", "feature n=1; feature read=n;");
        assert!(!model.has_errors());
        let mut resolved = ResolvedModel::build(&model);
        let target = resolved.resolve_qualified("n").unwrap().0;
        let read = resolved.resolve_qualified("read").unwrap().0;
        let value = resolved.b.elements[read]
            .owned_relationships
            .iter()
            .copied()
            .find(|&r| is_a!(resolved.b.elements[r], "FeatureValue"))
            .unwrap();
        let expression = resolved.b.elements[value].children[0];
        (resolved, expression, target)
    }

    #[test]
    fn generated_return_proves_local_ownership_and_subsetting_without_certifying_empty_family() {
        let (mut r, expression, target) = fixture();
        assert_eq!(
            TypeRelations::default().has_owned_feature(&mut r.b, expression, &mut 0),
            None
        );
        r.ensure_implied();
        let result =
            r.b.semantic_ownership
                .as_ref()
                .unwrap()
                .result(expression)
                .unwrap();
        let mut proof = TypeRelations::default();
        assert_eq!(
            proof.owning_type(&mut r.b, result.feature, &mut 0),
            Some(Some(expression))
        );
        assert_eq!(
            proof.has_owned_feature(&mut r.b, expression, &mut 0),
            Some(true)
        );
        assert_eq!(
            proof.specializes(&mut r.b, result.feature, target, &mut 0),
            RelationFact::Yes
        );
    }

    #[test]
    fn generated_membership_does_not_hide_corrupt_owner_alias_or_child_backlink() {
        for child_backlink in [false, true] {
            let (mut r, expression, target) = fixture();
            r.ensure_implied();
            let result =
                r.b.semantic_ownership
                    .as_ref()
                    .unwrap()
                    .result(expression)
                    .unwrap();
            if child_backlink {
                r.b.elements[result.membership].owning_relationship = Some(result.membership);
            } else {
                let wrong = r.b.elements[target].id;
                r.b.elements[result.membership].props.insert(
                    "owningRelatedElement",
                    serde_json::json!({"@id":wrong.to_string()}),
                );
            }
            assert_eq!(
                TypeRelations::default().owning_type(&mut r.b, result.feature, &mut 0),
                None
            );
        }
    }
}

#[cfg(test)]
mod annotation_completeness_tests {
    use super::*;
    use crate::{json::ResolvedModel, model::Model};
    const LIBRARY: &str = "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;} standard library package Metaobjects {metaclass SemanticMetadata {feature baseType;}}";
    fn fixture(about: bool, explicit: bool) -> ResolvedModel {
        let mut model = Model::new();
        let p = model.add_library_source("annotation-bases.kerml", LIBRARY);
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let class = if explicit {
            "class C specializes A;"
        } else {
            "class C;"
        };
        let suffix = if about {
            format!("{class} @Tagged about C;")
        } else {
            format!("#Tagged {class}")
        };
        let src = format!(
            "metaclass U; class A; metaclass Tagged :> Metaobjects::SemanticMetadata {{:>> baseType=A meta U;}} {suffix}"
        );
        let p = model.add_source("annotations.kerml", &src);
        assert!(p.diagnostics.is_empty(), "{:?}", p.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let semantic = r
            .resolve_qualified("Metaobjects::SemanticMetadata")
            .unwrap();
        assert_eq!(
            crate::json::library_element_name_map(&model).get(&r.element_id(semantic).to_string()),
            Some(&vec![
                "Metaobjects".to_owned(),
                "SemanticMetadata".to_owned()
            ])
        );
        r
    }
    #[test]
    fn semantic_metadata_annotation_supplies_specialization_evidence() {
        for about in [false, true] {
            for explicit in [false, true] {
                let mut r = fixture(about, explicit);
                let c = r.resolve_qualified("C").unwrap().0;
                let a = r.resolve_qualified("A").unwrap().0;
                // Both annotation spellings share positive association
                // storage, and the semantic metadata's base is a planned
                // row (KerML 9.2), so the checked specialization provider
                // certifies it whether or not the specialization is written.
                assert_eq!(r.b.metadata_of.get(&c).map(Vec::len), Some(1));
                let mut proof = TypeRelations::default();
                assert_eq!(
                    proof.specializes(&mut r.b, c, a, &mut 0),
                    RelationFact::Yes,
                    "about {about}, explicit {explicit}"
                );
            }
        }
    }
}

#[cfg(test)]
#[path = "function_specialization_readiness_tests.rs"]
mod function_specialization_readiness_tests;

#[cfg(test)]
#[path = "supertypes_checked_tests.rs"]
mod supertypes_checked_tests;
#[cfg(test)]
mod ordinary_owned_feature_tests {
    use super::{RelationFact, TypeRelations};
    use crate::{
        json::ResolvedModel,
        model::{GraphFormat, Model},
    };
    fn fixture(format: GraphFormat, source: &str) -> ResolvedModel {
        let mut model = Model::with_graph_format(format);
        model.add_library_source("feature-roles.kerml", "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;} standard library package Links {assoc SelfLink specializes Base::Anything;}");
        let unit = model.add_source("owned-features.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&model)
    }
    #[test]
    fn ordinary_owned_feature_specialization_has_complete_ancestry() {
        for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
            let mut r = fixture(
                format,
                "class Parent {feature slot;} class Child specializes Parent {feature slot redefines Parent::slot;}",
            );
            let slot = r.resolve_qualified("Child::slot").unwrap().0;
            let inherited = r.resolve_qualified("Parent::slot").unwrap().0;
            let unrelated = r.resolve_qualified("Links::SelfLink").unwrap().0;
            let mut proof = TypeRelations::default();
            assert_eq!(
                proof.specializes(&mut r.b, slot, inherited, &mut 0),
                RelationFact::Yes
            );
            assert_eq!(
                proof.specializes(&mut r.b, slot, unrelated, &mut 0),
                RelationFact::No
            );
            assert!(
                proof
                    .complete_direct_bases(&mut r.b, slot, &mut 0)
                    .is_some()
            );
            r.b.set(slot, "direction", serde_json::json!("in"));
            assert_eq!(
                proof.specializes(&mut r.b, slot, unrelated, &mut 0),
                RelationFact::Unknown
            );
            r.b.set(slot, "direction", serde_json::Value::Null);
            // Repairing a row does not relabel old evidence as current. A
            // separate query must establish the repaired domain again.
            assert_eq!(
                proof.specializes(&mut r.b, slot, unrelated, &mut 0),
                RelationFact::Unknown
            );
            assert_eq!(
                TypeRelations::default().specializes(&mut r.b, slot, unrelated, &mut 0),
                RelationFact::No
            );
        }
    }
    #[test]
    fn ordinary_owned_feature_keeps_contextual_families_and_malformed_ownership_qualified() {
        // An end (0) takes its positional targets from its owner's
        // certificate and a behaviour owner (5) is an audited context, so
        // those negative proofs complete; an untyped composite (1), a
        // variable Kernel feature (2), a malformed direction (3), an end
        // membership of a non-end (4) and a lost membership (6) stay
        // qualified.
        for (mutation, expected) in [
            (0, RelationFact::No),
            (1, RelationFact::Unknown),
            (2, RelationFact::Unknown),
            (3, RelationFact::Unknown),
            (4, RelationFact::Unknown),
            (5, RelationFact::No),
            (6, RelationFact::Unknown),
        ] {
            let mut r = fixture(GraphFormat::CanonicalV3, "class Parent {feature slot;}");
            let parent = r.resolve_qualified("Parent").unwrap().0;
            let slot = r.resolve_qualified("Parent::slot").unwrap().0;
            let unrelated = r.resolve_qualified("Links::SelfLink").unwrap().0;
            let membership = r.b.elements[slot].owning_relationship.unwrap();
            match mutation {
                0 => r.b.set(slot, "isEnd", serde_json::json!(true)),
                1 => r.b.set(slot, "isComposite", serde_json::json!(true)),
                2 => r.b.set(slot, "isVariable", serde_json::json!(true)),
                3 => r.b.set(slot, "direction", serde_json::json!(false)),
                4 => r.b.elements[membership].set_ty("EndFeatureMembership"),
                5 => r.b.elements[parent].set_ty("Function"),
                _ => r.b.elements[parent]
                    .owned_relationships
                    .make_mut()
                    .retain(|&m| m != membership),
            }
            assert_eq!(
                TypeRelations::default().specializes(&mut r.b, slot, unrelated, &mut 0),
                expected,
                "mutation {mutation}"
            );
        }
        // A feature value binds the feature's value and adds no
        // specialization obligation: the negative proof stays complete.
        let mut r = fixture(GraphFormat::CanonicalV3, "class Parent {feature slot=4;}");
        let slot = r.resolve_qualified("Parent::slot").unwrap().0;
        let unrelated = r.resolve_qualified("Links::SelfLink").unwrap().0;
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, slot, unrelated, &mut 0),
            RelationFact::No
        );
    }
}

#[cfg(test)]
mod usage_requirement_tests {
    use super::{RelationFact, TypeRelations};
    use crate::{json::ResolvedModel, model::Model};
    const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; assoc HappensLink specializes Base::Anything;} standard library package Links {assoc SelfLink specializes Base::Anything;}";
    fn fixture(source: &str) -> ResolvedModel {
        let mut m = Model::new();
        assert!(
            m.add_library_source("roles.kerml", LIB)
                .diagnostics
                .is_empty()
        );
        assert!(
            m.add_library_source(
                "roles.sysml",
                "standard library package Actions {action def Action :> Occurrences::Occurrence;}"
            )
            .diagnostics
            .is_empty()
        );
        assert!(m.add_source("source.sysml", source).diagnostics.is_empty());
        ResolvedModel::build(&m)
    }
    fn relation(r: &mut ResolvedModel, source: &str, target: &str) -> RelationFact {
        let a = r.resolve_qualified(source).unwrap().0;
        let z = r.resolve_qualified(target).unwrap().0;
        TypeRelations::default().specializes(&mut r.b, a, z, &mut 0)
    }
    #[test]
    fn actual_reference_usage_has_complete_negative_exclusion_paths() {
        let mut r = fixture("part def P :> Occurrences::Occurrence { ref x :> Base::things; }");
        let x = r.resolve_qualified("P::x").unwrap();
        assert_eq!(r.element_type(x), "ReferenceUsage");
        assert_eq!(
            relation(&mut r, "P", "Occurrences::Occurrence"),
            RelationFact::Yes
        );
        for target in [
            "Links::SelfLink",
            "Occurrences::HappensLink",
            "Actions::Action",
        ] {
            assert_eq!(
                relation(&mut r, "P::x", target),
                RelationFact::No,
                "{target}"
            );
        }
    }
    #[test]
    fn generic_feature_ancestry_closes_plain_reference_but_not_end_context() {
        for source in [
            "part def P { ref x; }",
            "part def P { end x :> Base::things; }",
        ] {
            let mut r = fixture(source);
            assert_eq!(
                relation(&mut r, "P::x", "Links::SelfLink"),
                if source.contains("ref x") {
                    RelationFact::No
                } else {
                    RelationFact::Unknown
                },
                "{source}"
            );
        }
    }
    #[test]
    fn plain_reference_still_requires_the_loaded_generic_feature_role() {
        let mut r = fixture("part def P { ref x; }");
        assert_eq!(
            relation(&mut r, "P::x", "Links::SelfLink"),
            RelationFact::No
        );
        let role =
            r.b.lib_qnames
                .iter()
                .position(|(_, name)| name.as_slice() == ["Base", "things"])
                .unwrap();
        r.b.lib_qnames[role].1[1] = "renamedThings".into();
        r.b.supported_implied = None;
        assert_eq!(
            relation(&mut r, "P::x", "Links::SelfLink"),
            RelationFact::Unknown
        );
    }
    #[test]
    fn positive_exclusion_survives_unsupported_owned_family() {
        let mut r = fixture("part def P { ref x : Links::SelfLink; }");
        assert_eq!(
            relation(&mut r, "P::x", "Links::SelfLink"),
            RelationFact::Yes
        );
        assert_eq!(
            relation(&mut r, "P::x", "Occurrences::HappensLink"),
            RelationFact::Unknown
        );
    }
    #[test]
    fn malformed_flags_and_missing_required_role_refuse_absence() {
        for key in ["isPortion", "isEnd", "isComposite", "isVariable"] {
            let mut r = fixture("part def P { ref x :> Base::things; }");
            let x = r.resolve_qualified("P::x").unwrap().0;
            r.b.set(x, key, serde_json::json!("malformed"));
            assert_eq!(
                relation(&mut r, "P::x", "Links::SelfLink"),
                RelationFact::Unknown,
                "{key}"
            );
        }
        let mut r = fixture("part def P { ref x :> Base::things; }");
        let role =
            r.b.lib_qnames
                .iter()
                .position(|(_, name)| name.as_slice() == ["Base", "things"])
                .unwrap();
        r.b.lib_qnames[role].1[1] = "renamedThings".into();
        assert_eq!(
            relation(&mut r, "P::x", "Links::SelfLink"),
            RelationFact::Unknown
        );
    }
    #[test]
    fn exhausted_proof_retries_and_changed_rows_revoke_negative() {
        let mut r = fixture("part def P { ref x :> Base::things; }");
        let x = r.resolve_qualified("P::x").unwrap().0;
        let z = r.resolve_qualified("Links::SelfLink").unwrap().0;
        let mut proof = TypeRelations::default();
        let mut exhausted = crate::eval::MAX_STEPS;
        assert_eq!(
            proof.specializes(&mut r.b, x, z, &mut exhausted),
            RelationFact::Unknown
        );
        assert_eq!(proof.specializes(&mut r.b, x, z, &mut 0), RelationFact::No);
        r.set_library_names(&std::collections::HashMap::from([(
            uuid::Uuid::new_v4().to_string(),
            vec!["Unrelated".into(), "Role".into()],
        )]));
        assert_eq!(
            proof.specializes(&mut r.b, x, z, &mut 0),
            RelationFact::Unknown
        );
        let mut proof = TypeRelations::default();
        assert_eq!(proof.specializes(&mut r.b, x, z, &mut 0), RelationFact::No);
        r.b.set(x, "isEnd", serde_json::json!(true));
        assert_eq!(
            proof.specializes(&mut r.b, x, z, &mut 0),
            RelationFact::Unknown
        );
        assert_eq!(
            TypeRelations::default().specializes(&mut r.b, x, z, &mut 0),
            RelationFact::Unknown
        );
    }
    #[test]
    fn real_library_reference_usage_exclusions_replay() {
        use crate::{libcache::LibraryCache, prepared::PreparedLibrary};
        use std::sync::Arc;
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../spec-refs/SysML-v2-Release/sysml.library");
        let mut library = Model::new();
        library.load_library_dir(&path).unwrap();
        library.record_library_cache();
        ResolvedModel::build(&library);
        let cache =
            LibraryCache::from_bytes(&library.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = library.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(113).unwrap(), 113).unwrap());
        let mut expected = None;
        for mode in 0..4 {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.load_library_dir(&path).unwrap();
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            assert!(
                m.add_source("source.sysml", "part def P { ref x :> Base::things; }")
                    .diagnostics
                    .is_empty()
            );
            let mut r = ResolvedModel::build(&m);
            let before: Vec<_> = r.user_elements().map(|e| r.element_id(e)).collect();
            if let Some(expected) = &expected {
                assert_eq!(&before, expected);
            } else {
                expected = Some(before.clone());
            }
            assert_eq!(
                relation(&mut r, "P", "Occurrences::Occurrence"),
                RelationFact::Yes
            );
            for target in [
                "Links::SelfLink",
                "Occurrences::HappensLink",
                "Actions::Action",
            ] {
                assert_eq!(
                    relation(&mut r, "P::x", target),
                    RelationFact::No,
                    "mode {mode}: {target}"
                );
            }
            assert_eq!(
                before,
                r.user_elements()
                    .map(|e| r.element_id(e))
                    .collect::<Vec<_>>()
            );
        }
    }
}
