//! Checked normative operation invocation, separate from AST scalar evaluation.
use super::{
    DerivedValue, ElementRef, Reference, ResolvedModel,
    type_relations::{RelationFact, SupertypesFailure, TypeRelations},
};
use crate::{
    metaclass::conforms,
    metamodel::{self, OperationSpec, ParameterSpec},
};
pub(in crate::json) mod elements;
pub(in crate::json) mod evaluation;
pub(in crate::json) mod features;
pub(in crate::json) mod namespaces;
pub(in crate::json) mod specializations;
mod usages;

use std::{
    collections::{HashMap, HashSet},
    sync::OnceLock,
};

/// Reviewed parameter roles for an executable family. The raw XMI catalog is
/// unchanged: absent source directions are not retroactively filled in.
#[derive(Clone, Copy, Debug)]
#[non_exhaustive]
pub struct OperationExecutionSignature {
    pub declaration: &'static str,
    /// Input declaration IDs in invocation argument order (not XMI order).
    pub inputs: &'static [&'static str],
    pub result: &'static str,
}

/// An audited signature does not imply every receiver override is executable.
/// Invocation resolves the effective declaration and refuses unimplemented
/// overrides, even when a less-specific declaration has an implementation.
pub fn operation_execution_signature(id: &str) -> Option<&'static OperationExecutionSignature> {
    SIGNATURES
        .iter()
        .find(|signature| signature.declaration == id)
}
static SIGNATURES: &[OperationExecutionSignature] = &[
    OperationExecutionSignature {
        declaration: "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean",
        inputs: &[
            "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean-excluded",
            "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean-isRecursive",
            "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean-includeAll",
        ],
        result: "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean",
        inputs: &[
            "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean-excludedNamespaces",
            "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean-excludedTypes",
            "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean-excludeImplied",
        ],
        result: "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-inheritableMemberships_Namespace_Type_Boolean",
        inputs: &[
            "Core-Types-Type-inheritableMemberships_Namespace_Type_Boolean-excludedNamespaces",
            "Core-Types-Type-inheritableMemberships_Namespace_Type_Boolean-excludedTypes",
            "Core-Types-Type-inheritableMemberships_Namespace_Type_Boolean-excludeImplied",
        ],
        result: "Core-Types-Type-inheritableMemberships_Namespace_Type_Boolean-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean",
        inputs: &[
            "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean-excludedNamespaces",
            "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean-excludedTypes",
            "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean-excludeImplied",
        ],
        result: "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-resolve_String",
        inputs: &["Root-Namespaces-Namespace-resolve_String-qualifiedName"],
        result: "Root-Namespaces-Namespace-resolve_String-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-resolveLocal_String",
        inputs: &["Root-Namespaces-Namespace-resolveLocal_String-name"],
        result: "Root-Namespaces-Namespace-resolveLocal_String-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-resolveGlobal_String",
        inputs: &["Root-Namespaces-Namespace-resolveGlobal_String-qualifiedName"],
        result: "Root-Namespaces-Namespace-resolveGlobal_String-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-resolveVisible_String",
        inputs: &["Root-Namespaces-Namespace-resolveVisible_String-name"],
        result: "Root-Namespaces-Namespace-resolveVisible_String-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-NamespaceImport-importedMemberships_Namespace",
        inputs: &["Root-Namespaces-NamespaceImport-importedMemberships_Namespace-excluded"],
        result: "Root-Namespaces-NamespaceImport-importedMemberships_Namespace-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-MembershipImport-importedMemberships_Namespace",
        inputs: &["Root-Namespaces-MembershipImport-importedMemberships_Namespace-excluded"],
        result: "Root-Namespaces-MembershipImport-importedMemberships_Namespace-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-qualificationOf_String",
        inputs: &["Root-Namespaces-Namespace-qualificationOf_String-qualifiedName"],
        result: "Root-Namespaces-Namespace-qualificationOf_String-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-unqualifiedNameOf_String",
        inputs: &["Root-Namespaces-Namespace-unqualifiedNameOf_String-qualifiedName"],
        result: "Root-Namespaces-Namespace-unqualifiedNameOf_String-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-membershipsOfVisibility_VisibilityKind_Namespace",
        inputs: &[
            "Root-Namespaces-Namespace-membershipsOfVisibility_VisibilityKind_Namespace-visibility",
            "Root-Namespaces-Namespace-membershipsOfVisibility_VisibilityKind_Namespace-excluded",
        ],
        result: "Root-Namespaces-Namespace-membershipsOfVisibility_VisibilityKind_Namespace-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean",
        inputs: &[
            "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean-excluded",
            "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean-isRecursive",
            "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean-includeAll",
        ],
        result: "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-importedMemberships_Namespace",
        inputs: &["Root-Namespaces-Namespace-importedMemberships_Namespace-excluded"],
        result: "Root-Namespaces-Namespace-importedMemberships_Namespace-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-visibilityOf_Membership",
        inputs: &["Root-Namespaces-Namespace-visibilityOf_Membership-mem"],
        result: "Root-Namespaces-Namespace-visibilityOf_Membership-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Namespace-namesOf_Element",
        inputs: &["Root-Namespaces-Namespace-namesOf_Element-element"],
        result: "Root-Namespaces-Namespace-namesOf_Element-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Packages-Package-importedMemberships_Namespace",
        inputs: &["Kernel-Packages-Package-importedMemberships_Namespace-excluded"],
        result: "Kernel-Packages-Package-importedMemberships_Namespace-",
    },
    OperationExecutionSignature {
        declaration: "Root-Elements-Element-effectiveName_",
        inputs: &[],
        result: "Root-Elements-Element-effectiveName_-",
    },
    OperationExecutionSignature {
        declaration: "Root-Elements-Element-effectiveShortName_",
        inputs: &[],
        result: "Root-Elements-Element-effectiveShortName_-",
    },
    OperationExecutionSignature {
        declaration: "Root-Elements-Element-libraryNamespace_",
        inputs: &[],
        result: "Root-Elements-Element-libraryNamespace_-",
    },
    OperationExecutionSignature {
        declaration: "Root-Elements-Relationship-libraryNamespace_",
        inputs: &[],
        result: "Root-Elements-Relationship-libraryNamespace_-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Packages-LibraryPackage-libraryNamespace_",
        inputs: &[],
        result: "Kernel-Packages-LibraryPackage-libraryNamespace_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-effectiveName_",
        inputs: &[],
        result: "Core-Features-Feature-effectiveName_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-effectiveShortName_",
        inputs: &[],
        result: "Core-Features-Feature-effectiveShortName_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Ports-ConjugatedPortDefinition-effectiveName_",
        inputs: &[],
        result: "Systems-Ports-ConjugatedPortDefinition-effectiveName_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-supertypes_Boolean",
        inputs: &["Core-Types-Type-supertypes_Boolean-excludeImplied"],
        result: "Core-Types-Type-supertypes_Boolean-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-supertypes_Boolean",
        inputs: &["Core-Features-Feature-supertypes_Boolean-excludeImplied"],
        result: "Core-Features-Feature-supertypes_Boolean-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-allSupertypes_",
        inputs: &[],
        result: "Core-Types-Type-allSupertypes_-result",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-specializes_Type",
        inputs: &["Core-Types-Type-specializes_Type-supertype"],
        result: "Core-Types-Type-specializes_Type-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-isCompatibleWith_Type",
        inputs: &["Core-Types-Type-isCompatibleWith_Type-otherType"],
        result: "Core-Types-Type-isCompatibleWith_Type-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-isCompatibleWith_Type",
        inputs: &["Core-Features-Feature-isCompatibleWith_Type-otherType"],
        result: "Core-Features-Feature-isCompatibleWith_Type-",
    },
    OperationExecutionSignature {
        declaration: "Root-Elements-Element-escapedName_",
        inputs: &[],
        result: "Root-Elements-Element-escapedName_-",
    },
    OperationExecutionSignature {
        declaration: "Root-Elements-Element-path_",
        inputs: &[],
        result: "Root-Elements-Element-path_-",
    },
    OperationExecutionSignature {
        declaration: "Root-Elements-Relationship-path_",
        inputs: &[],
        result: "Root-Elements-Relationship-path_-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-OwningMembership-path_",
        inputs: &[],
        result: "Root-Namespaces-OwningMembership-path_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-namingFeature_",
        inputs: &[],
        result: "Core-Features-Feature-namingFeature_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-DefinitionAndUsage-Usage-namingFeature_",
        inputs: &[],
        result: "Systems-DefinitionAndUsage-Usage-namingFeature_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-DefinitionAndUsage-ReferenceUsage-namingFeature_",
        inputs: &[],
        result: "Systems-DefinitionAndUsage-ReferenceUsage-namingFeature_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Constraints-ConstraintUsage-namingFeature_",
        inputs: &[],
        result: "Systems-Constraints-ConstraintUsage-namingFeature_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Actions-PerformActionUsage-namingFeature_",
        inputs: &[],
        result: "Systems-Actions-PerformActionUsage-namingFeature_-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Membership-isDistinguishableFrom_Membership",
        inputs: &["Root-Namespaces-Membership-isDistinguishableFrom_Membership-other"],
        result: "Root-Namespaces-Membership-isDistinguishableFrom_Membership-",
    },
    OperationExecutionSignature {
        declaration: "Root-Namespaces-Import-importedMemberships_Namespace",
        inputs: &["Root-Namespaces-Import-importedMemberships_Namespace-excluded"],
        result: "Root-Namespaces-Import-importedMemberships_Namespace-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-allRedefinedFeatures_",
        inputs: &[],
        result: "Core-Features-Feature-allRedefinedFeatures_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-allRedefinedFeaturesOf_Membership",
        inputs: &["Core-Types-Type-allRedefinedFeaturesOf_Membership-membership"],
        result: "Core-Types-Type-allRedefinedFeaturesOf_Membership-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-removeRedefinedFeatures_Membership",
        inputs: &["Core-Types-Type-removeRedefinedFeatures_Membership-memberships"],
        result: "Core-Types-Type-removeRedefinedFeatures_Membership-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Packages-Package-includeAsMember_Element",
        inputs: &["Kernel-Packages-Package-includeAsMember_Element-element"],
        result: "Kernel-Packages-Package-includeAsMember_Element-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Views-ViewUsage-includeAsExposed_Element",
        inputs: &["Systems-Views-ViewUsage-includeAsExposed_Element-element"],
        result: "Systems-Views-ViewUsage-includeAsExposed_Element-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-directionOf_Feature",
        inputs: &["Core-Types-Type-directionOf_Feature-feature"],
        result: "Core-Types-Type-directionOf_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-directionOfExcluding_Feature_Type",
        inputs: &[
            "Core-Types-Type-directionOfExcluding_Feature_Type-feature",
            "Core-Types-Type-directionOfExcluding_Feature_Type-excluded",
        ],
        result: "Core-Types-Type-directionOfExcluding_Feature_Type-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-directionFor_Type",
        inputs: &["Core-Features-Feature-directionFor_Type-type"],
        result: "Core-Features-Feature-directionFor_Type-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Behaviors-ParameterMembership-parameterDirection_",
        inputs: &[],
        result: "Kernel-Behaviors-ParameterMembership-parameterDirection_-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-LiteralExpression-evaluate_Element",
        inputs: &["Kernel-Expressions-LiteralExpression-evaluate_Element-target"],
        result: "Kernel-Expressions-LiteralExpression-evaluate_Element-result",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-LiteralExpression-modelLevelEvaluable_Feature",
        inputs: &["Kernel-Expressions-LiteralExpression-modelLevelEvaluable_Feature-visited"],
        result: "Kernel-Expressions-LiteralExpression-modelLevelEvaluable_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-MetadataAccessExpression-modelLevelEvaluable_Feature",
        inputs: &[
            "Kernel-Expressions-MetadataAccessExpression-modelLevelEvaluable_Feature-visited",
        ],
        result: "Kernel-Expressions-MetadataAccessExpression-modelLevelEvaluable_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-NullExpression-evaluate_Element",
        inputs: &["Kernel-Expressions-NullExpression-evaluate_Element-target"],
        result: "Kernel-Expressions-NullExpression-evaluate_Element-result",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-NullExpression-modelLevelEvaluable_Feature",
        inputs: &["Kernel-Expressions-NullExpression-modelLevelEvaluable_Feature-visited"],
        result: "Kernel-Expressions-NullExpression-modelLevelEvaluable_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Functions-Expression-evaluate_Element",
        inputs: &["Kernel-Functions-Expression-evaluate_Element-target"],
        result: "Kernel-Functions-Expression-evaluate_Element-result",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Functions-Expression-modelLevelEvaluable_Feature",
        inputs: &["Kernel-Functions-Expression-modelLevelEvaluable_Feature-visited"],
        result: "Kernel-Functions-Expression-modelLevelEvaluable_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Functions-ReturnParameterMembership-parameterDirection_",
        inputs: &[],
        result: "Kernel-Functions-ReturnParameterMembership-parameterDirection_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Calculations-CalculationUsage-modelLevelEvaluable_Feature",
        inputs: &["Systems-Calculations-CalculationUsage-modelLevelEvaluable_Feature-visited"],
        result: "Systems-Calculations-CalculationUsage-modelLevelEvaluable_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Constraints-ConstraintUsage-modelLevelEvaluable_Feature",
        inputs: &["Systems-Constraints-ConstraintUsage-modelLevelEvaluable_Feature-visited"],
        result: "Systems-Constraints-ConstraintUsage-modelLevelEvaluable_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-canAccess_Feature",
        inputs: &["Core-Features-Feature-canAccess_Feature-feature"],
        result: "Core-Features-Feature-canAccess_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-isFeaturedWithin_Type",
        inputs: &["Core-Features-Feature-isFeaturedWithin_Type-type"],
        result: "Core-Features-Feature-isFeaturedWithin_Type-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-isFeaturingType_Type",
        inputs: &["Core-Features-Feature-isFeaturingType_Type-type"],
        result: "Core-Features-Feature-isFeaturingType_Type-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-ownedCrossFeature_",
        inputs: &[],
        result: "Core-Features-Feature-ownedCrossFeature_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-isOwnedCrossFeature_",
        inputs: &[],
        result: "Core-Features-Feature-isOwnedCrossFeature_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-specializesFromLibrary_String",
        inputs: &["Core-Types-Type-specializesFromLibrary_String-libraryTypeName"],
        result: "Core-Types-Type-specializesFromLibrary_String-",
    },
    OperationExecutionSignature {
        declaration: "Core-Types-Type-multiplicities_",
        inputs: &[],
        result: "Core-Types-Type-multiplicities_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-redefines_Feature",
        inputs: &["Core-Features-Feature-redefines_Feature-redefinedFeature"],
        result: "Core-Features-Feature-redefines_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-redefinesFromLibrary_String",
        inputs: &["Core-Features-Feature-redefinesFromLibrary_String-libraryFeatureName"],
        result: "Core-Features-Feature-redefinesFromLibrary_String-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-subsetsChain_Feature_Feature",
        inputs: &[
            "Core-Features-Feature-subsetsChain_Feature_Feature-first",
            "Core-Features-Feature-subsetsChain_Feature_Feature-second",
        ],
        result: "Core-Features-Feature-subsetsChain_Feature_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-typingFeatures_",
        inputs: &[],
        result: "Core-Features-Feature-typingFeatures_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-isCartesianProduct_",
        inputs: &[],
        result: "Core-Features-Feature-isCartesianProduct_-",
    },
    OperationExecutionSignature {
        declaration: "Core-Features-Feature-asCartesianProduct_",
        inputs: &[],
        result: "Core-Features-Feature-asCartesianProduct_-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-FeatureChainExpression-sourceTargetFeature_",
        inputs: &[],
        result: "Kernel-Expressions-FeatureChainExpression-sourceTargetFeature_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Actions-ActionUsage-isSubactionUsage_",
        inputs: &[],
        result: "Systems-Actions-ActionUsage-isSubactionUsage_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Actions-ActionUsage-inputParameters_",
        inputs: &[],
        result: "Systems-Actions-ActionUsage-inputParameters_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Actions-ActionUsage-inputParameter_Integer",
        inputs: &["Systems-Actions-ActionUsage-inputParameter_Integer-i"],
        result: "Systems-Actions-ActionUsage-inputParameter_Integer-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Actions-ActionUsage-argument_Integer",
        inputs: &["Systems-Actions-ActionUsage-argument_Integer-i"],
        result: "Systems-Actions-ActionUsage-argument_Integer-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Actions-AcceptActionUsage-isTriggerAction_",
        inputs: &[],
        result: "Systems-Actions-AcceptActionUsage-isTriggerAction_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-States-StateUsage-isSubstateUsage_Boolean",
        inputs: &["Systems-States-StateUsage-isSubstateUsage_Boolean-isParallel"],
        result: "Systems-States-StateUsage-isSubstateUsage_Boolean-",
    },
    OperationExecutionSignature {
        declaration: "Systems-States-TransitionUsage-sourceFeature_",
        inputs: &[],
        result: "Systems-States-TransitionUsage-sourceFeature_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-States-TransitionUsage-triggerPayloadParameter_",
        inputs: &[],
        result: "Systems-States-TransitionUsage-triggerPayloadParameter_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-DefinitionAndUsage-Usage-referencedFeatureTarget_",
        inputs: &[],
        result: "Systems-DefinitionAndUsage-Usage-referencedFeatureTarget_-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-FeatureReferenceExpression-evaluate_Element",
        inputs: &["Kernel-Expressions-FeatureReferenceExpression-evaluate_Element-target"],
        result: "Kernel-Expressions-FeatureReferenceExpression-evaluate_Element-result",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-InvocationExpression-evaluate_Element",
        inputs: &["Kernel-Expressions-InvocationExpression-evaluate_Element-target"],
        result: "Kernel-Expressions-InvocationExpression-evaluate_Element-result",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Functions-Expression-checkCondition_Element",
        inputs: &["Kernel-Functions-Expression-checkCondition_Element-target"],
        result: "Kernel-Functions-Expression-checkCondition_Element-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-FeatureReferenceExpression-modelLevelEvaluable_Feature",
        inputs: &[
            "Kernel-Expressions-FeatureReferenceExpression-modelLevelEvaluable_Feature-visited",
        ],
        result: "Kernel-Expressions-FeatureReferenceExpression-modelLevelEvaluable_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-InvocationExpression-modelLevelEvaluable_Feature",
        inputs: &["Kernel-Expressions-InvocationExpression-modelLevelEvaluable_Feature-visited"],
        result: "Kernel-Expressions-InvocationExpression-modelLevelEvaluable_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-ConstructorExpression-modelLevelEvaluable_Feature",
        inputs: &["Kernel-Expressions-ConstructorExpression-modelLevelEvaluable_Feature-visited"],
        result: "Kernel-Expressions-ConstructorExpression-modelLevelEvaluable_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-InstantiationExpression-instantiatedType_",
        inputs: &[],
        result: "Kernel-Expressions-InstantiationExpression-instantiatedType_-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-OperatorExpression-instantiatedType_",
        inputs: &[],
        result: "Kernel-Expressions-OperatorExpression-instantiatedType_-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Actions-TriggerInvocationExpression-instantiatedType_",
        inputs: &[],
        result: "Systems-Actions-TriggerInvocationExpression-instantiatedType_-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Multiplicities-MultiplicityRange-valueOf_Expression",
        inputs: &["Kernel-Multiplicities-MultiplicityRange-valueOf_Expression-bound"],
        result: "Kernel-Multiplicities-MultiplicityRange-valueOf_Expression-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Multiplicities-MultiplicityRange-hasBounds_Integer_UnlimitedNatural",
        inputs: &[
            "Kernel-Multiplicities-MultiplicityRange-hasBounds_Integer_UnlimitedNatural-lower",
            "Kernel-Multiplicities-MultiplicityRange-hasBounds_Integer_UnlimitedNatural-upper",
        ],
        result: "Kernel-Multiplicities-MultiplicityRange-hasBounds_Integer_UnlimitedNatural-",
    },
    OperationExecutionSignature {
        declaration: "Systems-Actions-ControlNode-multiplicityHasBounds_Multiplicity_Integer_UnlimitedNatural",
        inputs: &[
            "Systems-Actions-ControlNode-multiplicityHasBounds_Multiplicity_Integer_UnlimitedNatural-mult",
            "Systems-Actions-ControlNode-multiplicityHasBounds_Multiplicity_Integer_UnlimitedNatural-lower",
            "Systems-Actions-ControlNode-multiplicityHasBounds_Multiplicity_Integer_UnlimitedNatural-upper",
        ],
        result: "Systems-Actions-ControlNode-multiplicityHasBounds_Multiplicity_Integer_UnlimitedNatural-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Metadata-MetadataFeature-evaluateFeature_Feature",
        inputs: &["Kernel-Metadata-MetadataFeature-evaluateFeature_Feature-baseFeature"],
        result: "Kernel-Metadata-MetadataFeature-evaluateFeature_Feature-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Metadata-MetadataFeature-isSemantic_",
        inputs: &[],
        result: "Kernel-Metadata-MetadataFeature-isSemantic_-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Metadata-MetadataFeature-isSyntactic_",
        inputs: &[],
        result: "Kernel-Metadata-MetadataFeature-isSyntactic_-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Metadata-MetadataFeature-syntaxElement_",
        inputs: &[],
        result: "Kernel-Metadata-MetadataFeature-syntaxElement_-",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-MetadataAccessExpression-evaluate_Element",
        inputs: &["Kernel-Expressions-MetadataAccessExpression-evaluate_Element-target"],
        result: "Kernel-Expressions-MetadataAccessExpression-evaluate_Element-result",
    },
    OperationExecutionSignature {
        declaration: "Kernel-Expressions-MetadataAccessExpression-metaclassFeature_",
        inputs: &[],
        result: "Kernel-Expressions-MetadataAccessExpression-metaclassFeature_-",
    },
];

#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum OperationArgumentIssue {
    WrongShape,
    InvalidSyntax,
    InvalidEnumValue,
    NullNotAllowed,
    InvalidElement,
    UnverifiedReference,
    WrongMetaclass {
        expected: &'static str,
        actual: &'static str,
    },
    DuplicateIdentity,
    Multiplicity,
}
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum OperationError {
    UnknownOperation,
    InvalidReceiver,
    WrongReceiver {
        expected: &'static str,
        actual: &'static str,
    },
    AmbiguousRedefinition,
    Unsupported {
        effective: &'static str,
    },
    /// The operation exists but this input configuration is not yet checked.
    UnsupportedConfiguration {
        effective: &'static str,
        parameter: &'static str,
    },
    /// Required graph evidence or unambiguous collection ordering is unavailable.
    /// `blocker` is the element the evidence stopped at, when the body can
    /// name one: an Import whose target does not resolve, a namespace or
    /// type whose membership provider is not certified, a member whose
    /// name cannot be derived, the second of two global bindings. It is a
    /// handle of the session that answered; `element_id` names it.
    Incomplete {
        effective: &'static str,
        blocker: Option<ElementRef>,
    },
    WorkLimit {
        effective: &'static str,
    },
    ArgumentCount {
        expected: usize,
        actual: usize,
    },
    InvalidArgument {
        index: usize,
        parameter: &'static str,
        issue: OperationArgumentIssue,
    },
}
impl std::fmt::Display for OperationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::UnknownOperation => f.write_str("unknown operation declaration identity"),
            Self::InvalidReceiver => f.write_str("invalid operation receiver"),
            Self::WrongReceiver { expected, actual } => {
                write!(f, "operation requires {expected}, got {actual}")
            }
            Self::AmbiguousRedefinition => {
                f.write_str("operation has incomparable applicable redefinitions")
            }
            Self::Unsupported { effective } => {
                write!(f, "operation body is not implemented: {effective}")
            }
            Self::UnsupportedConfiguration {
                effective,
                parameter,
            } => write!(f, "unsupported configuration of {effective}: {parameter}"),
            Self::Incomplete {
                effective,
                blocker: None,
            } => write!(f, "incomplete operation evidence: {effective}"),
            Self::Incomplete {
                effective,
                blocker: Some(blocker),
            } => write!(
                f,
                "incomplete operation evidence: {effective}; blocked at element {}",
                blocker.0
            ),
            Self::WorkLimit { effective } => write!(f, "operation work limit reached: {effective}"),
            Self::ArgumentCount { expected, actual } => {
                write!(f, "operation requires {expected} arguments, got {actual}")
            }
            Self::InvalidArgument {
                index,
                parameter,
                issue,
            } => write!(f, "invalid argument {index} for {parameter}: {issue:?}"),
        }
    }
}
impl std::error::Error for OperationError {}

#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct OperationResult {
    pub requested: &'static str,
    pub effective: &'static str,
    pub value: DerivedValue,
}

/// Build the normative redefinition closure once, independently of model state.
/// Dispatch by identity, not coincidental operation spelling or class depth.
struct Dispatch {
    descendants: HashMap<&'static str, Vec<&'static OperationSpec>>,
    ancestors: HashMap<&'static str, HashSet<&'static str>>,
}
impl Dispatch {
    fn catalog() -> &'static Self {
        static DISPATCH: OnceLock<Dispatch> = OnceLock::new();
        DISPATCH.get_or_init(|| {
            let mut ancestors = HashMap::new();
            for operation in metamodel::operations() {
                let mut found = HashSet::new();
                let mut stack = operation.redefines.to_vec();
                while let Some(id) = stack.pop() {
                    if found.insert(id) {
                        if let Some(parent) = metamodel::operation(id) {
                            stack.extend_from_slice(parent.redefines);
                        }
                    }
                }
                ancestors.insert(operation.id, found);
            }
            let mut descendants: HashMap<_, Vec<_>> = HashMap::new();
            for operation in metamodel::operations() {
                descendants.entry(operation.id).or_default().push(operation);
                for &ancestor in &ancestors[operation.id] {
                    descendants.entry(ancestor).or_default().push(operation);
                }
            }
            Self {
                descendants,
                ancestors,
            }
        })
    }
    fn effective(
        &self,
        requested: &'static OperationSpec,
        receiver: &str,
    ) -> Result<&'static OperationSpec, OperationError> {
        let applicable: Vec<_> = self.descendants[requested.id]
            .iter()
            .copied()
            .filter(|operation| conforms(receiver, operation.declaring_metaclass))
            .collect();
        let mut surviving = applicable.iter().copied().filter(|operation| {
            !applicable.iter().any(|other| {
                other.id != operation.id && self.ancestors[other.id].contains(operation.id)
            })
        });
        let effective = surviving
            .next()
            .ok_or(OperationError::AmbiguousRedefinition)?;
        if surviving.next().is_some() {
            return Err(OperationError::AmbiguousRedefinition);
        }
        Ok(effective)
    }
}

#[derive(Clone, Copy)]
enum Handler {
    Namespace(namespaces::Body),
    Elements(elements::Body),
    Features(features::Body),
    Evaluation(evaluation::Body),
    Specialization(specializations::Body),
    Usages(usages::Body),
    DeclaredName { key: &'static str, feature: bool },
    In,
    Out,
    SelfSequence,
    EmptySequence,
    True,
    False,
    Supertypes,
    AllSupertypes,
    Specializes,
    CompatibleWith { feature: bool },
    LibraryNamespace,
    ConjugatedName,
}
fn handler(id: &str) -> Option<Handler> {
    use Handler::*;
    Some(match id {
        "Root-Namespaces-Namespace-resolve_String" => Namespace(namespaces::Body::Resolve),
        "Root-Namespaces-Namespace-resolveLocal_String" => {
            Namespace(namespaces::Body::ResolveLocal)
        }
        "Root-Namespaces-Namespace-resolveGlobal_String" => {
            Namespace(namespaces::Body::ResolveGlobal)
        }
        "Root-Namespaces-Namespace-qualificationOf_String" => {
            Namespace(namespaces::Body::Qualification)
        }
        "Root-Namespaces-Namespace-unqualifiedNameOf_String" => {
            Namespace(namespaces::Body::Unqualified)
        }
        "Root-Namespaces-Namespace-membershipsOfVisibility_VisibilityKind_Namespace" => {
            Namespace(namespaces::Body::Memberships)
        }
        "Root-Namespaces-Import-importedMemberships_Namespace"
        | "Root-Namespaces-NamespaceImport-importedMemberships_Namespace"
        | "Root-Namespaces-MembershipImport-importedMemberships_Namespace" => {
            Namespace(namespaces::Body::Import)
        }
        "Root-Elements-Element-escapedName_" => Elements(elements::Body::EscapedName),
        "Root-Elements-Element-path_"
        | "Root-Elements-Relationship-path_"
        | "Root-Namespaces-OwningMembership-path_" => Elements(elements::Body::Path),
        "Core-Features-Feature-namingFeature_"
        | "Systems-DefinitionAndUsage-Usage-namingFeature_"
        | "Systems-DefinitionAndUsage-ReferenceUsage-namingFeature_"
        | "Systems-Constraints-ConstraintUsage-namingFeature_"
        | "Systems-Actions-PerformActionUsage-namingFeature_" => {
            Elements(elements::Body::NamingFeature)
        }
        "Root-Namespaces-Membership-isDistinguishableFrom_Membership" => {
            Elements(elements::Body::Distinguishable)
        }
        "Core-Features-Feature-allRedefinedFeatures_" => {
            Elements(elements::Body::AllRedefinedFeatures)
        }
        "Core-Types-Type-allRedefinedFeaturesOf_Membership" => {
            Elements(elements::Body::AllRedefinedFeaturesOf)
        }
        "Core-Types-Type-removeRedefinedFeatures_Membership" => {
            Elements(elements::Body::RemoveRedefinedFeatures)
        }
        "Kernel-Packages-Package-includeAsMember_Element" => {
            Elements(elements::Body::IncludeAsMember)
        }
        "Systems-Views-ViewUsage-includeAsExposed_Element" => {
            Elements(elements::Body::IncludeAsExposed)
        }
        "Core-Types-Type-directionOf_Feature" => Elements(elements::Body::DirectionOf),
        "Core-Types-Type-directionOfExcluding_Feature_Type" => {
            Elements(elements::Body::DirectionOfExcluding)
        }
        "Core-Features-Feature-directionFor_Type" => Elements(elements::Body::DirectionFor),
        "Core-Features-Feature-canAccess_Feature" => Features(features::Body::CanAccess),
        "Core-Features-Feature-isFeaturedWithin_Type" => Features(features::Body::IsFeaturedWithin),
        "Core-Features-Feature-isFeaturingType_Type" => Features(features::Body::IsFeaturingType),
        "Core-Features-Feature-ownedCrossFeature_" => Features(features::Body::OwnedCrossFeature),
        "Core-Features-Feature-isOwnedCrossFeature_" => {
            Features(features::Body::IsOwnedCrossFeature)
        }
        "Core-Features-Feature-isCartesianProduct_" => Features(features::Body::IsCartesianProduct),
        "Core-Features-Feature-asCartesianProduct_" => Features(features::Body::AsCartesianProduct),
        "Kernel-Expressions-FeatureChainExpression-sourceTargetFeature_" => {
            Features(features::Body::SourceTargetFeature)
        }
        "Systems-Actions-ActionUsage-isSubactionUsage_" => Usages(usages::Body::IsSubactionUsage),
        "Systems-Actions-ActionUsage-inputParameters_" => Usages(usages::Body::InputParameters),
        "Systems-Actions-ActionUsage-inputParameter_Integer" => {
            Usages(usages::Body::InputParameter)
        }
        "Systems-Actions-ActionUsage-argument_Integer" => Usages(usages::Body::Argument),
        "Systems-Actions-AcceptActionUsage-isTriggerAction_" => {
            Usages(usages::Body::IsTriggerAction)
        }
        "Systems-States-StateUsage-isSubstateUsage_Boolean" => {
            Usages(usages::Body::IsSubstateUsage)
        }
        "Systems-States-TransitionUsage-sourceFeature_" => Usages(usages::Body::SourceFeature),
        "Systems-States-TransitionUsage-triggerPayloadParameter_" => {
            Usages(usages::Body::TriggerPayloadParameter)
        }
        "Systems-DefinitionAndUsage-Usage-referencedFeatureTarget_" => {
            Usages(usages::Body::ReferencedFeatureTarget)
        }
        "Core-Types-Type-specializesFromLibrary_String" => {
            Specialization(specializations::Body::SpecializesFromLibrary)
        }
        "Core-Types-Type-multiplicities_" => Specialization(specializations::Body::Multiplicities),
        "Core-Features-Feature-redefines_Feature" => {
            Specialization(specializations::Body::Redefines)
        }
        "Core-Features-Feature-redefinesFromLibrary_String" => {
            Specialization(specializations::Body::RedefinesFromLibrary)
        }
        "Core-Features-Feature-subsetsChain_Feature_Feature" => {
            Specialization(specializations::Body::SubsetsChain)
        }
        "Core-Features-Feature-typingFeatures_" => {
            Specialization(specializations::Body::TypingFeatures)
        }
        "Root-Namespaces-Namespace-resolveVisible_String" => {
            Namespace(namespaces::Body::ResolveVisible)
        }
        "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean"
        | "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean" => {
            Namespace(namespaces::Body::Visible)
        }
        "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean" => {
            Namespace(namespaces::Body::Inherited)
        }
        "Core-Types-Type-inheritableMemberships_Namespace_Type_Boolean" => {
            Namespace(namespaces::Body::Inheritable)
        }
        "Core-Types-Type-nonPrivateMemberships_Namespace_Type_Boolean" => {
            Namespace(namespaces::Body::NonPrivate)
        }
        "Root-Namespaces-Namespace-importedMemberships_Namespace" => {
            Namespace(namespaces::Body::Imported)
        }
        "Root-Namespaces-Namespace-visibilityOf_Membership" => {
            Namespace(namespaces::Body::Visibility)
        }
        "Root-Namespaces-Namespace-namesOf_Element" => Namespace(namespaces::Body::Names),
        "Kernel-Packages-Package-importedMemberships_Namespace" => {
            Namespace(namespaces::Body::Imported)
        }
        "Root-Elements-Element-effectiveName_" => DeclaredName {
            key: "declaredName",
            feature: false,
        },
        "Root-Elements-Element-effectiveShortName_" => DeclaredName {
            key: "declaredShortName",
            feature: false,
        },
        "Core-Features-Feature-effectiveName_" => DeclaredName {
            key: "declaredName",
            feature: true,
        },
        "Core-Features-Feature-effectiveShortName_" => DeclaredName {
            key: "declaredShortName",
            feature: true,
        },
        "Systems-Ports-ConjugatedPortDefinition-effectiveName_" => ConjugatedName,

        "Core-Types-Type-supertypes_Boolean" | "Core-Features-Feature-supertypes_Boolean" => {
            Supertypes
        }
        "Core-Types-Type-allSupertypes_" => AllSupertypes,
        "Core-Types-Type-specializes_Type" => Specializes,
        "Core-Types-Type-isCompatibleWith_Type" => CompatibleWith { feature: false },
        "Core-Features-Feature-isCompatibleWith_Type" => CompatibleWith { feature: true },
        "Root-Elements-Element-libraryNamespace_"
        | "Root-Elements-Relationship-libraryNamespace_"
        | "Kernel-Packages-LibraryPackage-libraryNamespace_" => LibraryNamespace,
        "Kernel-Behaviors-ParameterMembership-parameterDirection_" => In,
        "Kernel-Functions-ReturnParameterMembership-parameterDirection_" => Out,
        "Kernel-Functions-Expression-evaluate_Element"
        | "Kernel-Expressions-FeatureReferenceExpression-evaluate_Element"
        | "Kernel-Expressions-InvocationExpression-evaluate_Element" => {
            Evaluation(evaluation::Body::Evaluate)
        }
        "Kernel-Functions-Expression-checkCondition_Element" => {
            Evaluation(evaluation::Body::CheckCondition)
        }
        "Kernel-Functions-Expression-modelLevelEvaluable_Feature"
        | "Kernel-Expressions-FeatureReferenceExpression-modelLevelEvaluable_Feature"
        | "Kernel-Expressions-InvocationExpression-modelLevelEvaluable_Feature"
        | "Kernel-Expressions-ConstructorExpression-modelLevelEvaluable_Feature" => {
            Evaluation(evaluation::Body::ModelLevelEvaluable)
        }
        "Kernel-Expressions-InstantiationExpression-instantiatedType_" => {
            Evaluation(evaluation::Body::InstantiatedType)
        }
        "Kernel-Expressions-OperatorExpression-instantiatedType_" => {
            Evaluation(evaluation::Body::OperatorInstantiatedType)
        }
        "Systems-Actions-TriggerInvocationExpression-instantiatedType_" => {
            Evaluation(evaluation::Body::TriggerInstantiatedType)
        }
        "Kernel-Multiplicities-MultiplicityRange-valueOf_Expression" => {
            Evaluation(evaluation::Body::ValueOf)
        }
        "Kernel-Multiplicities-MultiplicityRange-hasBounds_Integer_UnlimitedNatural" => {
            Evaluation(evaluation::Body::HasBounds)
        }
        "Systems-Actions-ControlNode-multiplicityHasBounds_Multiplicity_Integer_UnlimitedNatural" => {
            Evaluation(evaluation::Body::MultiplicityHasBounds)
        }
        "Kernel-Metadata-MetadataFeature-evaluateFeature_Feature" => {
            Evaluation(evaluation::Body::EvaluateFeature)
        }
        "Kernel-Metadata-MetadataFeature-isSemantic_" => Evaluation(evaluation::Body::IsSemantic),
        "Kernel-Metadata-MetadataFeature-isSyntactic_" => Evaluation(evaluation::Body::IsSyntactic),
        "Kernel-Metadata-MetadataFeature-syntaxElement_" => {
            Evaluation(evaluation::Body::SyntaxElement)
        }
        "Kernel-Expressions-MetadataAccessExpression-evaluate_Element" => {
            Evaluation(evaluation::Body::MetadataEvaluate)
        }
        "Kernel-Expressions-MetadataAccessExpression-metaclassFeature_" => {
            Evaluation(evaluation::Body::MetaclassFeature)
        }
        "Kernel-Expressions-LiteralExpression-evaluate_Element" => SelfSequence,
        "Kernel-Expressions-NullExpression-evaluate_Element" => EmptySequence,
        "Kernel-Expressions-LiteralExpression-modelLevelEvaluable_Feature"
        | "Kernel-Expressions-NullExpression-modelLevelEvaluable_Feature"
        | "Kernel-Expressions-MetadataAccessExpression-modelLevelEvaluable_Feature" => True,
        "Systems-Calculations-CalculationUsage-modelLevelEvaluable_Feature"
        | "Systems-Constraints-ConstraintUsage-modelLevelEvaluable_Feature" => False,
        _ => return None,
    })
}
/// `Element::effectiveName()` / `effectiveShortName()` and their Feature
/// overrides. An Element answers its declaration. A Feature declaring
/// either name answers its declarations too; one declaring neither takes
/// both names from its naming feature (KerML 8.3.3.3.4), through the same
/// derivation the `name` and `shortName` properties read — and refuses
/// where that derivation meets a naming feature it cannot identify or
/// name: an unresolved redefinition target, or an element outside the
/// model that no library name table names.
fn declared_name(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    key: &'static str,
    feature: bool,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    *steps = steps.saturating_add(4);
    let props = &r.b.elements[receiver.0].props;
    let mut declares = false;
    for name in ["declaredName", "declaredShortName"] {
        if let Some(value) = props.get(name) {
            if value.as_str().is_some() {
                declares = true;
            } else if !value.is_null() {
                return Err(OperationError::Incomplete {
                    effective,
                    blocker: Some(receiver),
                });
            }
        }
    }
    let value = if feature && !declares {
        // One naming walk per feature, memoized across the model's names;
        // charge it as a bounded read rather than per step it takes.
        *steps = steps.saturating_add(8);
        let derived = if key == "declaredName" {
            r.checked_effective_name_of(receiver.0)
        } else {
            r.checked_effective_short_name_of(receiver.0)
        };
        derived.ok_or(OperationError::Incomplete {
            effective,
            blocker: Some(receiver),
        })?
    } else {
        props.get(key).and_then(|v| v.as_str()).map(str::to_owned)
    };
    *steps = steps.saturating_add(value.as_deref().map_or(0, str::len));
    if *steps > crate::eval::MAX_STEPS {
        return Err(OperationError::WorkLimit { effective });
    }
    Ok(value.map_or(DerivedValue::Null, DerivedValue::Str))
}
/// `ConjugatedPortDefinition::effectiveName()`: the original port
/// definition's `name` with `~` prepended, or null when that name is null.
fn conjugated_name(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let incomplete = || OperationError::Incomplete {
        effective,
        blocker: Some(receiver),
    };
    let relationships = r.b.elements[receiver.0].owned_relationships.to_vec();
    *steps = steps.saturating_add(relationships.len().saturating_add(8));
    if *steps > crate::eval::MAX_STEPS {
        return Err(OperationError::WorkLimit { effective });
    }
    let mut original = None;
    for relationship in relationships {
        let relation = &r.b.elements[relationship];
        if !conforms(relation.ty, "Conjugation") {
            continue;
        }
        let id = relation
            .props
            .get("originalPortDefinition")
            .or_else(|| relation.props.get("originalType"))
            .and_then(|v| v.as_reference())
            .ok_or_else(incomplete)?;
        if original.replace(id).is_some() {
            return Err(incomplete());
        }
    }
    let id = original.ok_or_else(incomplete)?;
    r.ensure_by_id();
    let original = r.by_id.get(&id).copied().ok_or_else(incomplete)?;
    match r.checked_effective_name_of(original) {
        Some(Some(name)) => {
            *steps = steps.saturating_add(name.len());
            if *steps > crate::eval::MAX_STEPS {
                return Err(OperationError::WorkLimit { effective });
            }
            Ok(DerivedValue::Str(format!("~{name}")))
        }
        Some(None) => Ok(DerivedValue::Null),
        None => Err(incomplete()),
    }
}
/// Reuse the name bodies under a caller's cumulative allowance. Namespace
/// queries cannot restart an independent allowance for every Membership name.
fn checked_name(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    declaration: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    *steps = steps.saturating_add(metamodel::operations().len().saturating_mul(4));
    if *steps > crate::eval::MAX_STEPS {
        return Err(OperationError::WorkLimit {
            effective: declaration,
        });
    }
    let requested = metamodel::operation(declaration).expect("declared name operation");
    let effective = Dispatch::catalog().effective(requested, r.element_type(receiver))?;
    match handler(effective.id) {
        Some(Handler::DeclaredName { key, feature }) => {
            declared_name(r, receiver, effective.id, key, feature, steps)
        }
        Some(Handler::ConjugatedName) => conjugated_name(r, receiver, effective.id, steps),
        _ => Err(OperationError::Incomplete {
            effective: effective.id,
            blocker: Some(receiver),
        }),
    }
}

pub(super) fn argument_element(argument: &DerivedValue) -> usize {
    match argument {
        DerivedValue::Element(e) | DerivedValue::Reference(Reference::Element(e)) => e.0,
        _ => unreachable!("validated scalar element argument"),
    }
}
pub(super) fn references(elements: Vec<usize>) -> DerivedValue {
    DerivedValue::References(
        elements
            .into_iter()
            .map(|e| Reference::Element(ElementRef(e)))
            .collect(),
    )
}
fn work_limit(steps: &usize, effective: &'static str) -> Result<(), OperationError> {
    if *steps > crate::eval::MAX_STEPS {
        Err(OperationError::WorkLimit { effective })
    } else {
        Ok(())
    }
}
/// A checked relation fact as the Boolean an operation returns; an unknown
/// one refuses, naming the receiver.
pub(super) fn relation_fact(
    fact: RelationFact,
    receiver: ElementRef,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    work_limit(steps, effective)?;
    match fact {
        RelationFact::Yes => Ok(DerivedValue::Bool(true)),
        RelationFact::No => Ok(DerivedValue::Bool(false)),
        RelationFact::Unknown => Err(OperationError::Incomplete {
            effective,
            blocker: Some(receiver),
        }),
    }
}
/// `Type::supertypes(false)`: the complete direct bases of `specific`.
fn complete_bases(
    r: &mut ResolvedModel,
    specific: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let bases = TypeRelations::default().complete_direct_bases(&mut r.b, specific, steps);
    work_limit(steps, effective)?;
    bases.ok_or(OperationError::Incomplete {
        effective,
        blocker: Some(ElementRef(specific)),
    })
}
/// `Type::allSupertypes()`: the receiver and every type its complete direct
/// bases reach, each once, nearest first.
fn all_supertypes(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    Ok(references(supertype_closure(
        r, receiver.0, effective, steps,
    )?))
}
/// The receiver and every type its complete direct bases reach, each once,
/// nearest first.
pub(super) fn supertype_closure(
    r: &mut ResolvedModel,
    receiver: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let mut relations = TypeRelations::default();
    let mut order = vec![receiver];
    let mut seen = HashSet::from([receiver]);
    let mut next = 0;
    while let Some(&current) = order.get(next) {
        next += 1;
        *steps = steps.saturating_add(1);
        let bases = relations.complete_direct_bases(&mut r.b, current, steps);
        work_limit(steps, effective)?;
        let bases = bases.ok_or(OperationError::Incomplete {
            effective,
            blocker: Some(ElementRef(current)),
        })?;
        for base in bases {
            if seen.insert(base) {
                order.push(base);
            }
        }
    }
    Ok(order)
}
impl ResolvedModel {
    /// Invoke a supported normative operation by its declaration identity.
    /// Virtual redefinitions are resolved before execution; unsupported and
    /// incomparable overrides never fall back to a base implementation.
    ///
    /// Arguments follow the audited signature's input order. Collection-valued
    /// parameters require Elements/References even when empty; scalar element
    /// parameters require Element/Reference. In-model references are checked
    /// against parameter metaclasses and multiplicities. External/unresolved
    /// references cannot establish the checked argument contract.
    ///
    /// Literal evaluate returns a References sequence containing the literal ELEMENT;
    /// NullExpression evaluate returns an empty sequence. These operations do
    /// not evaluate to Rust scalar values, create result features, materialize
    /// implied relationships, initialize semantic caches, or hydrate libraries.
    /// supertypes admits excludeImplied=true and either flag for a conjugated
    /// receiver, using the shared
    /// checked stored endpoint/carrier provider. Missing endpoints, malformed
    /// aliases and duplicate projection/append ordering return Incomplete;
    /// ordinary excludeImplied=false returns UnsupportedConfiguration. Graph reads may
    /// initialize identity indexes; constant handlers do not mutate the model.
    /// libraryNamespace walks the ownership tree up to the library package
    /// that owns the receiver, as `isLibraryElement` does, and answers null
    /// outside a library package.
    /// Effective-name handlers read Element declarations; a Feature declaring
    /// neither name takes both from its naming feature through the `name`
    /// derivation, refusing where that derivation meets a naming feature it
    /// cannot identify or name; a conjugated port definition prepends `~` to
    /// its original's name.
    pub fn invoke_operation(
        &mut self,
        receiver: ElementRef,
        declaration: &str,
        arguments: &[DerivedValue],
    ) -> Result<OperationResult, OperationError> {
        let requested =
            metamodel::operation(declaration).ok_or(OperationError::UnknownOperation)?;
        let element = self
            .b
            .elements
            .get(receiver.0)
            .ok_or(OperationError::InvalidReceiver)?;
        if !conforms(element.ty, requested.declaring_metaclass) {
            return Err(OperationError::WrongReceiver {
                expected: requested.declaring_metaclass,
                actual: element.ty,
            });
        }
        let effective = Dispatch::catalog().effective(requested, element.ty)?;
        let handler = handler(effective.id).ok_or(OperationError::Unsupported {
            effective: effective.id,
        })?;
        let signature = operation_execution_signature(effective.id).expect("implemented signature");
        if arguments.len() != signature.inputs.len() {
            return Err(OperationError::ArgumentCount {
                expected: signature.inputs.len(),
                actual: arguments.len(),
            });
        }
        let mut steps = 0usize;
        for (index, (argument, &parameter)) in arguments.iter().zip(signature.inputs).enumerate() {
            // Bound validation before walking or allocating identity sets for
            // collection arguments, even when the selected body ignores them.
            let amount = match argument {
                DerivedValue::Elements(v) => v.len().saturating_mul(4),
                DerivedValue::References(v) => v.len().saturating_mul(4),
                DerivedValue::Strings(v) | DerivedValue::Literals(v) => v.len(),
                DerivedValue::Str(v) | DerivedValue::Literal(v) => v.len(),
                _ => 1,
            };
            steps = steps.saturating_add(amount).saturating_add(1);
            if steps > crate::eval::MAX_STEPS {
                return Err(OperationError::WorkLimit {
                    effective: effective.id,
                });
            }
            let spec = effective
                .parameters
                .iter()
                .find(|spec| spec.id == parameter)
                .expect("audited parameter identity");
            self.operation_argument(argument, spec).map_err(|issue| {
                OperationError::InvalidArgument {
                    index,
                    parameter,
                    issue,
                }
            })?;
        }
        let value = match handler {
            Handler::Namespace(body) => namespaces::invoke(
                self,
                receiver,
                effective.id,
                signature,
                arguments,
                body,
                steps,
            )?,
            Handler::Elements(body) => elements::invoke(
                self,
                receiver,
                effective.id,
                signature,
                arguments,
                body,
                steps,
            )?,
            Handler::DeclaredName { key, feature } => {
                declared_name(self, receiver, effective.id, key, feature, &mut steps)?
            }
            Handler::ConjugatedName => conjugated_name(self, receiver, effective.id, &mut steps)?,

            Handler::In => DerivedValue::Str("in".to_owned()),
            Handler::Out => DerivedValue::Str("out".to_owned()),
            Handler::SelfSequence => DerivedValue::References(vec![Reference::Element(receiver)]),
            Handler::EmptySequence => DerivedValue::References(Vec::new()),
            Handler::True => DerivedValue::Bool(true),
            Handler::False => DerivedValue::Bool(false),
            Handler::LibraryNamespace => match self.library_namespace(receiver) {
                Some(package) => DerivedValue::Reference(Reference::Element(package)),
                None => DerivedValue::Null,
            },
            Handler::Supertypes => {
                let exclude_implied = matches!(arguments.first(), Some(DerivedValue::Bool(true)));
                let targets = if exclude_implied {
                    TypeRelations::default()
                        .checked_supertypes(&mut self.b, receiver.0, true, &mut steps)
                        .map_err(|failure| {
                            if steps > crate::eval::MAX_STEPS {
                                OperationError::WorkLimit {
                                    effective: effective.id,
                                }
                            } else {
                                match failure {
                                    SupertypesFailure::Incomplete => OperationError::Incomplete {
                                        effective: effective.id,
                                        blocker: Some(receiver),
                                    },
                                    SupertypesFailure::UnsupportedConfiguration => {
                                        OperationError::UnsupportedConfiguration {
                                            effective: effective.id,
                                            parameter: signature.inputs[0],
                                        }
                                    }
                                }
                            }
                        })?
                } else {
                    // The complete direct bases: the written specializations,
                    // the implied library and positional ones the planner
                    // certifies, a Feature's final chain target; a conjugated
                    // type's original alone.
                    complete_bases(self, receiver.0, effective.id, &mut steps)?
                };
                references(targets)
            }
            Handler::AllSupertypes => all_supertypes(self, receiver, effective.id, &mut steps)?,
            Handler::Specializes => {
                let general = argument_element(&arguments[0]);
                let fact = TypeRelations::default().specializes(
                    &mut self.b,
                    receiver.0,
                    general,
                    &mut steps,
                );
                relation_fact(fact, receiver, effective.id, &mut steps)?
            }
            Handler::CompatibleWith { feature } => features::compatible_with(
                self,
                receiver,
                argument_element(&arguments[0]),
                feature,
                effective.id,
                &mut steps,
            )?,
            Handler::Features(body) => features::invoke(
                self,
                receiver,
                effective.id,
                signature,
                arguments,
                body,
                steps,
            )?,
            Handler::Evaluation(body) => evaluation::invoke(
                self,
                receiver,
                effective.id,
                signature,
                arguments,
                body,
                steps,
            )?,
            Handler::Specialization(body) => specializations::invoke(
                self,
                receiver,
                effective.id,
                signature,
                arguments,
                body,
                steps,
            )?,
            Handler::Usages(body) => usages::invoke(
                self,
                receiver,
                effective.id,
                signature,
                arguments,
                body,
                steps,
            )?,
        };
        Ok(OperationResult {
            requested: requested.id,
            effective: effective.id,
            value,
        })
    }
    fn operation_argument(
        &self,
        value: &DerivedValue,
        parameter: &ParameterSpec,
    ) -> Result<(), OperationArgumentIssue> {
        use OperationArgumentIssue::*;
        if parameter.target == "String" || parameter.target == "VisibilityKind" {
            return match value {
                DerivedValue::Str(value) => {
                    if parameter.target == "VisibilityKind"
                        && !matches!(value.as_str(), "public" | "protected" | "private")
                    {
                        Err(InvalidEnumValue)
                    } else {
                        Ok(())
                    }
                }
                DerivedValue::Null if parameter.lower == 0 => Ok(()),
                DerivedValue::Null => Err(NullNotAllowed),
                _ => Err(WrongShape),
            };
        }
        if parameter.target == "Boolean" {
            return match value {
                DerivedValue::Bool(_) => Ok(()),
                DerivedValue::Null if parameter.lower == 0 => Ok(()),
                DerivedValue::Null => Err(NullNotAllowed),
                _ => Err(WrongShape),
            };
        }
        if parameter.target == "Integer" || parameter.target == "UnlimitedNatural" {
            return match value {
                DerivedValue::Literal(text) => {
                    let valid = if parameter.target == "Integer" {
                        text.parse::<i128>().is_ok()
                    } else {
                        text == "*" || text.parse::<u128>().is_ok()
                    };
                    if valid { Ok(()) } else { Err(InvalidSyntax) }
                }
                DerivedValue::Null if parameter.lower == 0 => Ok(()),
                DerivedValue::Null => Err(NullNotAllowed),
                _ => Err(WrongShape),
            };
        }
        let mut seen = HashSet::new();
        let mut count = 0;
        let mut check = |element: ElementRef| {
            let element_data = self.b.elements.get(element.0).ok_or(InvalidElement)?;
            if !conforms(element_data.ty, parameter.target) {
                return Err(WrongMetaclass {
                    expected: parameter.target,
                    actual: element_data.ty,
                });
            }
            // Session handles are row indices, not semantic identities: an
            // invalid payload/remap can give distinct rows the same UUID.
            // Enforce this argument's uniqueness without scanning the model.
            if parameter.unique && !seen.insert(element_data.id) {
                return Err(DuplicateIdentity);
            }
            count += 1;
            Ok(())
        };
        let mut reference = |reference: &Reference| match reference {
            Reference::Element(element) => check(*element),
            Reference::External(_) | Reference::Unresolved(_) => Err(UnverifiedReference),
        };
        if parameter.upper == Some(1) {
            match value {
                DerivedValue::Element(element) => reference(&Reference::Element(*element))?,
                DerivedValue::Reference(value) => reference(value)?,
                DerivedValue::Null if parameter.lower == 0 => {}
                DerivedValue::Null => return Err(NullNotAllowed),
                _ => return Err(WrongShape),
            }
        } else {
            match value {
                DerivedValue::Elements(elements) => {
                    for &element in elements {
                        reference(&Reference::Element(element))?;
                    }
                }
                DerivedValue::References(elements) => {
                    for element in elements {
                        reference(element)?;
                    }
                }
                _ => return Err(WrongShape),
            }
        }
        if count < parameter.lower || parameter.upper.is_some_and(|upper| count > upper) {
            return Err(Multiplicity);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn audited_roles_preserve_raw_catalog_and_exact_implementation_count() {
        assert_eq!(metamodel::operations().len(), 103);
        assert_eq!(
            metamodel::operations()
                .iter()
                .map(|o| o.name)
                .collect::<HashSet<_>>()
                .len(),
            69
        );
        assert_eq!(
            metamodel::operations()
                .iter()
                .filter(|o| handler(o.id).is_some())
                .count(),
            103
        );
        assert_eq!(SIGNATURES.len(), 103); // every signature has a body
        for signature in SIGNATURES {
            let operation = metamodel::operation(signature.declaration).unwrap();
            let ids: HashSet<_> = signature
                .inputs
                .iter()
                .copied()
                .chain([signature.result])
                .collect();
            assert_eq!(ids.len(), operation.parameters.len());
            assert!(
                operation
                    .parameters
                    .iter()
                    .all(|p| p.direction.is_none() && ids.contains(p.id))
            );
        }
        for (receiver, effective) in [
            (
                "LiteralInteger",
                "Kernel-Expressions-LiteralExpression-modelLevelEvaluable_Feature",
            ),
            (
                "MetadataAccessExpression",
                "Kernel-Expressions-MetadataAccessExpression-modelLevelEvaluable_Feature",
            ),
            (
                "ConstructorExpression",
                "Kernel-Expressions-ConstructorExpression-modelLevelEvaluable_Feature",
            ),
        ] {
            assert_eq!(
                Dispatch::catalog()
                    .effective(
                        metamodel::operation(
                            "Kernel-Functions-Expression-modelLevelEvaluable_Feature"
                        )
                        .unwrap(),
                        receiver
                    )
                    .unwrap()
                    .id,
                effective
            );
        }
    }
    #[test]
    fn library_namespace_is_the_owning_library_package() {
        let mut model = crate::model::Model::new();
        assert!(
            model
                .add_library_source(
                    "lib.kerml",
                    "standard library package L { classifier C { feature f; } }"
                )
                .diagnostics
                .is_empty()
        );
        assert!(
            model
                .add_source("m.kerml", "package P { classifier D; }")
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let ask = |r: &mut ResolvedModel, e: ElementRef| {
            r.invoke_operation(e, "Root-Elements-Element-libraryNamespace_", &[])
                .unwrap()
        };
        let lib = r.resolve_qualified("L").unwrap();
        let found = DerivedValue::Reference(Reference::Element(lib));
        let own = ask(&mut r, lib);
        assert_eq!(own.value, found);
        assert_eq!(
            own.effective,
            "Kernel-Packages-LibraryPackage-libraryNamespace_"
        );
        for name in ["L::C", "L::C::f"] {
            let e = r.resolve_qualified(name).unwrap();
            let answer = ask(&mut r, e);
            assert_eq!(answer.value, found, "{name}");
            assert_eq!(answer.effective, "Root-Elements-Element-libraryNamespace_");
        }
        // A relationship goes up through its carrier: C's owning membership.
        let c = r.resolve_qualified("L::C").unwrap();
        let membership = r.property(c, "owningRelationship").unwrap()["@id"]
            .as_str()
            .unwrap()
            .to_owned();
        let membership = r.element_by_id(&membership).unwrap();
        let answer = ask(&mut r, membership);
        assert_eq!(answer.value, found);
        assert_eq!(
            answer.effective,
            "Root-Elements-Relationship-libraryNamespace_"
        );
        // Outside a library package: none, and isLibraryElement agrees.
        let d = r.resolve_qualified("P::D").unwrap();
        assert_eq!(ask(&mut r, d).value, DerivedValue::Null);
        assert_eq!(
            r.property(d, "isLibraryElement").unwrap(),
            serde_json::json!(false)
        );
        assert_eq!(
            r.property(c, "isLibraryElement").unwrap(),
            serde_json::json!(true)
        );
    }
    #[test]
    fn library_namespace_follows_each_branch_of_the_bodies() {
        let mut model = crate::model::Model::new();
        // A library unit whose root is a plain package: library elements by
        // unit, none by ownership.
        assert!(
            model
                .add_library_source("u.kerml", "package U { classifier E; }")
                .diagnostics
                .is_empty()
        );
        assert!(
            model
                .add_source(
                    "m.kerml",
                    "library package Outer {
                        library package Inner { classifier C; }
                        classifier A; classifier B;
                        specialization S subclassifier B specializes A;
                     }
                     package P { library package L { classifier D; } classifier F; }"
                )
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let ask = |r: &mut ResolvedModel, e: ElementRef| {
            let answer = r
                .invoke_operation(e, "Root-Elements-Element-libraryNamespace_", &[])
                .unwrap();
            (answer.value, answer.effective)
        };
        let found = |e: ElementRef| DerivedValue::Reference(Reference::Element(e));
        let outer = r.resolve_qualified("Outer").unwrap();
        let inner = r.resolve_qualified("Outer::Inner").unwrap();
        // The nearest library package, and a nested one is its own.
        assert_eq!(ask(&mut r, inner).0, found(inner));
        let c = r.resolve_qualified("Outer::Inner::C").unwrap();
        assert_eq!(ask(&mut r, c).0, found(inner));
        // A standalone specialization is a member, so it has no carrier:
        // the Relationship body's second branch, its owning membership.
        let s = r
            .elements_of_metaclass("Subclassification")
            .into_iter()
            .find(|&x| r.element_name(x) == Some("S"))
            .unwrap();
        assert_eq!(
            r.property(s, "owningRelatedElement").unwrap(),
            serde_json::Value::Null
        );
        assert_eq!(
            ask(&mut r, s),
            (found(outer), "Root-Elements-Relationship-libraryNamespace_")
        );
        // A library package inside a plain package: its own and its
        // contents', null for the package around it and the siblings.
        let p = r.resolve_qualified("P").unwrap();
        let l = r.resolve_qualified("P::L").unwrap();
        let d = r.resolve_qualified("P::L::D").unwrap();
        let f = r.resolve_qualified("P::F").unwrap();
        assert_eq!(ask(&mut r, p).0, DerivedValue::Null);
        assert_eq!(ask(&mut r, f).0, DerivedValue::Null);
        assert_eq!(ask(&mut r, l).0, found(l));
        assert_eq!(ask(&mut r, d).0, found(l));
        // From a library unit but under no library package: null, where
        // `is_library_element` says true.
        let e = r.resolve_qualified("U::E").unwrap();
        assert!(r.is_library_element(e));
        assert_eq!(ask(&mut r, e).0, DerivedValue::Null);
        assert_eq!(
            r.property(e, "isLibraryElement").unwrap(),
            serde_json::json!(false)
        );
        // The convenience traversal is the operation's answer.
        for (x, want) in [
            (c, Some(inner)),
            (s, Some(outer)),
            (d, Some(l)),
            (f, None),
            (e, None),
        ] {
            assert_eq!(r.library_namespace(x), want);
        }
    }
    fn name_of(
        r: &mut ResolvedModel,
        e: ElementRef,
        declaration: &str,
    ) -> Result<DerivedValue, OperationError> {
        r.invoke_operation(e, declaration, &[]).map(|v| v.value)
    }
    /// The feature `owner` owns at `index` among its owned features.
    fn owned_feature(r: &mut ResolvedModel, owner: &str, index: usize) -> ElementRef {
        let owner = r.resolve_qualified(owner).unwrap();
        let features: Vec<_> = r.b.elements[owner.0]
            .owned_relationships
            .iter()
            .filter(|&&m| r.b.elements[m].ty == "FeatureMembership")
            .map(|&m| ElementRef(r.b.elements[m].children[0]))
            .collect();
        features[index]
    }
    #[test]
    fn undeclared_feature_names_follow_the_naming_feature_and_refuse_unknown_ones() {
        const NAME: &str = "Core-Features-Feature-effectiveName_";
        const SHORT: &str = "Core-Features-Feature-effectiveShortName_";
        let mut model = crate::model::Model::new();
        // The Type bodies need the kernel's required library roots.
        model.add_library_source(
            "lib.kerml",
            "standard library package Base { classifier Anything; datatype DataValue specializes Anything; feature things : Anything; }
             standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences : Occurrence subsets Base::things; }",
        );
        model.add_source(
            "m.kerml",
            "class A { feature x; feature <s>; feature <t> z; }
             class B specializes A { feature :>> x; feature :>> s; feature w :>> z; }
             class C specializes A { feature :>> missing; }",
        );
        let mut r = ResolvedModel::build(&model);
        let name = |v: &str| DerivedValue::Str(v.to_owned());
        // `:>> x` takes x's name; x declares no short name, so none.
        let bx = owned_feature(&mut r, "B", 0);
        assert_eq!(name_of(&mut r, bx, NAME).unwrap(), name("x"));
        assert_eq!(name_of(&mut r, bx, SHORT).unwrap(), DerivedValue::Null);
        // `<s>` declares a short name only: a null name and the short
        // name, through the redefinition.
        let by = owned_feature(&mut r, "B", 1);
        assert_eq!(name_of(&mut r, by, NAME).unwrap(), DerivedValue::Null);
        assert_eq!(name_of(&mut r, by, SHORT).unwrap(), name("s"));
        // A feature declaring a name declares both: no inherited short name.
        let bw = owned_feature(&mut r, "B", 2);
        assert_eq!(name_of(&mut r, bw, NAME).unwrap(), name("w"));
        assert_eq!(name_of(&mut r, bw, SHORT).unwrap(), DerivedValue::Null);
        // An unresolved redefinition target is a naming feature nobody can
        // name: refused, not null.
        let bm = owned_feature(&mut r, "C", 0);
        for declaration in [NAME, SHORT] {
            assert!(matches!(
                name_of(&mut r, bm, declaration),
                Err(OperationError::Incomplete { effective, .. }) if effective == declaration
            ));
        }
        // The derivation agrees with the `name` property.
        assert_eq!(r.property(bx, "name").unwrap(), serde_json::json!("x"));
        assert_eq!(r.property(by, "shortName").unwrap(), serde_json::json!("s"));
        // Namespace resolution reads those names: the owned redefinition
        // hides the inherited feature, by name.
        let b = r.resolve_qualified("B").unwrap();
        let found = r
            .invoke_operation(
                b,
                "Root-Namespaces-Namespace-resolveLocal_String",
                &[name("x")],
            )
            .unwrap()
            .value;
        assert_eq!(
            found,
            DerivedValue::Reference(Reference::Element(ElementRef(
                r.b.elements[bx.0].owning_relationship.unwrap()
            )))
        );
        assert_eq!(
            r.invoke_operation(
                b,
                "Root-Namespaces-Namespace-namesOf_Element",
                &[DerivedValue::Element(by)]
            )
            .unwrap()
            .value,
            DerivedValue::Strings(vec!["s".into()])
        );
        // A namespace with a member nobody can name cannot answer a name
        // query either: no silent `null` for a possibly matching member.
        let c = r.resolve_qualified("C").unwrap();
        assert!(matches!(
            r.invoke_operation(
                c,
                "Root-Namespaces-Namespace-resolveLocal_String",
                &[name("nothing")],
            ),
            Err(OperationError::Incomplete { .. })
        ));
    }
    #[test]
    fn a_conjugated_port_definition_prepends_a_tilde_to_its_originals_name() {
        let mut model = crate::model::Model::new();
        assert!(
            model
                .add_source("m.sysml", "package P { port def Q { attribute a; } }")
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let conjugate = r.resolve_qualified("P::Q::'~Q'").unwrap();
        assert_eq!(r.element_type(conjugate), "ConjugatedPortDefinition");
        let answer = r
            .invoke_operation(conjugate, "Root-Elements-Element-effectiveName_", &[])
            .unwrap();
        assert_eq!(answer.value, DerivedValue::Str("~Q".into()));
        assert_eq!(
            answer.effective,
            "Systems-Ports-ConjugatedPortDefinition-effectiveName_"
        );
        // The `name` derivation agrees.
        assert_eq!(
            r.property(conjugate, "name").unwrap(),
            serde_json::json!("~Q")
        );
    }
    const KERNEL: &str = "standard library package Base { classifier Anything; datatype DataValue specializes Anything; feature things : Anything; }
         standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences : Occurrence subsets Base::things; }
         standard library package Objects { struct Object specializes Occurrences::Occurrence; feature objects : Object subsets Occurrences::occurrences; }
         standard library package Performances { behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance { return result; } step performances : Performance subsets Occurrences::occurrences; expr evaluations : Evaluation subsets performances; }";
    fn kernel_fixture(source: &str) -> ResolvedModel {
        let mut model = crate::model::Model::new();
        assert!(
            model
                .add_library_source("kernel.kerml", KERNEL)
                .diagnostics
                .is_empty()
        );
        let unit = model.add_source("conformance.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&model)
    }
    fn call(
        r: &mut ResolvedModel,
        receiver: &str,
        operation: &str,
        arguments: &[DerivedValue],
    ) -> Result<DerivedValue, OperationError> {
        let receiver = r.resolve_qualified(receiver).unwrap();
        r.invoke_operation(receiver, operation, arguments)
            .map(|v| v.value)
    }
    fn element(r: &mut ResolvedModel, name: &str) -> DerivedValue {
        DerivedValue::Element(r.resolve_qualified(name).unwrap())
    }
    fn names(r: &mut ResolvedModel, value: DerivedValue) -> Vec<String> {
        let DerivedValue::References(refs) = value else {
            panic!("{value:?}")
        };
        refs.into_iter()
            .map(|reference| match reference {
                Reference::Element(e) => r.element_qualified_name(e).unwrap(),
                other => panic!("{other:?}"),
            })
            .collect()
    }
    const REFLECTION: &str = "standard library package KerML { abstract metaclass Element; metaclass Namespace :> Element; metaclass Type :> Namespace; metaclass Classifier :> Type; metaclass Class :> Classifier; metaclass Feature :> Type; metaclass Package :> Namespace; }
         standard library package Metaobjects { abstract struct Metaobject; abstract struct SemanticMetadata :> Metaobject; }";
    const METADATA_MODEL: &str = "package M {
             metaclass Tag;
             class Other;
             class Rover { @Tag; @KerML::Class; @KerML::Package; @KerML::Class about Other; }
             feature rover : Rover;
             @KerML::Class about Rover, Other;
             feature probe = Rover.metadata;
             feature probeFeature = rover.metadata;
             feature probeOther = Other.metadata;
         }";
    const METADATA_EVALUATE: &str = "Kernel-Expressions-MetadataAccessExpression-evaluate_Element";
    const EVALUATE: &str = "Kernel-Functions-Expression-evaluate_Element";
    const METACLASS_FEATURE: &str = "Kernel-Expressions-MetadataAccessExpression-metaclassFeature_";
    const SYNTAX_ELEMENT: &str = "Kernel-Metadata-MetadataFeature-syntaxElement_";
    fn reflection_fixture(library: &str, source: &str) -> ResolvedModel {
        let mut model = crate::model::Model::new();
        assert!(
            model
                .add_library_source("kernel.kerml", KERNEL)
                .diagnostics
                .is_empty()
        );
        if !library.is_empty() {
            assert!(
                model
                    .add_library_source("reflection.kerml", library)
                    .diagnostics
                    .is_empty()
            );
        }
        let unit = model.add_source("metadata.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&model)
    }
    /// The value expression of a feature: the child of its FeatureValue.
    fn value_expression(r: &mut ResolvedModel, feature: &str) -> ElementRef {
        let feature = r.resolve_qualified(feature).unwrap();
        let value = r.b.elements[feature.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| r.b.elements[rel].ty == "FeatureValue")
            .unwrap();
        let expression = r.b.elements[value].children[0];
        assert_eq!(r.b.elements[expression].ty, "MetadataAccessExpression");
        ElementRef(expression)
    }
    /// The metadata features a namespace owns, in declaration order.
    fn owned_metadata(r: &mut ResolvedModel, owner: &str) -> Vec<ElementRef> {
        let owner = r.resolve_qualified(owner).unwrap();
        r.b.elements[owner.0]
            .owned_relationships
            .iter()
            .flat_map(|&rel| r.b.elements[rel].children.iter().copied())
            .filter(|&e| conforms(r.b.elements[e].ty, "MetadataFeature"))
            .map(ElementRef)
            .collect()
    }
    fn reference(e: ElementRef) -> DerivedValue {
        DerivedValue::Reference(Reference::Element(e))
    }
    /// KerML 8.3.4.8.8: `x.metadata` evaluates to the metadata features
    /// `x` owns that annotate it, then its metaclass feature, answered by
    /// the reflective metaclass that types it; the base `evaluate`
    /// dispatches to the override. KerML 8.3.4.14: a syntactic metadata
    /// feature's syntax element is the one element it annotates when
    /// that element's metaclass is the one named.
    #[test]
    fn metadata_access_reads_annotations_and_the_reflective_metaclass() {
        let mut r = reflection_fixture(REFLECTION, METADATA_MODEL);
        let probe = value_expression(&mut r, "M::probe");
        let class = r.resolve_qualified("KerML::Class").unwrap();
        let feature = r.resolve_qualified("KerML::Feature").unwrap();
        let rover = r.resolve_qualified("M::Rover").unwrap();
        let other = r.resolve_qualified("M::Other").unwrap();
        let rover_metadata = owned_metadata(&mut r, "M::Rover");
        assert_eq!(rover_metadata.len(), 4);
        let package_metadata = owned_metadata(&mut r, "M");
        assert_eq!(package_metadata.len(), 1);
        let target = [DerivedValue::Element(rover)];
        // The one `about Other` in Rover's body annotates Other, not Rover;
        // the package-level one annotates Rover but is not owned by it.
        let expected: Vec<Reference> = rover_metadata[..3]
            .iter()
            .copied()
            .chain([class])
            .map(Reference::Element)
            .collect();
        let result = r
            .invoke_operation(probe, METADATA_EVALUATE, &target)
            .unwrap();
        assert_eq!(result.value, DerivedValue::References(expected.clone()));
        let through_base = r.invoke_operation(probe, EVALUATE, &target).unwrap();
        assert_eq!(through_base.effective, METADATA_EVALUATE);
        assert_eq!(through_base.value, DerivedValue::References(expected));
        assert_eq!(
            r.invoke_operation(probe, METACLASS_FEATURE, &[])
                .unwrap()
                .value,
            reference(class)
        );
        // An element without annotations: the metaclass feature alone.
        let probe_feature = value_expression(&mut r, "M::probeFeature");
        assert_eq!(
            r.invoke_operation(probe_feature, METADATA_EVALUATE, &target)
                .unwrap()
                .value,
            DerivedValue::References(vec![Reference::Element(feature)])
        );
        let probe_other = value_expression(&mut r, "M::probeOther");
        assert_eq!(
            r.invoke_operation(probe_other, METADATA_EVALUATE, &target)
                .unwrap()
                .value,
            DerivedValue::References(vec![Reference::Element(class)])
        );
        // syntaxElement: `@KerML::Class` on a class represents the class;
        // `@KerML::Package` on it represents nothing; `@Tag` is not
        // syntactic; `about Other` represents Other; two targets refuse.
        // A model metaclass specializing a reflective one is the full
        // library's case (`evaluation_operations.rs`): here its feature's
        // closure is uncertified, like `@Tag`'s.
        let [tag, class_on_rover, package_on_rover, about_other] = rover_metadata[..] else {
            unreachable!()
        };
        assert_eq!(
            r.invoke_operation(class_on_rover, SYNTAX_ELEMENT, &[])
                .unwrap()
                .value,
            reference(rover)
        );
        assert_eq!(
            r.invoke_operation(package_on_rover, SYNTAX_ELEMENT, &[])
                .unwrap()
                .value,
            DerivedValue::Null
        );
        // The user metaclass's feature: the minimal library leaves its
        // supertype closure uncertified, so `isSyntactic` refuses and the
        // precondition carries that refusal (the full library decides it:
        // `evaluation_operations.rs`).
        assert_eq!(
            r.invoke_operation(tag, SYNTAX_ELEMENT, &[]),
            Err(OperationError::Incomplete {
                effective: SYNTAX_ELEMENT,
                blocker: Some(tag)
            })
        );
        assert!(matches!(
            r.invoke_operation(tag, "Kernel-Metadata-MetadataFeature-isSyntactic_", &[]),
            Err(OperationError::Incomplete { blocker: Some(b), .. }) if b == tag
        ));
        assert_eq!(
            r.invoke_operation(about_other, SYNTAX_ELEMENT, &[])
                .unwrap()
                .value,
            reference(other)
        );
        assert!(matches!(
            r.invoke_operation(package_metadata[0], SYNTAX_ELEMENT, &[]),
            Err(OperationError::UnsupportedConfiguration {
                effective: SYNTAX_ELEMENT,
                ..
            })
        ));
    }
    /// Without the reflection library no metaclass names the element:
    /// the metadata access bodies refuse at the referenced element rather
    /// than answer a partial sequence.
    #[test]
    fn metadata_access_refuses_without_the_reflection_library() {
        let mut r = reflection_fixture(
            "",
            "package M { metaclass Tag; class Rover { @Tag; } feature probe = Rover.metadata; }",
        );
        let probe = value_expression(&mut r, "M::probe");
        let rover = r.resolve_qualified("M::Rover").unwrap();
        let target = [DerivedValue::Element(rover)];
        assert_eq!(
            r.invoke_operation(probe, METACLASS_FEATURE, &[]),
            Err(OperationError::Incomplete {
                effective: METACLASS_FEATURE,
                blocker: Some(rover)
            })
        );
        assert_eq!(
            r.invoke_operation(probe, METADATA_EVALUATE, &target),
            Err(OperationError::Incomplete {
                effective: METADATA_EVALUATE,
                blocker: Some(rover)
            })
        );
    }
    const SPECIALIZES: &str = "Core-Types-Type-specializes_Type";
    const COMPATIBLE: &str = "Core-Types-Type-isCompatibleWith_Type";
    const ALL: &str = "Core-Types-Type-allSupertypes_";
    const SUPERTYPES: &str = "Core-Types-Type-supertypes_Boolean";
    /// KerML 8.3.3.1.10: `specializes` and `isCompatibleWith` follow the
    /// direct and indirect supertypes, the implied library bases included;
    /// `supertypes(false)` lists the direct ones; `allSupertypes` the
    /// closure with the receiver first; a conjugated receiver delegates.
    #[test]
    fn conformance_operations_follow_written_and_implied_specializations() {
        // A feature typed by a library type: this fixture's library is too
        // small for the planner to certify a user-typed feature's bases.
        let mut r = kernel_fixture(
            "class A; class B specializes A; class C conjugates B; class D; feature f : Base::Anything;",
        );
        let yes = DerivedValue::Bool(true);
        let no = DerivedValue::Bool(false);
        for (receiver, general, expected) in [
            ("B", "A", &yes),
            ("B", "Occurrences::Occurrence", &yes),
            ("B", "Base::Anything", &yes),
            ("B", "B", &yes),
            ("A", "B", &no),
            ("A", "D", &no),
            ("C", "A", &yes),
            ("C", "D", &no),
            ("f", "Base::Anything", &yes),
            ("f", "Base::things", &yes),
            ("f", "D", &no),
        ] {
            let arguments = [element(&mut r, general)];
            for operation in [SPECIALIZES, COMPATIBLE] {
                assert_eq!(
                    call(&mut r, receiver, operation, &arguments)
                        .unwrap_or_else(|e| panic!("{receiver} {operation} {general}: {e}")),
                    *expected,
                    "{receiver} {operation} {general}"
                );
            }
        }
        let supertypes = |r: &mut ResolvedModel, receiver: &str, exclude_implied: bool| {
            let value = call(
                r,
                receiver,
                SUPERTYPES,
                &[DerivedValue::Bool(exclude_implied)],
            )
            .unwrap();
            names(r, value)
        };
        assert_eq!(supertypes(&mut r, "B", false), ["A"]);
        assert_eq!(supertypes(&mut r, "B", true), ["A"]);
        assert_eq!(supertypes(&mut r, "A", false), ["Occurrences::Occurrence"]);
        assert_eq!(supertypes(&mut r, "A", true), Vec::<String>::new());
        assert_eq!(supertypes(&mut r, "C", false), ["B"]);
        let mut f = supertypes(&mut r, "f", false);
        f.sort();
        assert_eq!(f, ["Base::Anything", "Base::things"]);
        assert_eq!(supertypes(&mut r, "f", true), ["Base::Anything"]);
        let all = |r: &mut ResolvedModel, receiver: &str| {
            let value = call(r, receiver, ALL, &[]).unwrap();
            names(r, value)
        };
        assert_eq!(
            all(&mut r, "B"),
            ["B", "A", "Occurrences::Occurrence", "Base::Anything"]
        );
        assert_eq!(
            all(&mut r, "C"),
            ["C", "B", "A", "Occurrences::Occurrence", "Base::Anything"]
        );
        // A written specialization whose target is unresolved leaves the
        // closure uncertain: the bases and a negative answer are refused,
        // naming the type, while a positive witness still answers.
        let mut r = kernel_fixture("class A; class B specializes A, Unknown; class D;");
        let b = r.resolve_qualified("B").unwrap();
        let a = [element(&mut r, "A")];
        assert_eq!(call(&mut r, "B", SPECIALIZES, &a).unwrap(), yes);
        for (operation, arguments) in [
            (ALL, vec![]),
            (SUPERTYPES, vec![DerivedValue::Bool(false)]),
            (SPECIALIZES, vec![element(&mut r, "D")]),
        ] {
            assert!(
                matches!(
                    call(&mut r, "B", operation, &arguments),
                    Err(OperationError::Incomplete { blocker: Some(blocker), .. }) if blocker == b
                ),
                "{operation}"
            );
        }
    }
    /// `Feature::isCompatibleWith`'s second way (KerML 8.3.3.3.4): both
    /// featureless, a shared redefined feature, and access; two package
    /// features stand in `Base::Anything`, which every feature is featured
    /// within, so the access check decides for them.
    #[test]
    fn feature_compatibility_answers_through_the_access_check() {
        let mut r = kernel_fixture(
            "class D; feature f : Base::Anything; feature g :>> f; feature h :>> f; feature k :>> f { feature inner; } feature other : Base::Anything;",
        );
        const FEATURE: &str = "Core-Features-Feature-isCompatibleWith_Type";
        let argument = |r: &mut ResolvedModel, name: &str| vec![element(r, name)];
        // Specialization decides first: g redefines f.
        let f = argument(&mut r, "f");
        let g_feature = r.resolve_qualified("g").unwrap();
        let answer = r.invoke_operation(g_feature, COMPATIBLE, &f).unwrap();
        assert_eq!(answer.effective, FEATURE);
        assert_eq!(answer.value, DerivedValue::Bool(true));
        // A type the feature reaches through its typing: true; an unrelated
        // one, not a Feature: false; a feature owner on either side: false.
        let anything = argument(&mut r, "Base::Anything");
        assert_eq!(
            call(&mut r, "g", COMPATIBLE, &anything).unwrap(),
            DerivedValue::Bool(true)
        );
        let d = argument(&mut r, "D");
        assert_eq!(
            call(&mut r, "g", COMPATIBLE, &d).unwrap(),
            DerivedValue::Bool(false)
        );
        let g = argument(&mut r, "g");
        assert_eq!(
            call(&mut r, "k", COMPATIBLE, &g).unwrap(),
            DerivedValue::Bool(false)
        );
        let k = argument(&mut r, "k");
        assert_eq!(
            call(&mut r, "g", COMPATIBLE, &k).unwrap(),
            DerivedValue::Bool(false)
        );
        // No shared redefined feature: false.
        let o = argument(&mut r, "other");
        assert_eq!(
            call(&mut r, "g", COMPATIBLE, &o).unwrap(),
            DerivedValue::Bool(false)
        );
        // Both redefine f and own nothing: the access check decides, and
        // g, featured by nothing, stands in Anything, within which h is
        // featured.
        let h = argument(&mut r, "h");
        assert_eq!(
            call(&mut r, "g", COMPATIBLE, &h).unwrap(),
            DerivedValue::Bool(true)
        );
    }
    #[test]
    fn incomparable_redefinitions_refuse_instead_of_choosing_declaration_order() {
        static BASE: OperationSpec = OperationSpec {
            id: "base",
            declaring_metaclass: "Element",
            name: "op",
            redefines: &[],
            parameters: &[],
        };
        static LEFT: OperationSpec = OperationSpec {
            id: "left",
            declaring_metaclass: "Connector",
            name: "op",
            redefines: &["base"],
            parameters: &[],
        };
        static RIGHT: OperationSpec = OperationSpec {
            id: "right",
            declaring_metaclass: "Usage",
            name: "op",
            redefines: &["base"],
            parameters: &[],
        };
        assert!(conforms("BindingConnectorAsUsage", "Connector"));
        assert!(conforms("BindingConnectorAsUsage", "Usage"));
        let dispatch = Dispatch {
            descendants: HashMap::from([("base", vec![&BASE, &LEFT, &RIGHT])]),
            ancestors: HashMap::from([
                ("base", HashSet::new()),
                ("left", HashSet::from(["base"])),
                ("right", HashSet::from(["base"])),
            ]),
        };
        assert!(matches!(
            dispatch.effective(&BASE, "BindingConnectorAsUsage"),
            Err(OperationError::AmbiguousRedefinition)
        ));
    }
}
