//! Checked normative operation invocation, separate from AST scalar evaluation.
use super::{
    DerivedValue, ElementRef, Reference, ResolvedModel,
    type_relations::{SupertypesFailure, TypeRelations},
};
use crate::{
    metaclass::conforms,
    metamodel::{self, OperationSpec, ParameterSpec},
};
pub(in crate::json) mod namespaces;

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
    Incomplete {
        effective: &'static str,
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
            Self::Incomplete { effective } => {
                write!(f, "incomplete operation evidence: {effective}")
            }
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
    DeclaredName { key: &'static str, feature: bool },
    In,
    Out,
    SelfSequence,
    EmptySequence,
    True,
    False,
    ExplicitSupertypes,
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
        "Root-Namespaces-NamespaceImport-importedMemberships_Namespace"
        | "Root-Namespaces-MembershipImport-importedMemberships_Namespace" => {
            Namespace(namespaces::Body::Import)
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

        "Core-Types-Type-supertypes_Boolean" | "Core-Features-Feature-supertypes_Boolean" => {
            ExplicitSupertypes
        }
        "Kernel-Behaviors-ParameterMembership-parameterDirection_" => In,
        "Kernel-Functions-ReturnParameterMembership-parameterDirection_" => Out,
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
fn declared_name(
    r: &ResolvedModel,
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
                return Err(OperationError::Incomplete { effective });
            }
        }
    }
    if feature && !declares {
        return Err(OperationError::Incomplete { effective });
    }
    let value = props.get(key).and_then(|v| v.as_str());
    *steps = steps.saturating_add(value.map_or(0, str::len));
    if *steps > crate::eval::MAX_STEPS {
        return Err(OperationError::WorkLimit { effective });
    }
    Ok(value.map_or(DerivedValue::Null, |value| {
        DerivedValue::Str(value.to_owned())
    }))
}
/// Reuse declared-name bodies under a caller's cumulative allowance. Namespace
/// queries cannot restart an independent allowance for every Membership name.
fn checked_name(
    r: &ResolvedModel,
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
        _ => Err(OperationError::Incomplete {
            effective: effective.id,
        }),
    }
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
    /// Effective-name handlers read Element declarations and the declared-name
    /// branch of Feature overrides. Undeclared Feature names remain Incomplete
    /// until the virtual naming-feature dependencies can be certified.
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
                DerivedValue::Strings(v) => v.len(),
                DerivedValue::Str(v) => v.len(),
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
            Handler::DeclaredName { key, feature } => {
                declared_name(self, receiver, effective.id, key, feature, &mut steps)?
            }

            Handler::In => DerivedValue::Str("in".to_owned()),
            Handler::Out => DerivedValue::Str("out".to_owned()),
            Handler::SelfSequence => DerivedValue::References(vec![Reference::Element(receiver)]),
            Handler::EmptySequence => DerivedValue::References(Vec::new()),
            Handler::True => DerivedValue::Bool(true),
            Handler::False => DerivedValue::Bool(false),
            Handler::ExplicitSupertypes => {
                let exclude_implied = matches!(arguments.first(), Some(DerivedValue::Bool(true)));
                let targets = TypeRelations::default()
                    .checked_supertypes(&mut self.b, receiver.0, exclude_implied, &mut steps)
                    .map_err(|failure| {
                        if steps > crate::eval::MAX_STEPS {
                            OperationError::WorkLimit {
                                effective: effective.id,
                            }
                        } else {
                            match failure {
                                SupertypesFailure::Incomplete => OperationError::Incomplete {
                                    effective: effective.id,
                                },
                                SupertypesFailure::UnsupportedConfiguration => {
                                    OperationError::UnsupportedConfiguration {
                                        effective: effective.id,
                                        parameter: signature.inputs[0],
                                    }
                                }
                            }
                        }
                    })?;
                DerivedValue::References(
                    targets
                        .into_iter()
                        .map(|target| Reference::Element(ElementRef(target)))
                        .collect(),
                )
            }
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
            33
        );
        assert_eq!(SIGNATURES.len(), 35); // thirty-three bodies and two virtual base signatures
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
