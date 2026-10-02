//! Checked semantic reads. Compatibility accessors remain available for
//! callers that explicitly accept incomplete derivations.

use super::{Derived, DerivedValue, Derives, ElementRef, Reference, ResolvedModel, derives_under};
use crate::semantic_catalog::{self, PropertySpec};
use serde_json::{Value, json};
pub(super) mod certified_types;
mod export;
use certified_types::CheckedRow;
pub use certified_types::{ConditionalPropertyCapability, conditional_property_capability};

/// Why a specification property cannot be returned as an exact value.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PropertyError {
    NotDeclared,
    NotComputed,
    Approximate,
    /// The declaration has a conditional implementation, but this receiver's
    /// complete type projection could not be established.
    IncompleteTypeProjection(super::FeatureTypeIssue),
    /// Complete Usage variability could not be established for this receiver.
    IncompleteUsageVariability(super::UsageVariabilityIssue),
    /// Complete ordered Type.input could not be established.
    IncompleteTypeInput(super::TypeInputIssue),
    /// Complete ordered Type feature or membership projections could not be established.
    IncompleteTypeFeatures(super::TypeInputIssue),
    /// A complete supplied Invocation argument mapping could not be established.
    IncompleteInvocationBindings(super::InvocationBindingIssue),
    /// Complete canonical Constructor supplied-argument mapping could not be established.
    IncompleteConstructorBindings(super::ConstructorBindingIssue),
    /// Complete ordinary Function result selection could not be established.
    IncompleteFunctionResult(super::TypeInputIssue),
    MissingRequiredValue,
    UnresolvedReference(String),
    InvalidValue(String),
}

impl std::fmt::Display for PropertyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotDeclared => f.write_str("property is not declared"),
            Self::NotComputed => f.write_str("property is not computed"),
            Self::Approximate => f.write_str("property has an incomplete derivation"),
            Self::IncompleteTypeProjection(reason) => {
                write!(f, "type projection is incomplete: {reason:?}")
            }
            Self::IncompleteUsageVariability(reason) => {
                write!(f, "Usage variability is incomplete: {reason:?}")
            }
            Self::IncompleteTypeInput(reason) => write!(f, "Type.input is incomplete: {reason:?}"),
            Self::IncompleteTypeFeatures(reason) => {
                write!(f, "Type features are incomplete: {reason:?}")
            }
            Self::IncompleteInvocationBindings(reason) => {
                write!(f, "Invocation arguments are incomplete: {reason:?}")
            }
            Self::IncompleteConstructorBindings(reason) => {
                write!(f, "Constructor arguments are incomplete: {reason:?}")
            }
            Self::IncompleteFunctionResult(reason) => {
                write!(f, "Function.result is incomplete: {reason:?}")
            }
            Self::MissingRequiredValue => f.write_str("required property has no value"),
            Self::UnresolvedReference(s) => write!(f, "unresolved reference: {s}"),
            Self::InvalidValue(s) => write!(f, "invalid property value: {s}"),
        }
    }
}

impl std::error::Error for PropertyError {}

/// A field that prevented strict full-form export.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PropertyIssue {
    pub element_id: uuid::Uuid,
    pub property: String,
    pub reason: PropertyError,
}

/// Strict export never substitutes placeholders. Unavailable fields are
/// collected for an established snapshot. Snapshot or identity failures may
/// stop the export before property inspection.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticExportError {
    pub issues: Vec<PropertyIssue>,
}

impl std::fmt::Display for SemanticExportError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "strict export refused: {} unavailable properties",
            self.issues.len()
        )?;
        if let Some(first) = self.issues.first() {
            write!(
                f,
                " ({}.{}: {})",
                first.element_id, first.property, first.reason
            )?;
        }
        Ok(())
    }
}
impl std::error::Error for SemanticExportError {}

impl ResolvedModel {
    /// Export specification properties through the checked semantic reader.
    /// No recovery annotations or invented references are inserted. Incomplete
    /// semantic support causes refusal, even for a syntactically valid model.
    /// The current closure policy is preserved and never implicitly promoted.
    pub fn to_full_json_strict(&mut self) -> Result<Value, SemanticExportError> {
        export::full(self)
    }

    /// Read an owned or derived property by its specification name. Inherited
    /// names follow metamodel redefinitions, including changes of name, shape
    /// and derived status. Required values, known target metaclasses and
    /// multiplicities are checked. Unknown computations are errors, not defaults.
    /// Core type/behavior/function reads require complete bounded evidence and
    /// full semantic closure. Unsupported type-dependent derivations refuse;
    /// compatibility values remain available through [`Self::derived`].
    /// Other external UUIDs are preserved; their target type cannot be verified locally.
    pub fn property(&mut self, e: ElementRef, name: &str) -> Result<Value, PropertyError> {
        self.property_with_row(e, name, &mut CheckedRow::default())
    }

    fn property_with_row(
        &mut self,
        e: ElementRef,
        name: &str,
        row: &mut CheckedRow,
    ) -> Result<Value, PropertyError> {
        let (requested, effective) = semantic_catalog::property(self.element_type(e), name)
            .ok_or(PropertyError::NotDeclared)?;
        let spec = effective.ok_or(PropertyError::NotComputed)?;
        if let Some(result) = row.read_declared(self, e, requested, spec) {
            return result.map(|value| self.semantic_json(value));
        }
        let mut value = match row.read_owned_source(self, e, spec) {
            Some(result) => result?,
            None => self.effective_property(e, spec, row)?,
        };
        self.validate_property_value(spec, &value)?;
        value = reshape(value, requested)?;
        self.validate_property_value(requested, &value)?;
        Ok(value)
    }

    fn effective_property(
        &mut self,
        e: ElementRef,
        spec: &PropertySpec,
        row: &mut CheckedRow,
    ) -> Result<Value, PropertyError> {
        let ty = self.element_type(e);
        if ty == "FeatureReferenceExpression"
            && matches!(spec.name, "ownedRelationship" | "isImpliedIncluded")
            && !self.owned_result_projection_ready(e)
        {
            return Err(PropertyError::Approximate);
        }
        // Fixed constraints override the concrete syntax's default bits.
        if spec.name == "isSufficient" && super::metaclass_conforms(ty, "ConnectionDefinition") {
            return Ok(json!(true));
        }
        if spec.name == "isConstant"
            && self.b.graph_format == crate::model::GraphFormat::LegacyV2
            && super::metaclass_conforms(ty, "Usage")
            && self.b.elements[e.0]
                .props
                .get("isEnd")
                .and_then(|v| v.as_bool())
                == Some(true)
        {
            // The end constraint is conditional on mayTimeVary; do not guess.
            return Err(PropertyError::NotComputed);
        }
        if spec.derived {
            if matches!(
                spec.id,
                "Root-Namespaces-Namespace-importedMembership"
                    | "Root-Namespaces-Namespace-membership"
                    | "Root-Namespaces-Namespace-member"
            ) {
                let value = row.read_namespace(self, e, spec.id)?;
                return Ok(self.semantic_json(value));
            }
            let value = self.derived_exact_with_row(e, spec.name, row)?;
            return Ok(self.semantic_json(value));
        }
        let id = |r: usize| json!({"@id": self.element_id(ElementRef(r)).to_string()});
        match spec.name {
            "elementId" => return Ok(json!(self.element_id(e).to_string())),
            "owningRelationship" => {
                return Ok(self.b.elements[e.0]
                    .owning_relationship
                    .map(id)
                    .unwrap_or(Value::Null));
            }
            "ownedRelatedElement" => {
                return Ok(Value::Array(
                    self.b.elements[e.0]
                        .children
                        .iter()
                        .map(|&r| id(r))
                        .collect(),
                ));
            }
            "ownedRelationship" => {
                if !self.implied_relationships(e).is_empty() {
                    return Err(PropertyError::Approximate);
                }
                return Ok(Value::Array(
                    self.owned_relationships(e)
                        .into_iter()
                        .map(|r| json!({"@id": self.element_id(r).to_string()}))
                        .collect(),
                ));
            }
            "isImpliedIncluded" => {
                return if self.implied_relationships(e).is_empty() {
                    Ok(json!(false))
                } else {
                    Err(PropertyError::Approximate)
                };
            }
            "owningRelatedElement" => {
                self.ensure_rel_owner();
                return Ok(self.rel_owner[e.0]
                    .map(|r| json!({"@id": self.element_id(ElementRef(r)).to_string()}))
                    .unwrap_or(Value::Null));
            }
            _ => {}
        }
        for name in spec.storage_names {
            if let Some(value) = self.b.elements[e.0].props.get(name) {
                // Compact storage may retain a general property's spelling/shape.
                return reshape(value.to_json(), spec);
            }
        }
        if let Some(default) = spec.default_json {
            return serde_json::from_str(default)
                .map_err(|e| PropertyError::InvalidValue(e.to_string()));
        }
        if spec.lower == 0 {
            return Ok(if spec.upper == Some(1) {
                Value::Null
            } else {
                json!([])
            });
        }
        Err(PropertyError::MissingRequiredValue)
    }

    fn semantic_json(&self, value: DerivedValue) -> Value {
        let id = |e: ElementRef| json!({"@id": self.element_id(e).to_string()});
        let reference = |r: Reference| match r {
            Reference::Element(e) => id(e),
            Reference::External(u) => json!({"@id": u.to_string()}),
            Reference::Unresolved(s) => json!({"@ref": s}),
        };
        match value {
            DerivedValue::Null => Value::Null,
            DerivedValue::Bool(v) => json!(v),
            DerivedValue::Str(v) => json!(v),
            DerivedValue::Strings(v) => json!(v),
            DerivedValue::Element(e) => id(e),
            DerivedValue::Elements(es) => Value::Array(es.into_iter().map(id).collect()),
            DerivedValue::Reference(r) => reference(r),
            DerivedValue::References(rs) => Value::Array(rs.into_iter().map(reference).collect()),
        }
    }

    fn validate_property_value(
        &mut self,
        spec: &PropertySpec,
        value: &Value,
    ) -> Result<(), PropertyError> {
        let values: &[Value] = if spec.upper == Some(1) {
            if value.is_null() {
                &[]
            } else {
                std::slice::from_ref(value)
            }
        } else {
            value
                .as_array()
                .ok_or_else(|| PropertyError::InvalidValue("expected an array".into()))?
        };
        if values.len() < spec.lower {
            return Err(PropertyError::MissingRequiredValue);
        }
        if spec.upper.is_some_and(|upper| values.len() > upper) {
            return Err(PropertyError::InvalidValue(
                "multiplicity upper bound exceeded".into(),
            ));
        }
        if spec.unique && values.len() > 1 {
            let mut seen = std::collections::HashSet::with_capacity(values.len());
            for value in values {
                if !seen.insert(value.to_string()) {
                    return Err(PropertyError::InvalidValue(
                        "duplicate value in a unique property".into(),
                    ));
                }
            }
        }
        for v in values {
            if let Some(s) = v.get("@ref").and_then(Value::as_str) {
                return Err(PropertyError::UnresolvedReference(s.into()));
            }
            let valid = match spec.target {
                "Boolean" => v.is_boolean(),
                "String" => v.is_string(),
                "Integer" => v.is_i64() || v.is_u64(),
                "Real" => v.is_number(),
                "UnlimitedNatural" => v.is_u64() || v.as_i64() == Some(-1),
                target if crate::metaclass_name(target).is_some() => {
                    if let Some(id) = v.get("@id").and_then(Value::as_str) {
                        if uuid::Uuid::parse_str(id).is_err() {
                            false
                        } else if let Some(e) = self.element_by_id(id) {
                            super::metaclass_conforms(self.element_type(e), target)
                        } else {
                            true
                        }
                    } else {
                        false
                    }
                }
                _ if !spec.enum_values.is_empty() => {
                    v.as_str().is_some_and(|s| spec.enum_values.contains(&s))
                }
                _ => return Err(PropertyError::NotComputed),
            };
            if !valid {
                return Err(PropertyError::InvalidValue(format!(
                    "expected {}",
                    spec.target
                )));
            }
        }
        Ok(())
    }

    /// Read a derived property whose implementation is classified `Exact`.
    /// Unlike [`Self::derived`], this refuses passthrough values and unresolved
    /// spellings. A required reference is never substituted with a self-reference.
    /// External UUID references remain explicit external references.
    /// This is not whole-model validation or certification of reference target
    /// types and multiplicities beyond the required-reference check.
    pub fn derived_exact(
        &mut self,
        e: ElementRef,
        name: &str,
    ) -> Result<DerivedValue, PropertyError> {
        self.derived_exact_with_row(e, name, &mut CheckedRow::default())
    }

    fn derived_exact_with_row(
        &mut self,
        e: ElementRef,
        name: &str,
        row: &mut CheckedRow,
    ) -> Result<DerivedValue, PropertyError> {
        if let Some(result) = row.read(self, e, name) {
            return result;
        }
        if self.element_type(e) == "FeatureReferenceExpression" {
            // Local result/binding additions do not certify every required
            // family or existing-result expression, so entire collections
            // remain qualified.
            if matches!(
                name,
                "ownedElement"
                    | "ownedMember"
                    | "ownedFeature"
                    | "ownedFeatureMembership"
                    | "ownedMembership"
                    | "member"
                    | "membership"
                    | "feature"
                    | "featureMembership"
            ) || (matches!(name, "result" | "ownedParameter")
                && !self.owned_result_projection_ready(e))
            {
                return Err(PropertyError::Approximate);
            }
        }
        match derives_under(self.element_type(e), name, self.closure_policy()) {
            Derives::NotDeclared => return Err(PropertyError::NotDeclared),
            Derives::NotComputed => return Err(PropertyError::NotComputed),
            Derives::Passthrough => return Err(PropertyError::Approximate),
            Derives::Exact => {}
        }
        let value = match self.derived(e, name) {
            Derived::NotDeclared => return Err(PropertyError::NotDeclared),
            Derived::NotComputed => return Err(PropertyError::NotComputed),
            Derived::Value(value) => value,
        };
        let unresolved = match &value {
            DerivedValue::Reference(Reference::Unresolved(s)) => Some(s),
            DerivedValue::References(rs) => rs.iter().find_map(|r| match r {
                Reference::Unresolved(s) => Some(s),
                _ => None,
            }),
            _ => None,
        };
        if let Some(s) = unresolved {
            return Err(PropertyError::UnresolvedReference(s.clone()));
        }
        if value == DerivedValue::Null {
            let props = crate::schema_props::METACLASS_PROPS;
            if let Ok(i) = props.binary_search_by_key(&self.element_type(e), |(m, _)| *m) {
                if let Ok(p) = props[i].1.binary_search_by_key(&name, |(n, _)| *n) {
                    if props[i].1[p].1 == b'R' {
                        return Err(PropertyError::MissingRequiredValue);
                    }
                }
            }
        }
        Ok(value)
    }
}

pub(super) fn reshape(value: Value, spec: &PropertySpec) -> Result<Value, PropertyError> {
    if spec.upper != Some(1) {
        return Ok(match value {
            Value::Array(_) => value,
            Value::Null => json!([]),
            other => Value::Array(vec![other]),
        });
    }
    match value {
        Value::Array(mut values) if values.len() <= 1 => Ok(values.pop().unwrap_or(Value::Null)),
        Value::Array(_) => Err(PropertyError::InvalidValue(
            "multiple values for a single-valued redefinition".into(),
        )),
        other => Ok(other),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;

    #[test]
    fn strict_export_refuses_duplicate_row_identities() {
        let mut m = Model::new();
        m.add_source("identity.sysml", "package A; package B;");
        let mut r = ResolvedModel::build(&m);
        let a = r.resolve_qualified("A").unwrap();
        let b = r.resolve_qualified("B").unwrap();
        r.b.elements[b.0].id = r.element_id(a);
        let report = r.to_full_json_strict().unwrap_err();
        assert!(report.issues.iter().any(|issue| issue.property == "@id"
            && matches!(issue.reason, PropertyError::InvalidValue(_))));
    }

    #[test]
    fn semantic_validation_rejects_bad_enums_targets_and_duplicate_ids() {
        let mut model = Model::new();
        model.add_source("m.sysml", "package P { part def D; part p : D; }");
        let mut r = ResolvedModel::build(&model);
        let p = r.resolve_qualified("P::p").unwrap();
        let pkg = r.resolve_qualified("P").unwrap();
        let membership = r.b.elements[p.0].owning_relationship.unwrap();
        r.b.elements[membership]
            .props
            .insert("visibility", json!("sideways"));
        assert!(matches!(
            r.property(ElementRef(membership), "visibility"),
            Err(PropertyError::InvalidValue(_))
        ));
        let typing = r
            .owned_relationships(p)
            .into_iter()
            .find(|&e| r.element_type(e) == "FeatureTyping")
            .unwrap();
        let pkg_id = r.element_id(pkg).to_string();
        r.b.elements[typing.0]
            .props
            .insert("type", json!({"@id": pkg_id}));
        assert!(matches!(
            r.property(typing, "general"),
            Err(PropertyError::InvalidValue(_))
        ));
        let spec = semantic_catalog::property("Namespace", "ownedRelationship")
            .unwrap()
            .0;
        assert!(matches!(
            r.validate_property_value(spec, &json!([{"@id": pkg_id}, {"@id": pkg_id}])),
            Err(PropertyError::InvalidValue(_))
        ));
    }

    #[test]
    fn multiple_inheritance_ambiguity_is_explicit() {
        let (_, effective) = semantic_catalog::property("BindingConnectorAsUsage", "type").unwrap();
        assert!(effective.is_none());
        assert!(
            semantic_catalog::property("BindingConnectorAsUsage", "definition")
                .unwrap()
                .1
                .is_some()
        );
        assert!(
            semantic_catalog::property("BindingConnectorAsUsage", "association")
                .unwrap()
                .1
                .is_some()
        );
    }
}

#[cfg(test)]
mod type_fidelity_tests;
