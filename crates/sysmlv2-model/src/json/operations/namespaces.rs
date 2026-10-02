//! Checked Namespace bodies with bounded, reciprocal import membership evidence.
//! Import traversal reuses complete membership evidence for ordinary Type contexts.
//! Filtered visibility and general metadata predicates
//! remain explicitly qualified.
use super::{OperationArgumentIssue, OperationError, OperationExecutionSignature};
use crate::{
    json::{
        DerivedValue, ElementRef, PropertyError, Reference, ResolvedModel, membership_evidence,
        semantic::certified_types::Stamp, semantic_ownership, structural_index::StoredStructure,
    },
    metaclass::conforms,
};
use std::collections::HashSet;
pub(in crate::json) mod imports;
mod resolution;
use sysmlv2_syntax::{
    ast::Dialect,
    lexer::{tokenize, unescape},
    name::spell_path,
    parser::is_reserved,
    token::TokenKind,
};

#[derive(Clone, Copy)]
pub(super) enum Body {
    Qualification,
    Unqualified,
    Memberships,
    Visible,
    Inherited,
    Inheritable,
    NonPrivate,
    Imported,
    Visibility,
    Names,
    Import,
    ResolveVisible,
    Resolve,
    ResolveLocal,
    ResolveGlobal,
}
fn charge(steps: &mut usize, n: usize, effective: &'static str) -> Result<(), OperationError> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(OperationError::WorkLimit { effective })
    } else {
        Ok(())
    }
}
fn syntax(
    source: &str,
    effective: &'static str,
    signature: &OperationExecutionSignature,
    qualification: bool,
    mut steps: usize,
) -> Result<DerivedValue, OperationError> {
    let (global, mut names) = qualified_names(source, effective, signature, &mut steps)?;
    if !qualification {
        return Ok(DerivedValue::Str(names.pop().expect("at least one name")));
    }
    names.pop();
    if names.is_empty() {
        return Ok(if global {
            DerivedValue::Str("$".into())
        } else {
            DerivedValue::Null
        });
    }
    let prefix = spell_path(Some(Dialect::Kerml), names);
    Ok(DerivedValue::Str(if global {
        format!("$::{prefix}")
    } else {
        prefix
    }))
}
fn qualified_names(
    source: &str,
    effective: &'static str,
    signature: &OperationExecutionSignature,
    steps: &mut usize,
) -> Result<(bool, Vec<String>), OperationError> {
    // Bound tokenization, decoding, and re-spelling before allocating. The
    // existing lexer is the authority for quoted-name escapes and trivia.
    charge(
        steps,
        source.len().saturating_mul(8).saturating_add(1),
        effective,
    )?;
    let invalid = || OperationError::InvalidArgument {
        index: 0,
        parameter: signature.inputs[0],
        issue: OperationArgumentIssue::InvalidSyntax,
    };
    let (tokens, diagnostics) = tokenize(source);
    if !diagnostics.is_empty() {
        return Err(invalid());
    }
    let mut tokens = tokens.iter().filter(|t| !t.kind.is_trivia()).peekable();
    let global = tokens.peek().is_some_and(|t| t.kind == TokenKind::Dollar);
    if global {
        tokens.next();
        if tokens
            .next()
            .is_none_or(|t| t.kind != TokenKind::ColonColon)
        {
            return Err(invalid());
        }
    }
    let mut names = Vec::new();
    loop {
        let token = tokens.next().ok_or_else(invalid)?;
        let name = match token.kind {
            TokenKind::Ident if !is_reserved(Dialect::Kerml, token.text(source)) => {
                token.text(source).to_owned()
            }
            TokenKind::UnrestrictedName => unescape(token.text(source)),
            _ => return Err(invalid()),
        };
        names.push(name);
        match tokens.next().map(|t| t.kind) {
            Some(TokenKind::ColonColon) => {}
            Some(TokenKind::Eof) if tokens.next().is_none() => break,
            _ => return Err(invalid()),
        }
    }
    Ok((global, names))
}

#[derive(Clone)]
pub(in crate::json) struct Membership {
    pub(in crate::json) relationship: usize,
    pub(in crate::json) member: usize,
    pub(in crate::json) visibility: &'static str,
}
fn visibility(r: &ResolvedModel, relationship: usize) -> Option<&'static str> {
    visibility_builder(&r.b, relationship)
}
fn visibility_builder(b: &crate::json::Builder, relationship: usize) -> Option<&'static str> {
    match b.elements[relationship].props.get("visibility") {
        None => Some(if conforms(b.elements[relationship].ty, "Import") {
            "private"
        } else {
            "public"
        }),
        Some(v) => match v.as_str()? {
            "public" => Some("public"),
            "protected" => Some("protected"),
            "private" => Some("private"),
            _ => None,
        },
    }
}
pub(in crate::json) fn memberships_builder(
    b: &crate::json::Builder,
    raw: &StoredStructure,
    owner: usize,
    steps: &mut usize,
    effective: &'static str,
) -> Result<Vec<Membership>, OperationError> {
    let incomplete = || OperationError::Incomplete { effective };
    if !matches!(
        b.elements[owner].ty,
        "Namespace" | "Package" | "LibraryPackage"
    ) && !crate::json::type_features::supported_root(b.elements[owner].ty)
    {
        return Err(incomplete());
    }
    let domains = raw.membership_domains(b, steps).ok_or_else(incomplete)?;
    if !domains.owner_complete(owner)
        || raw.metadata_annotation_targets.contains(&owner)
        || b.metadata_of.get(&owner).is_some_and(|v| !v.is_empty())
    {
        return Err(incomplete());
    }
    let relationships = semantic_ownership::owned_relationships(b, owner).ok_or_else(incomplete)?;
    charge(steps, relationships.len().saturating_mul(2), effective)?;
    let mut seen = HashSet::new();
    let mut result = Vec::new();
    for relationship in relationships.iter() {
        if !seen.insert(relationship)
            || semantic_ownership::checked_relationship_carrier(b, raw, relationship, steps)
                != Some(Some(owner))
        {
            return Err(incomplete());
        }
        if !conforms(b.elements[relationship].ty, "Membership") {
            continue;
        }
        let member = membership_evidence::member(b, raw, owner, relationship, steps)
            .ok_or_else(incomplete)?;
        result.push(Membership {
            relationship,
            member,
            visibility: visibility_builder(b, relationship).ok_or_else(incomplete)?,
        });
    }
    Ok(result)
}
fn member_names(
    r: &mut ResolvedModel,
    membership: &Membership,
    steps: &mut usize,
    effective: &'static str,
) -> Result<Vec<String>, OperationError> {
    let incomplete = || OperationError::Incomplete { effective };
    charge(steps, 4, effective)?;
    let owned = conforms(r.b.elements[membership.relationship].ty, "OwningMembership");
    let mut names = Vec::new();
    let source = &r.b.elements[if owned {
        membership.member
    } else {
        membership.relationship
    }];
    for key in if owned {
        ["declaredName", "declaredShortName"]
    } else {
        ["memberName", "memberShortName"]
    } {
        if let Some(value) = source.props.get(key).and_then(|v| v.as_str()) {
            charge(steps, value.len().saturating_mul(3), effective)?;
        }
    }
    for (key, operation) in [
        (
            "memberShortName",
            "Root-Elements-Element-effectiveShortName_",
        ),
        ("memberName", "Root-Elements-Element-effectiveName_"),
    ] {
        let value = if owned {
            super::checked_name(r, ElementRef(membership.member), operation, steps)?
        } else {
            match r.b.elements[membership.relationship].props.get(key) {
                None => DerivedValue::Null,
                Some(v) if v.is_null() => DerivedValue::Null,
                Some(v) => DerivedValue::Str(v.as_str().ok_or_else(incomplete)?.to_owned()),
            }
        };
        match value {
            DerivedValue::Null => {}
            DerivedValue::Str(name) => {
                charge(steps, name.len().saturating_add(1), effective)?;
                if !names.contains(&name) {
                    names.push(name);
                }
            }
            _ => return Err(incomplete()),
        }
    }
    Ok(names)
}

// A nested Type query may initialize retained semantic or positional evidence.
// Discard the whole successful attempt in that case and reacquire its evidence;
// never return a value computed across two publication states. The one retry
// shares the original allowance and leaves ordinary Namespace reads cold.
fn with_stable_evidence<T>(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    steps: &mut usize,
    effective: &'static str,
    mut query: impl FnMut(&mut ResolvedModel, &StoredStructure, &mut usize) -> Result<T, OperationError>,
) -> Result<(std::sync::Arc<StoredStructure>, Stamp, T), OperationError> {
    let incomplete = || OperationError::Incomplete { effective };
    if r.b.positional_planning {
        return Err(incomplete());
    }
    if conforms(r.b.elements[receiver.0].ty, "Type")
        && !r.b.ensure_positional_redefinitions_with_budget(steps)
    {
        return Err(incomplete());
    }
    for _ in 0..2 {
        let raw = StoredStructure::for_query(&mut r.b, steps).ok_or_else(incomplete)?;
        if !raw.ids_unique || raw.annotations_incomplete || r.b.metadata_associations_incomplete {
            return Err(incomplete());
        }
        let stamp = Stamp::capture(r);
        let value = query(r, &raw, steps)?;
        charge(steps, 0, effective)?;
        if stamp.current(r) {
            return Ok((raw, stamp, value));
        }
    }
    Err(incomplete())
}
fn prepare(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    steps: &mut usize,
    effective: &'static str,
    excluded: &[usize],
) -> Result<(std::sync::Arc<StoredStructure>, Stamp, imports::Sequence), OperationError> {
    with_stable_evidence(r, receiver, steps, effective, |r, raw, steps| {
        imports::sequence(r, raw, receiver.0, excluded, steps, effective)
    })
}
#[derive(Default)]
pub(in crate::json) struct NamespaceRow {
    cached: Option<(ElementRef, Stamp, imports::Sequence)>,
}
impl NamespaceRow {
    /// One checked export row shares the complete domain and its work allowance
    /// across membership, member, and importedMembership property reads.
    pub(in crate::json) fn property(
        &mut self,
        r: &mut ResolvedModel,
        receiver: ElementRef,
        declaration: &'static str,
        steps: &mut usize,
    ) -> Result<DerivedValue, PropertyError> {
        let body = match declaration {
            "Root-Namespaces-Namespace-importedMembership" => 0,
            "Root-Namespaces-Namespace-membership" => 1,
            "Root-Namespaces-Namespace-member" => 2,
            _ => return Err(PropertyError::NotComputed),
        };
        let result = (|| {
            charge(steps, 1, declaration)?;
            if !self
                .cached
                .as_ref()
                .is_some_and(|(owner, stamp, _)| *owner == receiver && stamp.current(r))
            {
                self.cached = None;
                let (_, stamp, owned) = prepare(r, receiver, steps, declaration, &[])?;
                self.cached = Some((receiver, stamp, owned));
            }
            let (_, stamp, owned) = self.cached.as_ref().expect("complete row");
            let selected = if body == 0 {
                &owned.imported
            } else {
                &owned.all
            };
            charge(steps, selected.len().saturating_mul(2), declaration)?;
            let mut result = Vec::new();
            let mut seen = HashSet::new();
            {
                for membership in selected {
                    let target = if body != 2 {
                        membership.relationship
                    } else {
                        membership.member
                    };
                    if seen.insert(target) {
                        result.push(Reference::Element(ElementRef(target)));
                    }
                }
            }
            if !stamp.current(r) {
                return Err(OperationError::Incomplete {
                    effective: declaration,
                });
            }
            Ok(DerivedValue::References(result))
        })();
        result.map_err(|_| PropertyError::NotComputed)
    }
}
fn argument_element(argument: &DerivedValue) -> usize {
    match argument {
        DerivedValue::Element(e) | DerivedValue::Reference(Reference::Element(e)) => e.0,
        _ => unreachable!("validated scalar element argument"),
    }
}
pub(super) fn invoke(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    signature: &OperationExecutionSignature,
    arguments: &[DerivedValue],
    body: Body,
    mut steps: usize,
) -> Result<DerivedValue, OperationError> {
    if matches!(body, Body::Qualification | Body::Unqualified) {
        let DerivedValue::Str(source) = &arguments[0] else {
            unreachable!("validated string argument")
        };
        return syntax(
            source,
            effective,
            signature,
            matches!(body, Body::Qualification),
            steps,
        );
    }
    let incomplete = || OperationError::Incomplete { effective };
    let result = (|| {
        if matches!(
            body,
            Body::Resolve | Body::ResolveLocal | Body::ResolveGlobal
        ) {
            return resolution::invoke(
                r, receiver, effective, signature, arguments, body, &mut steps,
            );
        }
        if matches!(body, Body::Inherited | Body::Inheritable | Body::NonPrivate) {
            // Exclusions select from the already complete shared provider.
            let excluded_namespaces = imports::exclusions(&arguments[0]);
            let excluded = imports::exclusions(&arguments[1]);
            charge(&mut steps, excluded.len(), effective)?;
            let sequence =
                r.b.checked_type_membership_operation(
                    receiver.0,
                    &excluded_namespaces,
                    &excluded,
                    matches!(arguments[2], DerivedValue::Bool(true)),
                    &mut steps,
                )
                .map_err(|_| incomplete())?;
            let selected = match body {
                Body::Inherited => sequence.inherited,
                Body::Inheritable => sequence.inheritable,
                Body::NonPrivate => sequence.non_private,
                _ => unreachable!(),
            };
            charge(&mut steps, selected.len(), effective)?;
            return Ok(DerivedValue::References(
                selected
                    .into_iter()
                    .map(|m| Reference::Element(ElementRef(m.relationship)))
                    .collect(),
            ));
        }
        let excluded = match body {
            Body::Imported | Body::Visible | Body::Import => imports::exclusions(&arguments[0]),
            Body::Memberships => imports::exclusions(&arguments[1]),
            _ => Vec::new(),
        };
        if matches!(body, Body::Import) {
            return imports::invoke_import(r, receiver, &excluded, &mut steps, effective);
        }
        let (_, _, value) =
            with_stable_evidence(r, receiver, &mut steps, effective, |r, raw, steps| {
                let sequence = imports::sequence(r, raw, receiver.0, &excluded, steps, effective)?;
                let owned = sequence.all;
                let value = match body {
                    Body::Imported => imports::references(sequence.imported),
                    Body::Memberships => {
                        let requested = match &arguments[0] {
                            DerivedValue::Null => None,
                            DerivedValue::Str(v) => Some(v.as_str()),
                            _ => unreachable!("validated visibility"),
                        };
                        imports::references(imports::memberships_of_visibility(
                            r, raw, receiver.0, &excluded, requested, steps, effective, 0,
                        )?)
                    }
                    Body::Visibility => {
                        let mem = argument_element(&arguments[0]);
                        let value = owned
                            .iter()
                            .find(|m| m.relationship == mem)
                            .map_or("private", |m| m.visibility);
                        DerivedValue::Str(value.into())
                    }
                    Body::ResolveVisible => {
                        let DerivedValue::Str(name) = &arguments[0] else {
                            unreachable!("validated name")
                        };
                        charge(steps, name.len(), effective)?;
                        let visible = imports::visible(
                            r,
                            raw,
                            receiver.0,
                            &[],
                            false,
                            false,
                            steps,
                            effective,
                            0,
                        )?;
                        let mut result = DerivedValue::Null;
                        for membership in visible {
                            if member_names(r, &membership, steps, effective)?
                                .iter()
                                .any(|n| n == name)
                            {
                                result = DerivedValue::Reference(Reference::Element(ElementRef(
                                    membership.relationship,
                                )));
                                break;
                            }
                        }
                        result
                    }
                    Body::Names => {
                        let member = argument_element(&arguments[0]);
                        let mut names = Vec::new();
                        let mut seen = HashSet::new();
                        for membership in owned.iter().filter(|m| m.member == member) {
                            for name in member_names(r, membership, steps, effective)? {
                                if seen.insert(name.clone()) {
                                    names.push(name);
                                }
                            }
                        }
                        DerivedValue::Strings(names)
                    }
                    Body::Visible => {
                        let recursive = matches!(arguments[1], DerivedValue::Bool(true));
                        let all = matches!(arguments[2], DerivedValue::Bool(true));
                        imports::references(imports::visible(
                            r, raw, receiver.0, &excluded, recursive, all, steps, effective, 0,
                        )?)
                    }
                    Body::Inherited
                    | Body::Inheritable
                    | Body::NonPrivate
                    | Body::Qualification
                    | Body::Unqualified
                    | Body::Import
                    | Body::Resolve
                    | Body::ResolveLocal
                    | Body::ResolveGlobal => unreachable!(),
                };
                Ok(value)
            })?;
        Ok(value)
    })();
    if steps > crate::eval::MAX_STEPS {
        Err(OperationError::WorkLimit { effective })
    } else {
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;
    fn fixture(source: &str) -> ResolvedModel {
        let mut model = Model::new();
        let unit = model.add_source("namespace-operations.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&model)
    }
    fn invoke(
        r: &mut ResolvedModel,
        receiver: &str,
        operation: &str,
        args: &[DerivedValue],
    ) -> Result<DerivedValue, OperationError> {
        let receiver = r.resolve_qualified(receiver).unwrap();
        r.invoke_operation(
            receiver,
            &format!("Root-Namespaces-Namespace-{operation}"),
            args,
        )
        .map(|result| result.value)
    }
    fn empty() -> DerivedValue {
        DerivedValue::Elements(vec![])
    }
    #[test]
    fn collection_validation_and_body_share_the_operation_budget() {
        let mut r = fixture("package P;");
        let p = r.resolve_qualified("P").unwrap();
        let oversized = DerivedValue::Elements(vec![p; crate::eval::MAX_STEPS / 4 + 1]);
        assert!(matches!(
            invoke(&mut r, "P", "importedMemberships_Namespace", &[oversized]),
            Err(OperationError::WorkLimit { .. })
        ));
        let source = "a".repeat(crate::eval::MAX_STEPS / 9 + 1);
        assert!(matches!(
            invoke(
                &mut r,
                "P",
                "qualificationOf_String",
                &[DerivedValue::Str(source)]
            ),
            Err(OperationError::WorkLimit { .. })
        ));
        assert_eq!(
            invoke(
                &mut r,
                "P",
                "unqualifiedNameOf_String",
                &[DerivedValue::Str("a::b".into())]
            )
            .unwrap(),
            DerivedValue::Str("b".into())
        );
    }
    #[test]
    fn namespace_properties_share_complete_domain_and_refuse_inverse_orphans() {
        let mut r = fixture("package P { class A; alias Alias for A; } class Other;");
        let p = r.resolve_qualified("P").unwrap();
        let a = r.resolve_qualified("P::A").unwrap();
        let other = r.resolve_qualified("Other").unwrap();
        let declarations = [
            "Root-Namespaces-Namespace-importedMembership",
            "Root-Namespaces-Namespace-membership",
            "Root-Namespaces-Namespace-member",
        ];
        let mut row = NamespaceRow::default();
        let mut steps = 0;
        assert!(row.property(&mut r, p, declarations[0], &mut steps).is_ok());
        let cold = steps;
        let members = row
            .property(&mut r, p, declarations[2], &mut steps)
            .unwrap();
        assert_eq!(
            members,
            DerivedValue::References(vec![Reference::Element(a)])
        );
        assert!(
            steps - cold <= 5,
            "the completed row domain should be reused"
        );
        assert!(r.property(other, "importedMembership").is_err());
        for name in ["importedMembership", "membership", "member"] {
            assert!(r.property(p, name).is_ok(), "{name}");
        }
        let membership = r.b.elements[a.0].owning_relationship.unwrap();
        r.b.elements[p.0]
            .owned_relationships
            .make_mut()
            .retain(|&rel| rel != membership);
        for declaration in declarations {
            assert!(row.property(&mut r, p, declaration, &mut steps).is_err());
        }
        for name in ["importedMembership", "membership", "member"] {
            assert!(r.property(p, name).is_err(), "{name}");
        }
    }
    #[test]
    fn sibling_namespace_queries_share_raw_import_absence_with_cumulative_work() {
        let count = 1000;
        let source: String = (0..count).map(|i| format!("package P{i};")).collect();
        let mut r = fixture(&source);
        let packages: Vec<_> = (0..count)
            .map(|i| r.resolve_qualified(&format!("P{i}")).unwrap())
            .collect();
        let declaration = "Root-Namespaces-Namespace-importedMembership";
        let mut cold = 0;
        assert!(
            NamespaceRow::default()
                .property(&mut r, packages[0], declaration, &mut cold)
                .is_ok()
        );
        let raw = r.b.stored_structure.as_ref().unwrap().clone();
        assert!(!raw.has_authored_import);
        assert!(cold >= r.b.elements.len());
        let initial = crate::eval::MAX_STEPS - count * 16;
        let mut steps = initial;
        for package in packages {
            assert!(
                NamespaceRow::default()
                    .property(&mut r, package, declaration, &mut steps)
                    .is_ok()
            );
            assert!(std::sync::Arc::ptr_eq(
                &raw,
                r.b.stored_structure.as_ref().unwrap()
            ));
        }
        assert!(steps - initial <= count * 16);
    }

    #[test]
    fn orphan_import_presence_survives_forward_omission_and_stored_implied_flag() {
        let mut r = fixture("package P; package Q { private import P::*; }");
        let q = r.resolve_qualified("Q").unwrap();
        let import = r.b.elements[q.0].owned_relationships[0];
        let original_type = r.b.elements[import].ty;
        assert!(conforms(original_type, "Import"));
        r.b.elements[q.0].owned_relationships.make_mut().clear();
        r.b.elements[import]
            .props
            .insert("isImplied", serde_json::json!(true));
        assert!(invoke(&mut r, "P", "importedMemberships_Namespace", &[empty()]).is_ok());
        assert!(invoke(&mut r, "Q", "importedMemberships_Namespace", &[empty()]).is_err());
        assert!(r.b.stored_structure.as_ref().unwrap().has_authored_import);
        // Same-size row edits must invalidate the immutable presence fact.
        r.b.elements[import].ty = "Dependency";
        assert!(invoke(&mut r, "P", "importedMemberships_Namespace", &[empty()]).is_ok());
        assert!(!r.b.stored_structure.as_ref().unwrap().has_authored_import);
        r.b.elements[import].ty = original_type;
        assert!(invoke(&mut r, "P", "importedMemberships_Namespace", &[empty()]).is_ok());
        assert!(invoke(&mut r, "Q", "importedMemberships_Namespace", &[empty()]).is_err());
    }

    #[test]
    fn namespace_row_and_nested_name_work_use_the_callers_allowance() {
        let mut r = fixture("package P { class A; }");
        let p = r.resolve_qualified("P").unwrap();
        let a = r.resolve_qualified("P::A").unwrap();
        let mut row = NamespaceRow::default();
        let mut steps = crate::eval::MAX_STEPS;
        assert!(
            row.property(&mut r, p, "Root-Namespaces-Namespace-member", &mut steps)
                .is_err()
        );
        let mut retry = 0;
        assert!(
            row.property(&mut r, p, "Root-Namespaces-Namespace-member", &mut retry)
                .is_ok()
        );
        let m = Membership {
            relationship: r.b.elements[a.0].owning_relationship.unwrap(),
            member: a.0,
            visibility: "public",
        };
        let mut steps = crate::eval::MAX_STEPS - 5;
        assert!(matches!(
            member_names(
                &mut r,
                &m,
                &mut steps,
                "Root-Namespaces-Namespace-namesOf_Element"
            ),
            Err(OperationError::WorkLimit { .. })
        ));
        let mut steps = 0;
        assert_eq!(
            member_names(
                &mut r,
                &m,
                &mut steps,
                "Root-Namespaces-Namespace-namesOf_Element"
            )
            .unwrap(),
            vec!["A".to_owned()]
        );
    }
    #[test]
    fn qualified_name_syntax_uses_lexer_and_reference_spelling() {
        let mut r = fixture("package P;");
        for (source, prefix, name) in [
            ("a", None, "a"),
            ("a::b", Some("a"), "b"),
            ("$::a", Some("$"), "a"),
            ("$::a::b", Some("$::a"), "b"),
            ("'a::b'::'c\\'d'", Some("'a::b'"), "c'd"),
            ("'function'::'a\\nb'", Some("'function'"), "a\nb"),
            ("'Ω' :: '雪'", Some("'Ω'"), "雪"),
            ("a // note\n :: b", Some("a"), "b"),
        ] {
            let args = [DerivedValue::Str(source.into())];
            assert_eq!(
                invoke(&mut r, "P", "qualificationOf_String", &args).unwrap(),
                prefix.map_or(DerivedValue::Null, |s| DerivedValue::Str(s.into()))
            );
            assert_eq!(
                invoke(&mut r, "P", "unqualifiedNameOf_String", &args).unwrap(),
                DerivedValue::Str(name.into())
            );
        }
        for source in [
            "",
            "a::",
            "a b",
            "::a",
            "$a",
            "$::",
            "a::*",
            "function",
            "a::function",
            "'bad\\q'",
            "'unclosed",
            "a /* comment */ :: b",
        ] {
            assert!(
                matches!(
                    invoke(
                        &mut r,
                        "P",
                        "qualificationOf_String",
                        &[DerivedValue::Str(source.into())]
                    ),
                    Err(OperationError::InvalidArgument {
                        issue: OperationArgumentIssue::InvalidSyntax,
                        ..
                    })
                ),
                "{source}"
            );
        }
        let p = r.resolve_qualified("P").unwrap();
        assert!(matches!(
            invoke(
                &mut r,
                "P",
                "qualificationOf_String",
                &[DerivedValue::Element(p)]
            ),
            Err(OperationError::InvalidArgument {
                issue: OperationArgumentIssue::WrongShape,
                ..
            })
        ));
        let large = "a".repeat(crate::eval::MAX_STEPS / 8 + 1);
        assert!(matches!(
            invoke(
                &mut r,
                "P",
                "qualificationOf_String",
                &[DerivedValue::Str(large)]
            ),
            Err(OperationError::WorkLimit { .. })
        ));
    }
    #[test]
    fn namespace_memberships_preserve_alias_identity_names_and_relative_visibility() {
        let mut r = fixture(
            "package P { class <a> A; alias Alias for A; private class Hidden; package Q { class B; } } package Other { class O; }",
        );
        let a = r.resolve_qualified("P::A").unwrap();
        let hidden = r.resolve_qualified("P::Hidden").unwrap();
        let outside = r.resolve_qualified("Other::O").unwrap();
        let other_membership = r.b.elements[outside.0].owning_relationship.unwrap();
        let hidden_membership = r.b.elements[hidden.0].owning_relationship.unwrap();
        assert_eq!(
            invoke(&mut r, "P", "namesOf_Element", &[DerivedValue::Element(a)]).unwrap(),
            DerivedValue::Strings(vec!["a".into(), "A".into(), "Alias".into()])
        );
        assert_eq!(
            invoke(
                &mut r,
                "P",
                "namesOf_Element",
                &[DerivedValue::Element(outside)]
            )
            .unwrap(),
            DerivedValue::Strings(vec![])
        );
        assert_eq!(
            invoke(
                &mut r,
                "P",
                "visibilityOf_Membership",
                &[DerivedValue::Element(ElementRef(other_membership))]
            )
            .unwrap(),
            DerivedValue::Str("private".into())
        );
        assert_eq!(
            invoke(
                &mut r,
                "P",
                "membershipsOfVisibility_VisibilityKind_Namespace",
                &[DerivedValue::Str("private".into()), empty()]
            )
            .unwrap(),
            DerivedValue::References(vec![Reference::Element(ElementRef(hidden_membership))])
        );
        let p = r.resolve_qualified("P").unwrap();
        let members = invoke(
            &mut r,
            "P",
            "membershipsOfVisibility_VisibilityKind_Namespace",
            &[DerivedValue::Null, DerivedValue::Elements(vec![p])],
        )
        .unwrap();
        assert!(matches!(members, DerivedValue::References(ref members) if members.len() == 4));
        assert_eq!(
            invoke(&mut r, "P", "importedMemberships_Namespace", &[empty()]).unwrap(),
            DerivedValue::References(vec![])
        );
        assert!(matches!(
            invoke(
                &mut r,
                "P",
                "membershipsOfVisibility_VisibilityKind_Namespace",
                &[DerivedValue::Str("sideways".into()), empty()]
            ),
            Err(OperationError::InvalidArgument {
                issue: OperationArgumentIssue::InvalidEnumValue,
                ..
            })
        ));
    }
    #[test]
    fn visible_recursion_respects_ownership_visibility_and_type_overrides() {
        let mut r = fixture(
            "package P { public package Q { package B; } private package R { package C; } } class A;",
        );
        for (recursive, all, count) in [
            (false, false, 1),
            (true, false, 2),
            (false, true, 2),
            (true, true, 4),
        ] {
            let result = invoke(
                &mut r,
                "P",
                "visibleMemberships_Namespace_Boolean_Boolean",
                &[
                    empty(),
                    DerivedValue::Bool(recursive),
                    DerivedValue::Bool(all),
                ],
            )
            .unwrap();
            assert!(
                matches!(result, DerivedValue::References(ref result) if result.len() == count)
            );
        }
        assert!(matches!(
            invoke(
                &mut r,
                "A",
                "visibleMemberships_Namespace_Boolean_Boolean",
                &[
                    empty(),
                    DerivedValue::Bool(false),
                    DerivedValue::Bool(false)
                ]
            ),
            Err(OperationError::Incomplete {
                effective: "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean"
            })
        ));
    }
    #[test]
    fn unrelated_imports_do_not_poison_local_inverse_membership_proofs() {
        let mut r = fixture("package P { class A; } package Q { private import P::*; }");
        assert!(invoke(&mut r, "P", "importedMemberships_Namespace", &[empty()]).is_ok());
        assert!(invoke(&mut r, "Q", "importedMemberships_Namespace", &[empty()]).is_ok());
        let mut r = fixture("package P { class A; }");
        let before = r.b.elements.len();
        assert!(invoke(&mut r, "P", "importedMemberships_Namespace", &[empty()]).is_ok());
        assert_eq!(r.b.elements.len(), before);
        assert!(r.b.implied.is_none());
        let a = r.resolve_qualified("P::A").unwrap();
        let p = r.resolve_qualified("P").unwrap();
        let membership = r.b.elements[a.0].owning_relationship.unwrap();
        r.b.elements[p.0]
            .owned_relationships
            .make_mut()
            .retain(|&rel| rel != membership);
        assert!(invoke(&mut r, "P", "importedMemberships_Namespace", &[empty()]).is_err());
    }
}

#[cfg(test)]
mod type_memberships;

#[cfg(test)]
mod recursive_features;
