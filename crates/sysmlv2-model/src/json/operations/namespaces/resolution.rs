//! Membership-valued resolution with explicit, checked multi-unit global scope.
use super::*;
fn find(
    r: &mut ResolvedModel,
    values: Vec<Membership>,
    name: &str,
    steps: &mut usize,
    effective: &'static str,
) -> Result<Option<Membership>, OperationError> {
    charge(steps, values.len(), effective)?;
    for membership in values {
        if member_names(r, &membership, steps, effective)?
            .iter()
            .any(|v| v == name)
        {
            return Ok(Some(membership));
        }
    }
    Ok(None)
}
fn global(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    name: &str,
    steps: &mut usize,
    effective: &'static str,
) -> Result<Option<Membership>, OperationError> {
    let incomplete = || OperationError::Incomplete { effective };
    // The toolkit's global environment is the union of its source-unit root
    // Namespaces, including prepared library units. Unlike compatibility root
    // lookup, duplicate global bindings are qualified instead of selecting a
    // winner by source-unit insertion order.
    charge(steps, r.b.unit_starts.len(), effective)?;
    let roots: Vec<_> = r.b.unit_starts.iter().map(|&(root, _)| root).collect();
    let mut result: Option<Membership> = None;
    for root in roots {
        if r.b.elements[root].ty != "Namespace" || r.b.elements[root].owning_relationship.is_some()
        {
            return Err(incomplete());
        }
        let values = imports::sequence(r, raw, root, &[], steps, effective)?.all;
        // Reject ambiguity within a root as well as between units. Aliases
        // remain separate bindings even if they denote the same member.
        for value in values {
            if member_names(r, &value, steps, effective)?
                .iter()
                .any(|v| v == name)
            {
                if result
                    .as_ref()
                    .is_some_and(|m| m.relationship != value.relationship)
                {
                    return Err(incomplete());
                }
                result = Some(value);
            }
        }
    }
    Ok(result)
}
fn parent(
    r: &ResolvedModel,
    raw: &StoredStructure,
    owner: usize,
    steps: &mut usize,
    effective: &'static str,
) -> Result<Option<usize>, OperationError> {
    let incomplete = || OperationError::Incomplete { effective };
    charge(steps, 8, effective)?;
    let row = &r.b.elements[owner];
    if row.owning_relationship.is_none() {
        charge(steps, r.b.unit_starts.len(), effective)?;
        if !r.b.unit_starts.iter().any(|&(root, _)| root == owner) {
            return Err(incomplete());
        }
    }
    let result = if let Some(relationship) = row.owning_relationship {
        if conforms(r.b.elements[relationship].ty, "OwningMembership") {
            let parent =
                semantic_ownership::checked_relationship_carrier(&r.b, raw, relationship, steps)
                    .flatten()
                    .ok_or_else(incomplete)?;
            if membership_evidence::member(&r.b, raw, parent, relationship, steps) != Some(owner) {
                return Err(incomplete());
            }
            Some(parent)
        } else {
            let relation = &r.b.elements[relationship];
            if !conforms(relation.ty, "Import")
                || (relation.children.len() != 1 || relation.children.first() != Some(&owner))
                || relation
                    .props
                    .get("importedNamespace")
                    .and_then(|v| v.as_reference())
                    != Some(row.id)
            {
                return Err(incomplete());
            }
            None
        }
    } else {
        None
    };
    if result.is_none()
        && row
            .props
            .get("owningMembership")
            .is_some_and(|v| !v.is_null())
    {
        return Err(incomplete());
    }
    if row
        .props
        .get("owningNamespace")
        .is_some_and(|value| match result {
            Some(parent) => value.as_reference() != Some(r.b.elements[parent].id),
            None => !value.is_null(),
        })
    {
        return Err(incomplete());
    }
    Ok(result)
}
fn local(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    mut owner: usize,
    name: &str,
    steps: &mut usize,
    effective: &'static str,
) -> Result<Option<Membership>, OperationError> {
    let mut seen = HashSet::new();
    loop {
        charge(steps, 1, effective)?;
        if !seen.insert(owner) || seen.len() > crate::json::MAX_RESOLUTION_DEPTH {
            return Err(OperationError::Incomplete { effective });
        }
        let Some(parent) = parent(r, raw, owner, steps, effective)? else {
            return global(r, raw, name, steps, effective);
        };
        let values = imports::sequence(r, raw, owner, &[], steps, effective)?.all;
        if let Some(member) = find(r, values, name, steps, effective)? {
            return Ok(Some(member));
        }
        owner = parent;
    }
}
pub(super) fn invoke(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    signature: &OperationExecutionSignature,
    arguments: &[DerivedValue],
    body: Body,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let (_, _, result) =
        super::with_stable_evidence(r, receiver, steps, effective, |r, raw, steps| {
            let DerivedValue::Str(name) = &arguments[0] else {
                unreachable!("validated string")
            };
            charge(steps, name.len(), effective)?;
            let result = match body {
                Body::ResolveLocal => local(r, raw, receiver.0, name, steps, effective)?,
                Body::Resolve | Body::ResolveGlobal => {
                    let (explicit_global, names) =
                        qualified_names(name, effective, signature, steps)?;
                    let is_global = explicit_global || matches!(body, Body::ResolveGlobal);
                    let mut names = names.into_iter();
                    let name = names.next().expect("qualified syntax has a name");
                    let mut selected = if is_global {
                        global(r, raw, &name, steps, effective)?
                    } else {
                        local(r, raw, receiver.0, &name, steps, effective)?
                    };
                    for name in names {
                        let Some(namespace) = selected else { break };
                        if !conforms(r.b.elements[namespace.member].ty, "Namespace") {
                            selected = None;
                            break;
                        }
                        let visible = imports::visible(
                            r,
                            raw,
                            namespace.member,
                            &[],
                            false,
                            false,
                            steps,
                            effective,
                            0,
                        )?;
                        selected = find(r, visible, &name, steps, effective)?;
                    }
                    selected
                }
                _ => unreachable!("resolution body"),
            };
            Ok(result)
        })?;
    Ok(result.map_or(DerivedValue::Null, |m| {
        DerivedValue::Reference(Reference::Element(ElementRef(m.relationship)))
    }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;
    use serde_json::json;
    fn fixture() -> ResolvedModel {
        let mut model = Model::new();
        let unit = model.add_source("resolution.kerml", "package P { class Outer; package Q { class Inner; alias Alias for Inner; } private package Hidden { class Secret; } } package Elsewhere { class Global; }");
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&model)
    }
    fn call(
        r: &mut ResolvedModel,
        receiver: ElementRef,
        op: &str,
        name: &str,
    ) -> Result<DerivedValue, OperationError> {
        r.invoke_operation(
            receiver,
            &format!("Root-Namespaces-Namespace-{op}_String"),
            &[DerivedValue::Str(name.into())],
        )
        .map(|v| v.value)
    }
    fn member(r: &mut ResolvedModel, path: &str) -> DerivedValue {
        let e = r.resolve_qualified(path).unwrap();
        DerivedValue::Reference(Reference::Element(ElementRef(
            r.b.elements[e.0].owning_relationship.unwrap(),
        )))
    }
    #[test]
    fn local_resolution_searches_outers_and_qualified_resolution_keeps_memberships() {
        let mut r = fixture();
        let q = r.resolve_qualified("P::Q").unwrap();
        for (op, name, target) in [
            ("resolveLocal", "Inner", "P::Q::Inner"),
            ("resolveLocal", "Outer", "P::Outer"),
            ("resolve", "P::Outer", "P::Outer"),
            ("resolve", "$::Elsewhere::Global", "Elsewhere::Global"),
            ("resolveGlobal", "Elsewhere::Global", "Elsewhere::Global"),
        ] {
            let expected = member(&mut r, target);
            assert_eq!(call(&mut r, q, op, name).unwrap(), expected, "{op} {name}");
        }
        assert_eq!(
            call(&mut r, q, "resolve", "P::Hidden::Secret").unwrap(),
            DerivedValue::Null
        );
        assert_eq!(
            call(&mut r, q, "resolve", "NoSuchName").unwrap(),
            DerivedValue::Null
        );
        let alias = r.b.elements[q.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&m| r.b.elements[m].ty == "Membership")
            .unwrap();
        assert_eq!(
            call(&mut r, q, "resolve", "Alias").unwrap(),
            DerivedValue::Reference(Reference::Element(ElementRef(alias)))
        );
    }
    #[test]
    fn global_ambiguity_and_corrupt_lexical_ownership_are_qualified() {
        let mut m = Model::new();
        m.add_source("a.kerml", "package Root; package P;");
        m.add_source("b.kerml", "package Root;");
        let mut r = ResolvedModel::build(&m);
        let p = r.resolve_qualified("P").unwrap();
        assert!(matches!(
            call(&mut r, p, "resolveGlobal", "Root"),
            Err(OperationError::Incomplete { .. })
        ));
        let mut r = fixture();
        let q = r.resolve_qualified("P::Q").unwrap();
        r.b.elements[q.0].owning_relationship = None;
        assert!(call(&mut r, q, "resolveLocal", "Elsewhere").is_err());
        let mut r = fixture();
        let q = r.resolve_qualified("P::Q").unwrap();
        let other = r.resolve_qualified("Elsewhere").unwrap();
        r.b.set(
            q.0,
            "owningNamespace",
            json!({"@id": r.element_id(other).to_string()}),
        );
        assert!(call(&mut r, q, "resolveLocal", "Inner").is_err());
    }
}
