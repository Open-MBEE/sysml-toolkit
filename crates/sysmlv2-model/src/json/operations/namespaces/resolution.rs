//! Membership-valued resolution with explicit, checked multi-unit global scope.
use super::*;
use crate::metaclass::is_a;
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
/// The owned Membership of `owner` named `name`, public only when
/// `public_only`, before any import or inheritance is composed: an owned
/// member hides an imported or inherited one of the same name (KerML
/// 8.2.3.5.1), so a match here is the answer whatever the rest of the
/// namespace's evidence, and a miss says nothing.
fn owned_match(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    owner: usize,
    name: &str,
    public_only: bool,
    steps: &mut usize,
    effective: &'static str,
) -> Result<Option<Membership>, OperationError> {
    let incomplete = || blocked(effective, owner);
    if !raw
        .import_domains(&r.b, steps)
        .ok_or_else(incomplete)?
        .owner_complete(owner)
    {
        return Err(incomplete());
    }
    let mut values = owned_memberships_of_namespace(&r.b, raw, owner, steps, effective)?;
    if public_only {
        values.retain(|m| m.visibility == "public");
    }
    charge(steps, values.len(), effective)?;
    let mut found: Option<Membership> = None;
    for value in values {
        if member_names(r, &value, steps, effective)?
            .iter()
            .any(|n| n == name)
        {
            if found
                .as_ref()
                .is_some_and(|m| m.relationship != value.relationship)
            {
                return Err(blocked(effective, value.relationship));
            }
            found = Some(value);
        }
    }
    Ok(found)
}
/// Whether any source-unit root owns a public Import: only then can a root's
/// imports bind a global name that another root's owned member also binds,
/// which the full composition detects as an ambiguity.
fn roots_import_publicly(
    r: &ResolvedModel,
    roots: &[usize],
    steps: &mut usize,
    effective: &'static str,
) -> Result<bool, OperationError> {
    for &root in roots {
        let relationships = &r.b.elements[root].owned_relationships;
        charge(steps, relationships.len(), effective)?;
        if relationships.iter().any(|&relationship| {
            is_a!(r.b.elements[relationship], "Import")
                && visibility(r, relationship) != Some("private")
        }) {
            return Ok(true);
        }
    }
    Ok(false)
}
fn global(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    name: &str,
    steps: &mut usize,
    effective: &'static str,
) -> Result<Option<Membership>, OperationError> {
    // The toolkit's global environment is the union of its source-unit root
    // Namespaces, including prepared library units. Unlike compatibility root
    // lookup, duplicate global bindings are qualified instead of selecting a
    // winner by source-unit insertion order.
    charge(steps, r.b.unit_starts.len(), effective)?;
    let roots: Vec<_> = r.b.unit_starts.iter().map(|&(root, _)| root).collect();
    for &root in &roots {
        if r.b.elements[root].ty != "Namespace" || r.b.elements[root].owning_relationship.is_some()
        {
            return Err(blocked(effective, root));
        }
    }
    // Owned first: a name one root's owned member binds is answered before
    // any root's imports are composed, unless a root imports publicly, where
    // an import could bind the same name and make it ambiguous.
    if !roots_import_publicly(r, &roots, steps, effective)? {
        let mut result: Option<Membership> = None;
        for &root in &roots {
            if let Some(value) = owned_match(r, raw, root, name, false, steps, effective)? {
                if result
                    .as_ref()
                    .is_some_and(|m| m.relationship != value.relationship)
                {
                    return Err(blocked(effective, value.relationship));
                }
                result = Some(value);
            }
        }
        if result.is_some() {
            return Ok(result);
        }
    }
    let mut result: Option<Membership> = None;
    for root in roots {
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
                    return Err(blocked(effective, value.relationship));
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
    let incomplete = || blocked(effective, owner);
    charge(steps, 8, effective)?;
    let row = &r.b.elements[owner];
    if row.owning_relationship.is_none() {
        charge(steps, r.b.unit_starts.len(), effective)?;
        if !r.b.unit_starts.iter().any(|&(root, _)| root == owner) {
            return Err(incomplete());
        }
    }
    let result = if let Some(relationship) = row.owning_relationship {
        if is_a!(r.b.elements[relationship], "OwningMembership") {
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
            if !is_a!(relation, "Import")
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
            return Err(blocked(effective, owner));
        }
        let Some(parent) = parent(r, raw, owner, steps, effective)? else {
            return global(r, raw, name, steps, effective);
        };
        // An owned member of any visibility answers before the namespace's
        // imports and inheritance are composed.
        if let Some(member) = owned_match(r, raw, owner, name, false, steps, effective)? {
            return Ok(Some(member));
        }
        let values = imports::sequence(r, raw, owner, &[], steps, effective)?.all;
        if let Some(member) = find(r, values, name, steps, effective)? {
            return Ok(Some(member));
        }
        owner = parent;
    }
}
/// The segments of a qualified name, resolved from the global scope or
/// locally from `receiver`, then through each namespace in turn.
pub(in crate::json) fn resolve_segments(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    is_global: bool,
    receiver: usize,
    names: &[String],
    steps: &mut usize,
    effective: &'static str,
) -> Result<Option<Membership>, OperationError> {
    let mut names = names.iter();
    let name = names.next().expect("qualified syntax has a name");
    let mut selected = if is_global {
        global(r, raw, name, steps, effective)?
    } else {
        local(r, raw, receiver, name, steps, effective)?
    };
    for name in names {
        let Some(namespace) = selected else { break };
        if !is_a!(r.b.elements[namespace.member], "Namespace") {
            selected = None;
            break;
        }
        // A public owned member answers before the visible memberships
        // are composed (8.2.3.5.1: the last segment resolves among the
        // visible memberships, which an owned one hides by name).
        selected = match owned_match(r, raw, namespace.member, name, true, steps, effective)? {
            Some(member) => Some(member),
            None => {
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
                find(r, visible, name, steps, effective)?
            }
        };
    }
    Ok(selected)
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
                    resolve_segments(r, raw, is_global, receiver.0, &names, steps, effective)?
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
    fn duplicate_owned_global_names_in_one_unit_are_refused() {
        for source in [
            "package R; package R; package Q;",
            "package R; alias R for R; package Q;",
        ] {
            let mut model = Model::new();
            model.add_source("duplicates.kerml", source);
            let mut r = ResolvedModel::build(&model);
            let q = r.resolve_qualified("Q").unwrap();
            assert!(
                matches!(
                    call(&mut r, q, "resolveGlobal", "R"),
                    Err(OperationError::Incomplete {
                        blocker: Some(_),
                        ..
                    })
                ),
                "{source}"
            );
            assert_eq!(
                call(&mut r, q, "resolveGlobal", "Q").unwrap(),
                member(&mut r, "Q")
            );
        }
    }

    const KERNEL: &str = "standard library package Base { classifier Anything; datatype DataValue specializes Anything; feature things : Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences : Occurrence subsets Base::things; }";
    fn kernel_fixture(source: &str) -> ResolvedModel {
        let mut model = Model::new();
        assert!(
            model
                .add_library_source("kernel.kerml", KERNEL)
                .diagnostics
                .is_empty()
        );
        let unit = model.add_source("scopes.kerml", source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&model)
    }
    /// KerML 8.2.3.5: a qualified name resolves its last segment among the
    /// visible memberships of its qualification, and a plain name among a
    /// namespace's own memberships, inherited and imported ones included,
    /// then its outers'.
    #[test]
    fn resolution_follows_visibility_inheritance_and_imports() {
        let mut r = kernel_fixture(
            "package Scopes {
                class P;
                class Base { feature a : P; protected feature b : P; private feature c : P; }
                class Derived specializes Base { feature d : P; }
                package Inner { public import Scopes::Base::*; feature x : P; }
                package Hidden { private feature h : P; }
            }",
        );
        let scopes = r.resolve_qualified("Scopes").unwrap();
        let a = member(&mut r, "Scopes::Base::a");
        let p = member(&mut r, "Scopes::P");
        for (name, expected) in [
            ("Scopes::Base::a", a.clone()),
            ("Scopes::Base::b", DerivedValue::Null),
            ("Scopes::Derived::a", a.clone()),
            ("Scopes::Inner::a", a.clone()),
            ("Scopes::Hidden::h", DerivedValue::Null),
            ("Scopes::P", p.clone()),
        ] {
            assert_eq!(
                call(&mut r, scopes, "resolveGlobal", name).unwrap(),
                expected,
                "{name}"
            );
        }
        let base = r.resolve_qualified("Scopes::Base").unwrap();
        let derived = r.resolve_qualified("Scopes::Derived").unwrap();
        assert_eq!(call(&mut r, base, "resolve", "P").unwrap(), p);
        assert_eq!(call(&mut r, base, "resolve", "a").unwrap(), a);
        assert_eq!(call(&mut r, derived, "resolve", "a").unwrap(), a);
        assert_eq!(
            call(&mut r, derived, "resolve", "c").unwrap(),
            DerivedValue::Null
        );
        // The compatibility lookup finds members whatever their visibility.
        for name in ["Scopes::Base::b", "Scopes::Base::c", "Scopes::Hidden::h"] {
            assert!(r.resolve_qualified(name).is_some(), "{name}");
        }
    }
    /// An owned member answers before the namespace's imports are composed,
    /// so an import whose target does not resolve blocks only the names
    /// that would have to go through it — and the refusal names it.
    #[test]
    fn an_unresolved_import_blocks_only_the_names_through_it_and_is_named() {
        let mut r = kernel_fixture("package A { public import Nothing::*; package B; }");
        let a = r.resolve_qualified("A").unwrap();
        let b = member(&mut r, "A::B");
        assert_eq!(call(&mut r, a, "resolveGlobal", "A::B").unwrap(), b);
        assert_eq!(call(&mut r, a, "resolveLocal", "B").unwrap(), b);
        assert_eq!(call(&mut r, a, "resolve", "B").unwrap(), b);
        let import = r.b.elements[a.0]
            .owned_relationships
            .iter()
            .copied()
            .find(|&rel| r.b.elements[rel].ty == "NamespaceImport")
            .unwrap();
        for (operation, name) in [
            ("resolveGlobal", "A::X"),
            ("resolveLocal", "X"),
            ("resolve", "X"),
            ("resolveVisible", "X"),
        ] {
            let refused = call(&mut r, a, operation, name).unwrap_err();
            assert!(
                matches!(
                    refused,
                    OperationError::Incomplete {
                        blocker: Some(ElementRef(blocker)),
                        ..
                    } if blocker == import
                ),
                "{operation} {name}: {refused:?}"
            );
            assert!(
                refused
                    .to_string()
                    .ends_with(&format!("; blocked at element {import}")),
                "{refused}"
            );
        }
    }
    /// A global name bound by one root's owned member answers without
    /// composing the other roots' imports; two roots binding it refuse,
    /// naming the second binding.
    #[test]
    fn global_owned_bindings_answer_before_root_imports_are_composed() {
        let mut m = Model::new();
        m.add_source(
            "a.kerml",
            "package P { class C; } package Q { private import Nothing::*; }",
        );
        m.add_source("b.kerml", "package R;");
        let mut r = ResolvedModel::build(&m);
        let q = r.resolve_qualified("Q").unwrap();
        assert_eq!(
            call(&mut r, q, "resolveGlobal", "P::C").unwrap(),
            member(&mut r, "P::C")
        );
        assert_eq!(
            call(&mut r, q, "resolveGlobal", "R").unwrap(),
            member(&mut r, "R")
        );
        m.add_source("c.kerml", "package R;");
        let mut r = ResolvedModel::build(&m);
        let q = r.resolve_qualified("Q").unwrap();
        assert!(matches!(
            call(&mut r, q, "resolveGlobal", "R"),
            Err(OperationError::Incomplete {
                blocker: Some(_),
                ..
            })
        ));
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
