//! `Namespace::resolveGlobal` and `resolve` through `invoke_operation`
//! resolve names as KerML 8.2.3.5 does, visibility included, on ordinary
//! models: the specification's Annex A vehicle model, and the visibility
//! table of a small one. `ResolvedModel::resolve_qualified` stays the
//! lookup by qualified name whatever the visibility.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, OperationError, Reference, ResolvedModel},
    model::Model,
};

const RESOLVE_GLOBAL: &str = "Root-Namespaces-Namespace-resolveGlobal_String";
const RESOLVE: &str = "Root-Namespaces-Namespace-resolve_String";

fn with_library(name: &str, source: &str) -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(name, source);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

fn membership_of(r: &mut ResolvedModel, e: ElementRef) -> ElementRef {
    let id = r.property(e, "owningRelationship").unwrap()["@id"]
        .as_str()
        .expect("a member has an owning membership")
        .to_owned();
    r.element_by_id(&id).unwrap()
}

fn resolve_global(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    name: &str,
) -> Result<Option<ElementRef>, OperationError> {
    match r
        .invoke_operation(receiver, RESOLVE_GLOBAL, &[DerivedValue::Str(name.into())])?
        .value
    {
        DerivedValue::Null => Ok(None),
        DerivedValue::Reference(Reference::Element(m)) => Ok(Some(m)),
        other => panic!("{name}: {other:?}"),
    }
}

/// Whether every membership from `e` up to the root is public, which is
/// what makes `e`'s own qualified name resolvable globally.
fn publicly_reachable(r: &mut ResolvedModel, mut e: ElementRef) -> bool {
    loop {
        let Some(owner) = r.owner(e) else {
            return true;
        };
        let membership = membership_of(r, e);
        let visibility = r.element_properties(membership).get("visibility").cloned();
        if visibility.is_some_and(|v| v.as_str() != Some("public")) {
            return false;
        }
        e = owner;
    }
}

/// Every named element of the Annex A model resolves by its own qualified
/// name through `resolveGlobal` (its memberships are all public; a
/// non-public one would resolve to nothing); no name is refused.
#[test]
fn annex_a_qualified_names_resolve_globally() {
    let path = sysmlv2_testkit::corpus_root()
        .join("sysml/src/examples/Vehicle Example/SysML v2 Spec Annex A SimpleVehicleModel.sysml");
    let source = std::fs::read_to_string(&path).unwrap();
    let mut r = with_library("SimpleVehicleModel.sysml", &source);
    let root = r.resolve_qualified("SimpleVehicleModel").unwrap();
    let users: Vec<ElementRef> = r.user_elements().collect();
    let named: Vec<(ElementRef, String)> = users
        .into_iter()
        .filter_map(|e| r.element_qualified_name(e).map(|name| (e, name)))
        .collect();
    assert!(named.len() > 700, "{} named elements", named.len());
    let mut refused = Vec::new();
    let mut mismatched = Vec::new();
    let mut hidden = 0;
    for (e, name) in &named {
        match resolve_global(&mut r, root, name) {
            Ok(Some(m)) => {
                if r.membership_member(m) != Some(*e) {
                    mismatched.push(name.clone());
                }
            }
            Ok(None) => {
                if publicly_reachable(&mut r, *e) {
                    mismatched.push(format!("{name} (none)"));
                } else {
                    hidden += 1;
                }
            }
            Err(error) => {
                let blocker = match &error {
                    OperationError::Incomplete {
                        blocker: Some(b), ..
                    } => r
                        .element_qualified_name(*b)
                        .unwrap_or_else(|| r.element_type(*b).to_owned()),
                    _ => String::new(),
                };
                refused.push(format!("{name}: {error} [{blocker}]"));
            }
        }
    }
    assert!(
        refused.is_empty(),
        "{} refused:\n{}",
        refused.len(),
        refused.join("\n")
    );
    assert!(
        mismatched.is_empty(),
        "{} mismatched:\n{}",
        mismatched.len(),
        mismatched.join("\n")
    );
    // Every path in this model is public, so nothing resolves to null.
    assert_eq!(hidden, 0);
}

/// The issue's visibility table (KerML 8.2.3.5.1, 8.2.3.5.3) on SysML
/// definitions, and the compatibility lookup beside it.
#[test]
fn resolution_respects_visibility_where_the_compatibility_lookup_does_not() {
    let mut r = with_library(
        "scopes.sysml",
        "package Scopes {
            part def P;
            part def Base { part a : P; protected part b : P; private part c : P; }
            part def Derived :> Base { part d : P; }
            package Inner { public import Scopes::Base::*; part x : P; }
            package Hidden { private part h : P; }
        }",
    );
    let scopes = r.resolve_qualified("Scopes").unwrap();
    let a = r.resolve_qualified("Scopes::Base::a").unwrap();
    let a_membership = membership_of(&mut r, a);
    let p = r.resolve_qualified("Scopes::P").unwrap();
    let p_membership = membership_of(&mut r, p);
    for (name, expected) in [
        ("Scopes::Base::a", Some(a_membership)),
        ("Scopes::Base::b", None),
        ("Scopes::Derived::a", Some(a_membership)),
        ("Scopes::Inner::a", Some(a_membership)),
        ("Scopes::Hidden::h", None),
    ] {
        assert_eq!(
            resolve_global(&mut r, scopes, name).unwrap(),
            expected,
            "{name}"
        );
    }
    let base = r.resolve_qualified("Scopes::Base").unwrap();
    let derived = r.resolve_qualified("Scopes::Derived").unwrap();
    let resolve = |r: &mut ResolvedModel, receiver: ElementRef, name: &str| {
        r.invoke_operation(receiver, RESOLVE, &[DerivedValue::Str(name.into())])
            .unwrap()
            .value
    };
    let found = |m: ElementRef| DerivedValue::Reference(Reference::Element(m));
    assert_eq!(resolve(&mut r, base, "P"), found(p_membership));
    assert_eq!(resolve(&mut r, base, "a"), found(a_membership));
    assert_eq!(resolve(&mut r, derived, "a"), found(a_membership));
    assert_eq!(resolve(&mut r, derived, "c"), DerivedValue::Null);
    // The compatibility lookup by qualified name, whatever the visibility.
    for name in ["Scopes::Base::b", "Scopes::Base::c", "Scopes::Hidden::h"] {
        assert!(r.resolve_qualified(name).is_some(), "{name}");
    }
}

/// An import whose target does not resolve blocks only the names that
/// would have to go through it, and the refusal names the import.
#[test]
fn an_unresolved_import_is_named_and_does_not_hide_owned_members() {
    let mut r = with_library(
        "imports.sysml",
        "package A { public import Nothing::*; package B; }",
    );
    let a = r.resolve_qualified("A").unwrap();
    let b = r.resolve_qualified("A::B").unwrap();
    let b_membership = membership_of(&mut r, b);
    assert_eq!(
        resolve_global(&mut r, a, "A::B").unwrap(),
        Some(b_membership)
    );
    let import = r
        .owned_relationships(a)
        .into_iter()
        .find(|&rel| r.element_type(rel) == "NamespaceImport")
        .unwrap();
    match resolve_global(&mut r, a, "A::X") {
        Err(OperationError::Incomplete {
            blocker: Some(blocker),
            ..
        }) => assert_eq!(blocker, import),
        other => panic!("{other:?}"),
    }
}
