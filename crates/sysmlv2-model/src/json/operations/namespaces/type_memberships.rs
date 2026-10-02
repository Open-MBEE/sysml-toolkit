//! Checked Type operation cases share the complete membership provider.
use super::*;
use crate::model::{GraphFormat, Model};
const LIB: &str = "standard library package Base { classifier Anything; feature things:Anything; } standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things; } standard library package Performances { behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance { return result; } step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances; }";
fn fixture(source: &str, format: GraphFormat) -> ResolvedModel {
    let mut model = Model::with_graph_format(format);
    assert!(
        model
            .add_library_source("membership-library.kerml", LIB)
            .diagnostics
            .is_empty()
    );
    let unit = model.add_source("membership-operations.kerml", source);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}
fn empty() -> DerivedValue {
    DerivedValue::Elements(vec![])
}
fn args(excluded: Vec<ElementRef>, implied: bool) -> [DerivedValue; 3] {
    [
        empty(),
        DerivedValue::Elements(excluded),
        DerivedValue::Bool(implied),
    ]
}
fn call(
    r: &mut ResolvedModel,
    owner: ElementRef,
    op: &str,
    args: &[DerivedValue],
) -> Result<DerivedValue, OperationError> {
    r.invoke_operation(
        owner,
        &format!("Core-Types-Type-{op}_Namespace_Type_Boolean"),
        args,
    )
    .map(|r| r.value)
}
fn expected(r: &mut ResolvedModel, names: &[&str]) -> DerivedValue {
    DerivedValue::References(
        names
            .iter()
            .map(|name| {
                let e = r.resolve_qualified(name).unwrap();
                Reference::Element(ElementRef(r.b.elements[e.0].owning_relationship.unwrap()))
            })
            .collect(),
    )
}
#[test]
fn type_operation_order_visibility_redefinitions_and_exclusions() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(
            "class A { protected feature guarded; feature initialSlot; private feature hidden; feature last; class Nested; } class B specializes A { protected feature ownGuard; private feature ownHidden; feature own redefines A::initialSlot; } class C specializes B;",
            format,
        );
        let b = r.resolve_qualified("B").unwrap();
        let a = r.resolve_qualified("A").unwrap();
        let inherited = expected(&mut r, &["A::last", "A::Nested", "A::guarded"]);
        let inheritable = expected(
            &mut r,
            &["A::initialSlot", "A::last", "A::Nested", "A::guarded"],
        );
        let nonprivate = expected(
            &mut r,
            &[
                "B::own",
                "B::ownGuard",
                "A::last",
                "A::Nested",
                "A::guarded",
            ],
        );
        assert_eq!(
            call(&mut r, b, "inheritedMemberships", &args(vec![], true)),
            Ok(inherited)
        );
        assert_eq!(
            call(&mut r, b, "inheritableMemberships", &args(vec![], true)),
            Ok(inheritable)
        );
        assert_eq!(
            call(&mut r, b, "nonPrivateMemberships", &args(vec![], true)),
            Ok(nonprivate)
        );
        for op in ["inheritedMemberships", "inheritableMemberships"] {
            assert_eq!(
                call(&mut r, b, op, &args(vec![a], true)),
                Ok(DerivedValue::References(vec![]))
            );
            let baseline = call(&mut r, b, op, &args(vec![], true));
            assert_eq!(call(&mut r, b, op, &args(vec![b], true)), baseline);
            let mut namespaces = args(vec![], true);
            namespaces[0] = DerivedValue::Elements(vec![a, b]);
            assert_eq!(call(&mut r, b, op, &namespaces), baseline);
        }
        let own = expected(&mut r, &["B::own", "B::ownGuard"]);
        assert_eq!(
            call(&mut r, b, "nonPrivateMemberships", &args(vec![a], true)),
            Ok(own)
        );
        let c = r.resolve_qualified("C").unwrap();
        let transitively_cut = expected(&mut r, &["B::own", "B::ownGuard"]);
        assert_eq!(
            call(&mut r, c, "inheritedMemberships", &args(vec![a], true)),
            Ok(transitively_cut)
        );
    }
}
#[test]
fn type_visible_override_has_exact_dispatch_and_visibility_order() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(
            "class A { protected feature guarded; feature inherited; } class B specializes A { private feature secret; feature own; } class C specializes A;",
            format,
        );
        let b = r.resolve_qualified("B").unwrap();
        let public = expected(&mut r, &["B::own", "A::inherited"]);
        let all = expected(
            &mut r,
            &["B::secret", "B::own", "A::inherited", "A::guarded"],
        );
        for recursive in [false, true] {
            for (include_all, expected) in [(false, public.clone()), (true, all.clone())] {
                let result = r
                    .invoke_operation(
                        b,
                        "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean",
                        &[
                            empty(),
                            DerivedValue::Bool(recursive),
                            DerivedValue::Bool(include_all),
                        ],
                    )
                    .unwrap();
                assert_eq!(
                    result.effective,
                    "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean"
                );
                assert_eq!(result.value, expected);
            }
        }
        let c = r.resolve_qualified("C").unwrap();
        for include_all in [false, true] {
            let expected = expected(
                &mut r,
                if include_all {
                    &["A::inherited", "A::guarded"]
                } else {
                    &["A::inherited"]
                },
            );
            let result = r
                .invoke_operation(
                    c,
                    "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean",
                    &[
                        empty(),
                        DerivedValue::Bool(true),
                        DerivedValue::Bool(include_all),
                    ],
                )
                .unwrap();
            assert_eq!(result.value, expected);
        }
    }
}
#[test]
fn type_alias_memberships_remain_distinct_and_private_imports_never_inherit() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(
            "package P { class Imported; } class A { class Nested; alias firstAlias for Nested; alias second for Nested; private import P::*; } class B specializes A;",
            format,
        );
        let b = r.resolve_qualified("B").unwrap();
        let a = r.resolve_qualified("A").unwrap();
        let rels: Vec<_> = r.b.elements[a.0]
            .owned_relationships
            .iter()
            .copied()
            .filter(|&rel| conforms(r.b.elements[rel].ty, "Membership"))
            .map(|rel| Reference::Element(ElementRef(rel)))
            .collect();
        assert_eq!(rels.len(), 3);
        let result = call(&mut r, b, "inheritedMemberships", &args(vec![], true)).unwrap();
        assert_eq!(result, DerivedValue::References(rels));
        for access in ["public", "protected"] {
            let import = r.b.elements[a.0]
                .owned_relationships
                .iter()
                .copied()
                .find(|&rel| conforms(r.b.elements[rel].ty, "Import"))
                .unwrap();
            r.b.set(import, "visibility", serde_json::json!(access));
            let mut excluded = args(vec![a], true);
            excluded[0] = DerivedValue::Elements(vec![r.resolve_qualified("P").unwrap()]);
            assert_eq!(
                call(&mut r, b, "inheritedMemberships", &excluded),
                Ok(DerivedValue::References(vec![]))
            );
            r.b.set(import, "visibility", serde_json::json!("private"));
        }
    }
}
#[test]
fn type_visibility_retains_import_collisions_that_namespace_prunes() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(
            "package P {class Shared;} package Q {class Shared;} class A {public import P::*; public import Q::*;} class B specializes A;",
            format,
        );
        let a = r.resolve_qualified("A").unwrap();
        let b = r.resolve_qualified("B").unwrap();
        let both = expected(&mut r, &["P::Shared", "Q::Shared"]);
        assert_eq!(
            call(&mut r, a, "nonPrivateMemberships", &args(vec![], true)),
            Ok(both.clone()),
            "{format:?}"
        );
        assert_eq!(
            call(&mut r, b, "inheritedMemberships", &args(vec![], true)),
            Ok(both),
            "{format:?}"
        );
        let pruned = r
            .invoke_operation(
                a,
                "Root-Namespaces-Namespace-importedMemberships_Namespace",
                &[empty()],
            )
            .unwrap();
        assert_eq!(pruned.value, DerivedValue::References(vec![]), "{format:?}");
    }
}
#[test]
fn implied_filter_keeps_semantic_positional_suppression() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(
            "function A { in a; feature kept; } function B specializes A { in x; }",
            format,
        );
        let b = r.resolve_qualified("B").unwrap();
        let ordinary = call(&mut r, b, "inheritedMemberships", &args(vec![], false)).unwrap();
        let explicit = expected(&mut r, &["A::kept"]);
        assert_eq!(
            call(&mut r, b, "inheritedMemberships", &args(vec![], true)),
            Ok(explicit.clone())
        );
        assert_ne!(ordinary, explicit);
        let candidates = expected(&mut r, &["A::a", "A::kept"]);
        assert_eq!(
            call(&mut r, b, "inheritableMemberships", &args(vec![], true)),
            Ok(candidates)
        );
    }
}
#[test]
fn operation_arguments_budget_and_same_identity_edits_are_checked() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(
            "class A { feature slot; } class B specializes A; package P;",
            format,
        );
        let b = r.resolve_qualified("B").unwrap();
        let a = r.resolve_qualified("A").unwrap();
        let p = r.resolve_qualified("P").unwrap();
        assert!(matches!(
            call(&mut r, b, "inheritedMemberships", &args(vec![p], true)),
            Err(OperationError::InvalidArgument {
                index: 1,
                issue: OperationArgumentIssue::WrongMetaclass { .. },
                ..
            })
        ));
        assert!(matches!(
            call(&mut r, b, "inheritedMemberships", &args(vec![a, a], true)),
            Err(OperationError::InvalidArgument {
                index: 1,
                issue: OperationArgumentIssue::DuplicateIdentity,
                ..
            })
        ));
        let baseline = call(&mut r, b, "inheritedMemberships", &args(vec![], true)).unwrap();
        let effective = "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean";
        let signature = crate::json::operations::operation_execution_signature(effective).unwrap();
        assert!(matches!(
            invoke(
                &mut r,
                b,
                effective,
                signature,
                &args(vec![], true),
                Body::Inherited,
                crate::eval::MAX_STEPS
            ),
            Err(OperationError::WorkLimit { .. })
        ));
        assert_eq!(
            call(&mut r, b, "inheritedMemberships", &args(vec![], true)),
            Ok(baseline)
        );
        let member = r.resolve_qualified("A::slot").unwrap();
        let membership = r.b.elements[member.0].owning_relationship.unwrap();
        r.b.set(membership, "visibility", serde_json::json!("private"));
        assert_eq!(
            call(&mut r, b, "inheritedMemberships", &args(vec![], true)),
            Ok(DerivedValue::References(vec![]))
        );
        r.b.elements[a.0]
            .owned_relationships
            .make_mut()
            .retain(|&rel| rel != membership);
        assert!(matches!(
            call(&mut r, b, "inheritedMemberships", &args(vec![a], true)),
            Err(OperationError::Incomplete { .. })
        ));
    }
}
#[test]
fn excluded_types_do_not_mask_cycles_or_unresolved_ancestry() {
    for source in [
        "class A specializes B; class B specializes A;",
        "class A specializes Missing; class B specializes A;",
    ] {
        let mut r = fixture(source, GraphFormat::CanonicalV3);
        let b = r.resolve_qualified("B").unwrap();
        let a = r.resolve_qualified("A").unwrap();
        assert!(matches!(
            call(&mut r, b, "inheritedMemberships", &args(vec![a], true)),
            Err(OperationError::Incomplete { .. })
        ));
    }
}

#[test]
fn named_multiplicity_members_are_not_features_and_require_complete_carriers() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(
            "class A { feature count=4; multiplicity limit[count]; feature slots {multiplicity subsets limit;} } class B specializes A;",
            format,
        );
        let a = r.resolve_qualified("A").unwrap();
        let b = r.resolve_qualified("B").unwrap();
        let limit = r.resolve_qualified("A::limit").unwrap();
        let membership = r.b.elements[limit.0].owning_relationship.unwrap();
        assert_eq!(r.b.elements[membership].ty, "OwningMembership");
        let projection = r.type_feature_report(a).projections.unwrap();
        assert!(!projection.features.contains(&limit));
        assert!(
            projection
                .owned_memberships
                .contains(&ElementRef(membership))
        );
        let inherited = call(&mut r, b, "inheritedMemberships", &args(vec![], true)).unwrap();
        assert!(
            matches!(inherited, DerivedValue::References(ref members) if members.contains(&Reference::Element(ElementRef(membership))))
        );
        r.b.set(limit.0, "direction", serde_json::json!("in"));
        assert!(r.type_feature_report(a).projections.is_err());
        r.b.set(limit.0, "direction", serde_json::Value::Null);
        assert!(r.type_feature_report(a).projections.is_ok());
        r.b.set(limit.0, "isEnd", serde_json::json!(true));
        assert!(r.type_feature_report(a).projections.is_err());
        r.b.set(limit.0, "isEnd", serde_json::json!(false));
        assert!(r.type_feature_report(a).projections.is_ok());
        r.b.elements[a.0]
            .owned_relationships
            .make_mut()
            .retain(|&m| m != membership);
        assert!(r.type_feature_report(a).projections.is_err());
    }
}
