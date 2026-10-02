//! Recursive visibility traverses admitted Feature namespaces with full Type evidence.
use super::*;
use crate::model::{GraphFormat, Model};

const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;}";
const SOURCE: &str = "class BaseType { class Inherited; }
class Outer {
    feature plain;
    feature typedSlot : BaseType subsets Occurrences::occurrences {class Local;}
    private feature hidden {class Secret;}
}
package Consumer {public import Outer::**;}";
fn fixture(format: GraphFormat, source: &str) -> ResolvedModel {
    let mut model = Model::with_graph_format(format);
    model.add_library_source("recursive-library.kerml", LIB);
    let unit = model.add_source("recursive-features.kerml", source);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}
fn memberships_for(r: &mut ResolvedModel, names: &[&str]) -> DerivedValue {
    DerivedValue::References(
        names
            .iter()
            .map(|name| {
                let element = r.resolve_qualified(name).unwrap();
                Reference::Element(ElementRef(
                    r.b.elements[element.0].owning_relationship.unwrap(),
                ))
            })
            .collect(),
    )
}
fn visible(
    r: &mut ResolvedModel,
    owner: ElementRef,
    all: bool,
) -> Result<DerivedValue, OperationError> {
    r.invoke_operation(
        owner,
        "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean",
        &[
            DerivedValue::Elements(vec![]),
            DerivedValue::Bool(true),
            DerivedValue::Bool(all),
        ],
    )
    .map(|result| {
        assert_eq!(
            result.effective,
            "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean"
        );
        result.value
    })
}
#[test]
fn recursive_feature_namespaces_preserve_order_visibility_and_inherited_memberships() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(format, SOURCE);
        let outer = r.resolve_qualified("Outer").unwrap();
        let expected = memberships_for(
            &mut r,
            &[
                "Outer::plain",
                "Outer::typedSlot",
                "Outer::typedSlot::Local",
                "BaseType::Inherited",
            ],
        );
        assert_eq!(
            visible(&mut r, outer, false),
            Ok(expected.clone()),
            "{format:?}"
        );
        let all = memberships_for(
            &mut r,
            &[
                "Outer::plain",
                "Outer::typedSlot",
                "Outer::hidden",
                "Outer::typedSlot::Local",
                "BaseType::Inherited",
                "Outer::hidden::Secret",
            ],
        );
        assert_eq!(visible(&mut r, outer, true), Ok(all), "{format:?}");
        let consumer = r.resolve_qualified("Consumer").unwrap();
        let imported = r
            .invoke_operation(
                consumer,
                "Root-Namespaces-Namespace-importedMemberships_Namespace",
                &[DerivedValue::Elements(vec![])],
            )
            .unwrap();
        let imported_expected = memberships_for(
            &mut r,
            &[
                "Outer",
                "Outer::plain",
                "Outer::typedSlot",
                "Outer::typedSlot::Local",
                "BaseType::Inherited",
            ],
        );
        assert_eq!(imported.value, imported_expected);
        let excluded = r
            .invoke_operation(
                consumer,
                "Root-Namespaces-Namespace-importedMemberships_Namespace",
                &[DerivedValue::Elements(vec![outer])],
            )
            .unwrap();
        // MembershipImport includes its selected Membership even when Namespace
        // exclusion suppresses the recursively imported descendants.
        assert_eq!(excluded.value, memberships_for(&mut r, &["Outer"]));
        // Namespace exclusions affect imports, not the receiver's own descendants.
        let direct = r
            .invoke_operation(
                outer,
                "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean",
                &[
                    DerivedValue::Elements(vec![outer]),
                    DerivedValue::Bool(true),
                    DerivedValue::Bool(false),
                ],
            )
            .unwrap();
        assert_eq!(direct.value, expected);
    }
}
#[test]
fn recursive_feature_imports_admit_cold_package_queries() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(format, SOURCE);
        let consumer = r.resolve_qualified("Consumer").unwrap();
        let expected = memberships_for(
            &mut r,
            &[
                "Outer",
                "Outer::plain",
                "Outer::typedSlot",
                "Outer::typedSlot::Local",
                "BaseType::Inherited",
            ],
        );
        let result = r
            .invoke_operation(
                consumer,
                "Root-Namespaces-Namespace-importedMemberships_Namespace",
                &[DerivedValue::Elements(vec![])],
            )
            .unwrap();
        assert_eq!(result.value, expected, "{format:?}");
    }
}

#[test]
fn recursive_feature_import_and_resolution_admit_cold_entry_points() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for direct_import in [false, true] {
            let mut r = fixture(format, SOURCE);
            let consumer = r.resolve_qualified("Consumer").unwrap();
            if direct_import {
                let relationship = r.b.elements[consumer.0]
                    .owned_relationships
                    .iter()
                    .copied()
                    .find(|&rel| conforms(r.b.elements[rel].ty, "Import"))
                    .unwrap();
                let expected = memberships_for(
                    &mut r,
                    &[
                        "Outer",
                        "Outer::plain",
                        "Outer::typedSlot",
                        "Outer::typedSlot::Local",
                        "BaseType::Inherited",
                    ],
                );
                let result = r
                    .invoke_operation(
                        ElementRef(relationship),
                        "Root-Namespaces-MembershipImport-importedMemberships_Namespace",
                        &[DerivedValue::Elements(vec![])],
                    )
                    .unwrap();
                assert_eq!(result.value, expected, "{format:?}");
            } else {
                let local = r.resolve_qualified("Outer::typedSlot::Local").unwrap();
                let relationship = ElementRef(r.b.elements[local.0].owning_relationship.unwrap());
                let result = r
                    .invoke_operation(
                        consumer,
                        "Root-Namespaces-Namespace-resolveVisible_String",
                        &[DerivedValue::Str("Local".into())],
                    )
                    .unwrap();
                assert_eq!(
                    result.value,
                    DerivedValue::Reference(Reference::Element(relationship)),
                    "{format:?}"
                );
            }
        }
    }
}
#[test]
fn recursive_package_visibility_initializes_type_evidence_without_imports() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut r = fixture(format, "package Holder {class Outer {feature plain;}}");
        let holder = r.resolve_qualified("Holder").unwrap();
        let expected = memberships_for(&mut r, &["Holder::Outer", "Holder::Outer::plain"]);
        let result = r
            .invoke_operation(
                holder,
                "Root-Namespaces-Namespace-visibleMemberships_Namespace_Boolean_Boolean",
                &[
                    DerivedValue::Elements(vec![]),
                    DerivedValue::Bool(true),
                    DerivedValue::Bool(false),
                ],
            )
            .unwrap();
        assert_eq!(result.value, expected, "{format:?}");
    }
}
#[test]
fn cold_recursive_preparation_retry_keeps_one_work_allowance() {
    let effective = "Kernel-Packages-Package-importedMemberships_Namespace";
    let mut r = fixture(GraphFormat::CanonicalV3, SOURCE);
    let consumer = r.resolve_qualified("Consumer").unwrap();
    let mut needed = 0;
    prepare(&mut r, consumer, &mut needed, effective, &[]).unwrap();
    assert!(needed > 1 && needed < crate::eval::MAX_STEPS);
    let mut retry = fixture(GraphFormat::CanonicalV3, SOURCE);
    let consumer = retry.resolve_qualified("Consumer").unwrap();
    let mut steps = crate::eval::MAX_STEPS - needed + 1;
    assert!(prepare(&mut retry, consumer, &mut steps, effective, &[]).is_err());
    assert!(steps >= crate::eval::MAX_STEPS);
    // A failed cold attempt must not poison a subsequent full-budget query.
    let result = retry
        .invoke_operation(consumer, effective, &[DerivedValue::Elements(vec![])])
        .unwrap();
    assert_eq!(
        result.value,
        memberships_for(
            &mut retry,
            &[
                "Outer",
                "Outer::plain",
                "Outer::typedSlot",
                "Outer::typedSlot::Local",
                "BaseType::Inherited",
            ]
        )
    );
}
#[test]
fn recursive_feature_visibility_rejects_incomplete_ownership_metadata_and_feature_families() {
    for mutation in 0..4 {
        let mut r = fixture(GraphFormat::CanonicalV3, SOURCE);
        let outer = r.resolve_qualified("Outer").unwrap();
        let typed = r.resolve_qualified("Outer::typedSlot").unwrap();
        let local = r.resolve_qualified("Outer::typedSlot::Local").unwrap();
        assert!(visible(&mut r, outer, false).is_ok());
        let membership = r.b.elements[local.0].owning_relationship.unwrap();
        match mutation {
            0 => r.b.elements[typed.0]
                .owned_relationships
                .make_mut()
                .retain(|&rel| rel != membership),
            1 => {
                r.b.metadata_of.insert(typed.0, vec![typed.0]);
            }
            2 => {
                r.b.set(typed.0, "direction", serde_json::json!("in"));
            }
            _ => {
                r.b.set(typed.0, "isEnd", serde_json::json!(true));
            }
        }
        assert!(
            matches!(
                visible(&mut r, outer, false),
                Err(OperationError::Incomplete { .. })
            ),
            "mutation {mutation}"
        );
    }
    for source in [
        "class Outer {feature valued=1;}",
        "class Outer {feature nested {feature child;}}",
    ] {
        let mut r = fixture(GraphFormat::CanonicalV3, source);
        let outer = r.resolve_qualified("Outer").unwrap();
        assert!(matches!(
            visible(&mut r, outer, false),
            Err(OperationError::Incomplete { .. })
        ));
    }
}
#[test]
fn recursive_feature_visibility_observes_mutations_and_budget_retry() {
    let mut r = fixture(GraphFormat::CanonicalV3, SOURCE);
    let outer = r.resolve_qualified("Outer").unwrap();
    let expected = visible(&mut r, outer, false).unwrap();
    let effective = "Core-Types-Type-visibleMemberships_Namespace_Boolean_Boolean";
    let signature = crate::json::operations::operation_execution_signature(effective).unwrap();
    let arguments = [
        DerivedValue::Elements(vec![]),
        DerivedValue::Bool(true),
        DerivedValue::Bool(false),
    ];
    assert!(matches!(
        invoke(
            &mut r,
            outer,
            effective,
            signature,
            &arguments,
            Body::Visible,
            crate::eval::MAX_STEPS
        ),
        Err(OperationError::WorkLimit { .. })
    ));
    assert_eq!(visible(&mut r, outer, false), Ok(expected));
    let typed = r.resolve_qualified("Outer::typedSlot").unwrap();
    let relationship = r.b.elements[typed.0].owning_relationship.unwrap();
    r.b.set(relationship, "visibility", serde_json::json!("private"));
    let expected = memberships_for(&mut r, &["Outer::plain"]);
    assert_eq!(visible(&mut r, outer, false), Ok(expected));
}

#[test]
fn package_owned_feature_roots_keep_the_same_narrow_flag_boundary() {
    for (key, value) in [
        ("isEnd", serde_json::json!(true)),
        ("direction", serde_json::json!("in")),
    ] {
        let mut r = fixture(GraphFormat::CanonicalV3, "feature plain;");
        let feature = r.resolve_qualified("plain").unwrap();
        assert_eq!(
            visible(&mut r, feature, false),
            Ok(DerivedValue::References(vec![]))
        );
        r.b.set(feature.0, key, value);
        assert!(
            matches!(
                visible(&mut r, feature, false),
                Err(OperationError::Incomplete { .. })
            ),
            "{key}"
        );
    }
}
