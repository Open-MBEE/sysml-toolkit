//! Visible foreign-owner imports share selectors without adding inheritance.
use super::*;
use crate::model::{GraphFormat, Model};
const LIB: &str = "standard library package Base {classifier Anything; feature things:Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything; feature occurrences:Occurrence subsets Base::things;} standard library package Performances {behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance {return result;} step performances:Performance subsets Occurrences::occurrences; expr evaluations:Evaluation subsets performances;}";
fn fixture(source: &str, format: GraphFormat) -> ResolvedModel {
    let mut model = Model::with_graph_format(format);
    assert!(
        model
            .add_library_source("visible-library.kerml", LIB)
            .diagnostics
            .is_empty()
    );
    let unit = model.add_source("visible-dependencies.kerml", source);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}
fn id(r: &mut ResolvedModel, name: &str) -> usize {
    r.resolve_qualified(name).unwrap().0
}

#[test]
fn visible_foreign_and_ancestor_imports_preserve_positional_roles_and_memberships() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for (declaration, role) in [
            ("class", "end feature"),
            ("behavior", "in"),
            ("function", "return"),
        ] {
            let source = format!(
                "class Extras {{feature auxiliary;}} package Catalog {{class Marker; alias MarkerAlias for Marker; feature extra; alias featureAlias for Extras::auxiliary;}} {declaration} Original {{protected import Catalog::extra; {role} original;}} {declaration} Foreign specializes Original {{public import Catalog::Marker; protected import Catalog::MarkerAlias; public import Catalog::featureAlias; {role} selected;}} {declaration} Provider {{public import Foreign::selected;}} {declaration} Bridge specializes Provider; {declaration} Child specializes Bridge {{{role} replacement;}} {declaration} Actual specializes Foreign;"
            );
            let mut r = fixture(&source, format);
            let child = id(&mut r, "Child");
            let actual = id(&mut r, "Actual");
            let selected = id(&mut r, "Foreign::selected");
            let original = id(&mut r, "Original::original");
            let replacement = id(&mut r, "Child::replacement");
            let marker = id(&mut r, "Catalog::Marker");
            let extra = id(&mut r, "Catalog::extra");
            let auxiliary = id(&mut r, "Extras::auxiliary");
            let result =
                r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0);
            if format == GraphFormat::LegacyV2 {
                assert!(result.is_err());
                continue;
            }
            let proof = result.unwrap_or_else(|e| panic!("{declaration}: {e:?}"));
            assert_eq!(
                proof.required_positional.get(&selected),
                Some(&vec![original])
            );
            // A parameter pairs with the inherited one at its position as
            // an end or a result does.
            assert_eq!(
                proof.required_positional.get(&replacement),
                Some(&vec![selected])
            );
            assert!(proof.inherited.is_empty());
            let actual =
                r.b.checked_type_membership_operation(actual, &[], &[], true, &mut 0)
                    .unwrap();
            let members = actual
                .inherited
                .iter()
                .map(|m| m.member)
                .collect::<Vec<_>>();
            assert!(members.contains(&selected));
            assert!(members.contains(&extra));
            assert!(members.contains(&auxiliary));
            assert_eq!(members.iter().filter(|&&m| m == marker).count(), 2);
        }
    }
}

#[test]
fn foreign_namespace_imports_use_complete_acyclic_package_selection() {
    for package in [
        "package Catalog {}",
        "package Catalog {class Marker; feature extra;}",
        "package Leaf {class Marker; feature extra;} package Catalog {public import Leaf::*;}",
    ] {
        let mut r = fixture(
            &format!(
                "{package} class Foreign {{public import Catalog::*; end feature selected;}} class Provider {{public import Foreign::selected;}} class Child specializes Provider;"
            ),
            GraphFormat::CanonicalV3,
        );
        let child = id(&mut r, "Child");
        let selected = id(&mut r, "Foreign::selected");
        let proof =
            r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
                .unwrap();
        assert_eq!(
            proof.inherited.iter().map(|m| m.member).collect::<Vec<_>>(),
            vec![selected]
        );
    }
}

#[test]
fn nested_positional_imports_and_unproved_lookup_domains_stay_qualified() {
    for prefix in [
        "class Extra {end feature outside;} package Catalog {alias extra for Extra::outside;}",
        // Structural rejection fixture: the non-end relay is not a conformant
        // end redefinition, and cannot conceal the nested role dependency.
        "class Extra {end feature outside;} class Relay {feature selected redefines Extra::outside;} package Catalog {alias extra for Relay::selected;}",
        "package Leaf {class Marker;} package Catalog {public import Leaf::**;}",
        "package Catalog {public import Other::*;} package Other {public import Catalog::*;}",
    ] {
        let mut r = fixture(
            &format!(
                "{prefix} class Foreign {{public import Catalog::*; end feature selected;}} class Provider {{public import Foreign::selected;}} class Child specializes Provider;"
            ),
            GraphFormat::CanonicalV3,
        );
        let child = id(&mut r, "Child");
        let foreign = id(&mut r, "Foreign");
        let catalog = id(&mut r, "Catalog");
        assert!(
            r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
                .is_err(),
            "{prefix}"
        );
        assert!(
            r.b.checked_type_membership_operation(child, &[catalog], &[foreign], true, &mut 0)
                .is_err(),
            "{prefix}"
        );
    }
}

#[test]
fn foreign_import_endpoint_inverse_and_visibility_mutations_are_observed() {
    let mut r = fixture(
        "package Catalog {class Marker;} class Foreign {public import Catalog::*; end feature selected;} class Provider {public import Foreign::selected;} class Child specializes Provider; class Actual specializes Foreign;",
        GraphFormat::CanonicalV3,
    );
    let child = id(&mut r, "Child");
    let foreign = id(&mut r, "Foreign");
    let selected = id(&mut r, "Foreign::selected");
    let actual = id(&mut r, "Actual");
    let marker = id(&mut r, "Catalog::Marker");
    let mut exhausted = crate::eval::MAX_STEPS;
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut exhausted)
            .is_err()
    );
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    let import = *r.b.elements[foreign]
        .owned_relationships
        .iter()
        .find(|&&e| conforms(r.b.elements[e].ty, "Import"))
        .unwrap();
    let props = r.b.elements[import].props.clone();
    let wrong = r.b.elements[selected].id.to_string();
    r.b.set(
        import,
        "importedNamespace",
        serde_json::json!({"@id":wrong}),
    );
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_err()
    );
    r.b.elements[import].props = props;
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    r.b.set(import, "visibility", serde_json::json!("unknown"));
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_err()
    );
    r.b.set(import, "visibility", serde_json::json!("protected"));
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    let exported =
        r.b.checked_type_membership_operation(actual, &[], &[], true, &mut 0)
            .unwrap();
    assert!(exported.inherited.iter().any(|m| m.member == marker));
    r.b.set(import, "visibility", serde_json::json!("private"));
    let hidden =
        r.b.checked_type_membership_operation(actual, &[], &[], true, &mut 0)
            .unwrap();
    assert!(!hidden.inherited.iter().any(|m| m.member == marker));
    let proof_only =
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .unwrap();
    assert_eq!(
        proof_only
            .inherited
            .iter()
            .map(|m| m.member)
            .collect::<Vec<_>>(),
        vec![selected]
    );
    r.b.set(import, "visibility", serde_json::json!("public"));
    let restored =
        r.b.checked_type_membership_operation(actual, &[], &[], true, &mut 0)
            .unwrap();
    assert!(restored.inherited.iter().any(|m| m.member == marker));
    let metadata = r.b.metadata_of.clone();
    r.b.metadata_of.insert(foreign, vec![selected]);
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_err()
    );
    r.b.metadata_of = metadata;
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
    let owned = r.b.elements[foreign].owned_relationships.clone();
    r.b.elements[foreign]
        .owned_relationships
        .make_mut()
        .retain(|&e| e != import);
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_err()
    );
    r.b.elements[foreign].owned_relationships = owned;
    assert!(
        r.b.checked_type_membership_operation(child, &[], &[], true, &mut 0)
            .is_ok()
    );
}
