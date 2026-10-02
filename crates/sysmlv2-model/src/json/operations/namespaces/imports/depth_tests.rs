use super::*;
use crate::model::{GraphFormat, Model};

fn chain(edges: usize) -> String {
    let mut source = format!("package P{edges} {{ class A; }}");
    for n in (0..edges).rev() {
        source.push_str(&format!("package P{n} {{public import $::P{}::*;}}", n + 1));
    }
    source
}

fn namespace_call(
    r: &mut ResolvedModel,
    owner: ElementRef,
    operation: &str,
    arguments: &[DerivedValue],
) -> Result<DerivedValue, OperationError> {
    r.invoke_operation(
        owner,
        &format!("Root-Namespaces-Namespace-{operation}"),
        arguments,
    )
    .map(|report| report.value)
}

fn references_of(r: &ResolvedModel, members: &[usize]) -> DerivedValue {
    DerivedValue::References(
        members
            .iter()
            .map(|&m| Reference::Element(ElementRef(r.b.elements[m].owning_relationship.unwrap())))
            .collect(),
    )
}

fn assert_chain(r: &mut ResolvedModel, edges: usize) {
    let owner = r.resolve_qualified("P0").unwrap();
    let terminal = r.resolve_qualified(&format!("P{edges}::A")).unwrap();
    let expected = references_of(r, &[terminal.0]);
    let empty = DerivedValue::Elements(vec![]);
    let import = ElementRef(r.b.elements[owner.0].owned_relationships[0]);
    let mut results = vec![
        r.invoke_operation(
            import,
            "Root-Namespaces-NamespaceImport-importedMemberships_Namespace",
            std::slice::from_ref(&empty),
        )
        .map(|report| report.value),
    ];
    for (op, args) in [
        ("importedMemberships_Namespace", vec![empty.clone()]),
        (
            "membershipsOfVisibility_VisibilityKind_Namespace",
            vec![DerivedValue::Null, empty.clone()],
        ),
        (
            "visibleMemberships_Namespace_Boolean_Boolean",
            vec![empty, DerivedValue::Bool(false), DerivedValue::Bool(false)],
        ),
    ] {
        results.push(namespace_call(r, owner, op, &args));
    }
    for result in results {
        if edges <= crate::json::MAX_RESOLUTION_DEPTH {
            assert_eq!(result.unwrap(), expected, "edges={edges}");
        } else {
            assert!(
                matches!(result, Err(OperationError::Incomplete { .. })),
                "edges={edges}: {result:?}"
            );
        }
    }
}

#[test]
fn import_edge_boundary_agrees_across_selectors_and_serialization() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for edges in [
            1,
            8,
            crate::json::MAX_RESOLUTION_DEPTH,
            crate::json::MAX_RESOLUTION_DEPTH + 1,
        ] {
            let mut model = Model::with_graph_format(format);
            assert!(
                model
                    .add_source("import-depth.kerml", &chain(edges))
                    .diagnostics
                    .is_empty()
            );
            assert_chain(&mut ResolvedModel::build(&model), edges);
            for document in [
                crate::json::model_to_compact_json(&model),
                crate::full::model_to_full_json(&model),
            ] {
                let (_, mut loaded, _, _) =
                    crate::loader::load_document_with_format(&document, &HashMap::new(), format)
                        .unwrap();
                assert_chain(&mut loaded, edges);
            }
        }
    }
}

#[test]
fn recursive_containment_uses_one_depth_per_child_and_preserves_order() {
    for edges in [
        crate::json::MAX_RESOLUTION_DEPTH,
        crate::json::MAX_RESOLUTION_DEPTH + 1,
    ] {
        let mut source = String::from("package P0 {");
        for n in 1..=edges {
            source.push_str(&format!("package P{n} {{"));
        }
        source.push_str(&"}".repeat(edges + 1));
        let mut model = Model::new();
        assert!(
            model
                .add_source("containment-depth.kerml", &source)
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        // Read owned rows directly: resolving a long qualified name has its own bound.
        let owner = r.resolve_qualified("P0").unwrap();
        let mut children = vec![];
        let mut parent = owner.0;
        for _ in 0..edges {
            let membership = r.b.elements[parent].owned_relationships[0];
            parent = r.b.elements[membership].children[0];
            children.push(parent);
        }
        let result = namespace_call(
            &mut r,
            owner,
            "visibleMemberships_Namespace_Boolean_Boolean",
            &[
                DerivedValue::Elements(vec![]),
                DerivedValue::Bool(true),
                DerivedValue::Bool(false),
            ],
        );
        if edges <= crate::json::MAX_RESOLUTION_DEPTH {
            assert_eq!(result.unwrap(), references_of(&r, &children));
        } else {
            assert!(matches!(result, Err(OperationError::Incomplete { .. })));
        }
    }
}

#[test]
fn import_and_containment_edges_share_one_cumulative_depth_bound() {
    let imports = 12;
    for containment in [12, 13] {
        let mut source = String::new();
        for n in 0..imports {
            source.push_str(&format!(
                "package P{n} {{public import $::P{}::*::**;}}",
                n + 1
            ));
        }
        source.push_str(&format!("package P{imports} {{"));
        for n in 0..containment {
            source.push_str(&format!("package C{n} {{"));
        }
        source.push_str(&"}".repeat(containment + 1));
        let mut model = Model::new();
        assert!(
            model
                .add_source("mixed-depth.kerml", &source)
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let owner = r.resolve_qualified("P0").unwrap();
        let tree = r.resolve_qualified(&format!("P{imports}")).unwrap();
        let mut children = vec![];
        let mut parent = tree.0;
        for _ in 0..containment {
            let membership = r.b.elements[parent].owned_relationships[0];
            parent = r.b.elements[membership].children[0];
            children.push(parent);
        }
        let result = namespace_call(
            &mut r,
            owner,
            "importedMemberships_Namespace",
            &[DerivedValue::Elements(vec![])],
        );
        if imports + containment <= crate::json::MAX_RESOLUTION_DEPTH {
            assert_eq!(result.unwrap(), references_of(&r, &children));
        } else {
            assert!(matches!(result, Err(OperationError::Incomplete { .. })));
        }
    }
}

#[test]
fn deep_imports_keep_exclusions_identity_checks_and_budget_retry() {
    let edges = 12;
    let mut model = Model::new();
    let source = format!(
        "{} package Diamond {{public import $::P0::*; public import $::P1::*;}}",
        chain(edges).replace("class A;", "class A; public import $::P0::*;")
    );
    assert!(
        model
            .add_source("deep-imports.kerml", &source)
            .diagnostics
            .is_empty()
    );
    let mut r = ResolvedModel::build(&model);
    let owner = r.resolve_qualified("Diamond").unwrap();
    let leaf = r.resolve_qualified(&format!("P{edges}::A")).unwrap();
    let expected = references_of(&r, &[leaf.0]);
    let empty = DerivedValue::Elements(vec![]);
    assert_eq!(
        namespace_call(
            &mut r,
            owner,
            "importedMemberships_Namespace",
            std::slice::from_ref(&empty)
        )
        .unwrap(),
        expected
    );
    let excluded = r.resolve_qualified("P6").unwrap();
    assert_eq!(
        namespace_call(
            &mut r,
            owner,
            "importedMemberships_Namespace",
            &[DerivedValue::Elements(vec![excluded])]
        )
        .unwrap(),
        DerivedValue::References(vec![])
    );
    let mut row = NamespaceRow::default();
    let declaration = "Root-Namespaces-Namespace-importedMembership";
    let mut steps = crate::eval::MAX_STEPS - 1;
    assert!(
        row.property(&mut r, owner, declaration, &mut steps)
            .is_err()
    );
    assert_eq!(
        row.property(&mut r, owner, declaration, &mut 0).unwrap(),
        expected
    );
    let membership = r.b.elements[leaf.0].owning_relationship.take().unwrap();
    assert!(
        namespace_call(
            &mut r,
            owner,
            "importedMemberships_Namespace",
            std::slice::from_ref(&empty)
        )
        .is_err()
    );
    r.b.elements[leaf.0].owning_relationship = Some(membership);
    assert_eq!(
        namespace_call(&mut r, owner, "importedMemberships_Namespace", &[empty]).unwrap(),
        expected
    );
}
