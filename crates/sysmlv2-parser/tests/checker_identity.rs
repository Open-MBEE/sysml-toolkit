//! Semantic diagnostics must use bound identities rather than display spellings.
#![cfg(feature = "json")]
use std::{collections::HashMap, sync::Arc};
use sysmlv2_parser::{
    check, json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};

const ID: &str = "88888888-8888-4888-8888-888888888888";

fn models(source: &str) -> Vec<Model> {
    models_in(source, "kerml")
}

fn models_in(source: &str, dialect: &str) -> Vec<Model> {
    models_with_library(
        source,
        dialect,
        "package ScalarValues { datatype Integer; datatype Boolean; } package Tags { metaclass Tag; #Tag class Tagged; }",
    )
}

fn models_with_library(source: &str, dialect: &str, library: &str) -> Vec<Model> {
    let mut base = Model::new();
    base.add_library_source("library.kerml", library);
    assert!(!base.has_errors());
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(43).unwrap(), 43).unwrap());
    (0..4)
        .map(|mode| {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("library.kerml", library);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            for package in ["A", "B"] {
                let unit = model.add_source(
                    format!("{package}.{dialect}"),
                    &format!("package {package} {{ {source} }}"),
                );
                assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            }
            model
        })
        .collect()
}

#[test]
fn scalar_conformance_uses_source_bound_identity_without_capturing_other_units() {
    for (actual, spelled, expected) in [("\"bad\"", "2", "A.kerml"), ("2", "\"bad\"", "B.kerml")] {
        let source = format!(
            "feature actual = {actual}; feature '{ID}' = {spelled}; feature checked : ScalarValues::Integer = '{ID}';"
        );
        for (mode, model) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            let actual = r.resolve_qualified("A::actual").unwrap();
            r.override_ids(&HashMap::from([(
                r.element_id(actual),
                ID.parse().unwrap(),
            )]));
            let checked = r.resolve_qualified("A::checked").unwrap();
            let value = r.members_via(checked, "FeatureValue")[0];
            let membership = r.owned_relationships(value)[0];
            let mut hints = HashMap::from([(
                (r.element_id(membership), "memberElement".into()),
                ID.parse().unwrap(),
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&ID.parse().unwrap())
            );
            for _ in 0..2 {
                let findings = check::validate_semantics_with(&mut r, &model);
                assert_eq!(findings.len(), 1, "mode {mode}: {findings:?}");
                assert_eq!(model.unit(findings[0].0).name, expected);
                assert!(
                    findings[0].1.message.contains("evaluates to a String"),
                    "{findings:?}"
                );
                let text = format!(
                    "package {} {{ {source} }}",
                    expected.trim_end_matches(".kerml")
                );
                assert_eq!(
                    &text[findings[0].1.span.start as usize..findings[0].1.span.end as usize],
                    format!("'{ID}'")
                );
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn duplicate_specializations_use_resolved_endpoints_across_replay() {
    let source = format!("class Good; class '{ID}'; class Child specializes Good, '{ID}';");
    for (mode, model) in models(&source).into_iter().enumerate() {
        let mut r = ResolvedModel::build(&model);
        let good = r.resolve_qualified("A::Good").unwrap();
        r.override_ids(&HashMap::from([(r.element_id(good), ID.parse().unwrap())]));
        let child = r.resolve_qualified("A::Child").unwrap();
        let edges: Vec<_> = r
            .owned_relationships(child)
            .into_iter()
            .filter(|e| r.element_type(*e) == "Subclassification")
            .collect();
        let mut hints = HashMap::from([(
            (r.element_id(edges[1]), "superclassifier".into()),
            ID.parse().unwrap(),
        )]);
        assert!(
            r.bind_id_spelled_references_with(&mut hints)
                .contains(&ID.parse().unwrap())
        );
        for _ in 0..2 {
            let findings = check::validate_semantics_with(&mut r, &model);
            assert_eq!(findings.len(), 1, "mode {mode}: {findings:?}");
            assert_eq!(model.unit(findings[0].0).name, "A.kerml");
            assert!(
                findings[0]
                    .1
                    .message
                    .starts_with("duplicate specialization"),
                "{findings:?}"
            );
        }
        if mode == 3 {
            assert_eq!(model.loaded_library_unit_count(), 0);
        }
    }
}

#[test]
fn specialization_cycles_follow_bound_endpoints() {
    for cyclic in [false, true] {
        let source = if cyclic {
            format!("class Good specializes Bridge; class Bridge specializes '{ID}'; class '{ID}';")
        } else {
            format!("class Good specializes '{ID}'; class '{ID}';")
        };
        for model in models(&source) {
            let mut r = ResolvedModel::build(&model);
            let good = r.resolve_qualified("A::Good").unwrap();
            r.override_ids(&HashMap::from([(r.element_id(good), ID.parse().unwrap())]));
            let owner = if cyclic {
                r.resolve_qualified("A::Bridge").unwrap()
            } else {
                good
            };
            let edge = r
                .owned_relationships(owner)
                .into_iter()
                .find(|e| r.element_type(*e) == "Subclassification")
                .unwrap();
            let mut hints = HashMap::from([(
                (r.element_id(edge), "superclassifier".into()),
                ID.parse().unwrap(),
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&ID.parse().unwrap())
            );
            let findings = check::validate_semantics_with(&mut r, &model);
            assert_eq!(findings.len(), if cyclic { 2 } else { 1 }, "{findings:?}");
            for (unit, d) in findings {
                assert_eq!(model.unit(unit).name, "A.kerml");
                assert!(
                    if cyclic {
                        d.message.starts_with("circular specialization")
                    } else {
                        d.message.contains("cannot specialize itself")
                    },
                    "{}",
                    d.message
                );
            }
        }
    }
}

#[test]
fn redefinition_duplicate_checks_preserve_pending_header_exclusion() {
    let mut model = Model::new();
    model.add_source("test.kerml", "class Base { feature x; } class Child specializes Base { feature x redefines x, Base::x; }");
    assert!(!model.has_errors());
    let findings = check::validate_semantics(&model);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert!(
        findings[0]
            .1
            .message
            .starts_with("duplicate specialization"),
        "{findings:?}"
    );
}

#[test]
fn metadata_typing_uses_the_stored_type_identity() {
    let source = format!("metaclass Good; class '{ID}'; metadata m : '{ID}';");
    for model in models(&source) {
        let mut r = ResolvedModel::build(&model);
        let good = r.resolve_qualified("A::Good").unwrap();
        r.override_ids(&HashMap::from([(r.element_id(good), ID.parse().unwrap())]));
        let owner = r.resolve_qualified("A::m").unwrap();
        let edge = r
            .owned_relationships(owner)
            .into_iter()
            .find(|e| r.element_type(*e) == "FeatureTyping")
            .unwrap();
        let mut hints = HashMap::from([((r.element_id(edge), "type".into()), ID.parse().unwrap())]);
        assert!(
            r.bind_id_spelled_references_with(&mut hints)
                .contains(&ID.parse().unwrap())
        );
        let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
            .into_iter()
            .filter(|(_, d)| d.message.starts_with("metadata must be typed"))
            .collect();
        assert_eq!(findings.len(), 1, "{findings:?}");
        assert_eq!(model.unit(findings[0].0).name, "B.kerml");
    }
}

#[test]
fn unresolved_redefinitions_are_not_reinterpreted_as_self_targets() {
    let mut model = Model::new();
    model.add_source("test.kerml", "class C { feature x redefines x, x; }");
    assert!(!model.has_errors());
    assert!(check::validate_semantics(&model).is_empty());
}

#[test]
fn shorthand_metadata_typings_record_identity_and_preserve_replay() {
    for spelling in [
        format!("#'{ID}' class Annotated;"),
        format!("class Annotated {{ @'{ID}'; }}"),
    ] {
        let source = format!("metaclass Good; class '{ID}'; {spelling}");
        for (mode, model) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            let good = r.resolve_qualified("A::Good").unwrap();
            r.override_ids(&HashMap::from([(r.element_id(good), ID.parse().unwrap())]));
            let annotated = r.resolve_qualified("A::Annotated").unwrap();
            let metadata = r.metadata_of(annotated);
            assert_eq!(metadata.len(), 1);
            let edge = r
                .owned_relationships(metadata[0])
                .into_iter()
                .find(|e| r.element_type(*e) == "FeatureTyping")
                .unwrap();
            let mut hints =
                HashMap::from([((r.element_id(edge), "type".into()), ID.parse().unwrap())]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&ID.parse().unwrap())
            );
            for _ in 0..2 {
                let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                    .into_iter()
                    .filter(|(_, d)| d.message.starts_with("metadata must be typed"))
                    .collect();
                assert_eq!(findings.len(), 1, "mode{mode}: {findings:?}");
                assert_eq!(model.unit(findings[0].0).name, "B.kerml");
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

// Bind only the selected expression in A; B has identical source spans and an
// ordinary declaration whose name happens to be the UUID spelling.
fn bind_expression(r: &mut ResolvedModel, owner: &str, relationship: &str) {
    let actual = r.resolve_qualified("A::Actual").unwrap();
    r.override_ids(&HashMap::from([(
        r.element_id(actual),
        ID.parse().unwrap(),
    )]));
    let owner = r.resolve_qualified(owner).unwrap();
    let expr = r.members_via(owner, relationship)[0];
    let edge = r
        .owned_relationships(expr)
        .into_iter()
        .find(|e| r.element_type(*e) == "Membership")
        .unwrap();
    let mut hints = HashMap::from([(
        (r.element_id(edge), "memberElement".into()),
        ID.parse().unwrap(),
    )]);
    assert!(
        r.bind_id_spelled_references_with(&mut hints)
            .contains(&ID.parse().unwrap())
    );
}

#[test]
fn expression_reference_kind_preserves_value_and_result_source_identity() {
    for (actual, spelled, expected) in [
        ("class Actual;", format!("feature '{ID}'=1;"), "A.kerml"),
        ("feature Actual=1;", format!("class '{ID}';"), "B.kerml"),
    ] {
        for (declaration, relation) in [
            (format!("feature checked='{ID}';"), "FeatureValue"),
            (
                format!("function checked {{ '{ID}' }}"),
                "ResultExpressionMembership",
            ),
        ] {
            let source = format!("{actual} {spelled} {declaration}");
            for (mode, model) in models(&source).into_iter().enumerate() {
                let mut r = ResolvedModel::build(&model);
                bind_expression(&mut r, "A::checked", relation);
                for _ in 0..2 {
                    let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                        .into_iter()
                        .filter(|(_, d)| {
                            d.message
                                .contains("validateFeatureReferenceExpressionReferentIsFeature")
                        })
                        .collect();
                    assert_eq!(findings.len(), 1, "mode {mode}: {findings:?}");
                    assert_eq!(model.unit(findings[0].0).name, expected);
                    let text = format!(
                        "package {} {{ {source} }}",
                        expected.trim_end_matches(".kerml")
                    );
                    assert_eq!(
                        &text[findings[0].1.span.start as usize..findings[0].1.span.end as usize],
                        format!("'{ID}'")
                    );
                }
                if mode == 3 {
                    assert_eq!(model.loaded_library_unit_count(), 0);
                }
            }
        }
    }
}

#[test]
fn invocation_arity_preserves_value_and_result_source_identity() {
    for (actual, spelled, expected) in [
        ("in a; in b; a+b", "in a; a", "A.sysml"),
        ("in a; a", "in a; in b; a+b", "B.sysml"),
    ] {
        for (declaration, relation) in [
            (format!("attribute checked='{ID}'(1);"), "FeatureValue"),
            (
                format!("calc def checked {{ '{ID}'(1) }}"),
                "ResultExpressionMembership",
            ),
        ] {
            let source = format!(
                "calc def Actual {{ {actual} }} calc def '{ID}' {{ {spelled} }} {declaration}"
            );
            for (mode, model) in models_in(&source, "sysml").into_iter().enumerate() {
                let mut r = ResolvedModel::build(&model);
                bind_expression(&mut r, "A::checked", relation);
                for _ in 0..2 {
                    let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                        .into_iter()
                        .filter(|(_, d)| d.message.contains("never bound"))
                        .collect();
                    assert_eq!(findings.len(), 1, "mode {mode}: {findings:?}");
                    assert_eq!(model.unit(findings[0].0).name, expected);
                    let text = format!(
                        "package {} {{ {source} }}",
                        expected.trim_end_matches(".sysml")
                    );
                    assert_eq!(
                        &text[findings[0].1.span.start as usize..findings[0].1.span.end as usize],
                        format!("'{ID}'(1)")
                    );
                }
                if mode == 3 {
                    assert_eq!(model.loaded_library_unit_count(), 0);
                }
            }
        }
    }
}

#[test]
fn invocation_callee_kind_uses_bound_identity() {
    for (actual, spelled, expected) in [
        (
            "class Actual;",
            format!("function '{ID}' {{ 1 }}"),
            "A.kerml",
        ),
        ("function Actual { 1 }", format!("class '{ID}';"), "B.kerml"),
    ] {
        let source = format!("{actual} {spelled} feature checked='{ID}'();");
        for (mode, model) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            bind_expression(&mut r, "A::checked", "FeatureValue");
            let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                .into_iter()
                .filter(|(_, d)| {
                    d.message
                        .contains("validateInvocationExpressionInstantiatedType")
                })
                .collect();
            assert_eq!(findings.len(), 1, "mode {mode}: {findings:?}");
            assert_eq!(model.unit(findings[0].0).name, expected);
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn scoped_filter_type_uses_bound_source_identity() {
    for (actual, spelled, expected) in [
        ("Integer = 1", "Boolean = true", "A.kerml"),
        ("Boolean = true", "Integer = 1", "B.kerml"),
    ] {
        let source = format!(
            "feature Actual : ScalarValues::{actual}; feature '{ID}' : ScalarValues::{spelled}; filter '{ID}';"
        );
        for (mode, model) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            bind_expression(&mut r, "A", "ElementFilterMembership");
            let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                .into_iter()
                .filter(|(_, d)| {
                    d.message
                        .contains("validateElementFilterMembershipIsBoolean")
                })
                .collect();
            assert_eq!(findings.len(), 1, "mode {mode}: {findings:?}");
            assert_eq!(model.unit(findings[0].0).name, expected);
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn contract_reference_kind_preserves_source_identity() {
    for (actual, spelled, expected) in [
        (
            "attribute Actual = true;",
            format!("part def '{ID}';"),
            "B.sysml",
        ),
        (
            "part def Actual;",
            format!("attribute '{ID}' = true;"),
            "A.sysml",
        ),
    ] {
        let source =
            format!("{actual} {spelled} part target; action def Work {{ send '{ID}' to target; }}");
        for (mode, model) in models_in(&source, "sysml").into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            let actual = r.resolve_qualified("A::Actual").unwrap();
            let spelled = r.resolve_qualified(&format!("A::'{ID}'")).unwrap();
            r.override_ids(&HashMap::from([(
                r.element_id(actual),
                ID.parse().unwrap(),
            )]));
            let sites = r.references_to(spelled);
            assert_eq!(sites.len(), 1);
            let mut hints = HashMap::from([(
                (r.element_id(sites[0].owner), "memberElement".into()),
                ID.parse().unwrap(),
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&ID.parse().unwrap())
            );
            for _ in 0..2 {
                let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                    .into_iter()
                    .filter(|(_, d)| {
                        d.message
                            .contains("validateFeatureReferenceExpressionReferentIsFeature")
                    })
                    .collect();
                assert_eq!(findings.len(), 1, "mode {mode}: {findings:?}");
                assert_eq!(model.unit(findings[0].0).name, expected);
                let text = format!(
                    "package {} {{ {source} }}",
                    expected.trim_end_matches(".sysml")
                );
                assert_eq!(
                    &text[findings[0].1.span.start as usize..findings[0].1.span.end as usize],
                    format!("'{ID}'")
                );
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn filter_evaluability_follows_dependency_source_across_units() {
    for (actual, spelled, expected) in [
        (
            "class Holder { feature Actual; }",
            format!("feature '{ID}'=true;"),
            "UA",
        ),
        (
            "feature Actual=true;",
            format!("class Holder {{ feature runtime; }} feature '{ID}'=Holder::runtime;"),
            "UB",
        ),
    ] {
        let actual_path = if actual.starts_with("class") {
            "A::Holder::Actual"
        } else {
            "A::Actual"
        };
        let reference = format!("'{ID}'");
        let source = format!("{actual} {spelled} feature bridge={reference};");
        for (mode, mut model) in models(&source).into_iter().enumerate() {
            let use_source = "package UA { filter A::bridge; } package UB { filter B::bridge; }";
            model.add_source("use.kerml", use_source);
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            let actual = r.resolve_qualified(actual_path).unwrap();
            r.override_ids(&HashMap::from([(
                r.element_id(actual),
                ID.parse().unwrap(),
            )]));
            let bridge = r.resolve_qualified("A::bridge").unwrap();
            let expr = r.members_via(bridge, "FeatureValue")[0];
            let edge = r
                .owned_relationships(expr)
                .into_iter()
                .find(|e| r.element_type(*e) == "Membership")
                .unwrap();
            let mut hints = HashMap::from([(
                (r.element_id(edge), "memberElement".into()),
                ID.parse().unwrap(),
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&ID.parse().unwrap())
            );
            for _ in 0..2 {
                let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                    .into_iter()
                    .filter(|(_, d)| {
                        d.message
                            .contains("validateElementFilterMembershipIsModelLevelEvaluable")
                    })
                    .collect();
                assert_eq!(findings.len(), 1, "mode {mode}: {findings:?}");
                assert_eq!(model.unit(findings[0].0).name, "use.kerml");
                let span = findings[0].1.span;
                assert_eq!(
                    &use_source[span.start as usize..span.end as usize],
                    if expected == "UA" {
                        "A::bridge"
                    } else {
                        "B::bridge"
                    }
                );
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

fn bind_named_site(r: &mut ResolvedModel, actual: &str, key: &str) {
    let actual = r.resolve_qualified(actual).unwrap();
    let spelled = r.resolve_qualified(&format!("A::'{ID}'")).unwrap();
    r.override_ids(&HashMap::from([(
        r.element_id(actual),
        ID.parse().unwrap(),
    )]));
    let sites = r.references_to(spelled);
    assert_eq!(sites.len(), 1, "{sites:?}");
    let mut hints = HashMap::from([(
        (r.element_id(sites[0].owner), key.into()),
        ID.parse().unwrap(),
    )]);
    assert!(
        r.bind_id_spelled_references_with(&mut hints)
            .contains(&ID.parse().unwrap())
    );
}

#[test]
fn metadata_relationship_and_chain_checks_preserve_bound_identity() {
    let cases = [
        (
            "kerml",
            format!(
                "class Holder {{ feature Actual; }} feature '{ID}'=true; metaclass M {{ feature value; }} metadata m:M {{ feature value='{ID}'; }}"
            ),
            "A::Holder::Actual",
            "memberElement",
            "metadata body value must be model-level",
        ),
        (
            "kerml",
            format!(
                "datatype T; datatype U; feature Actual:U; feature '{ID}':T; function f {{ return r:T; '{ID}' }}"
            ),
            "A::Actual",
            "memberElement",
            "validateBindingConnectorTypeConformance",
        ),
        (
            "kerml",
            format!(
                "class Holder {{ feature Actual; }} feature '{ID}'; class C {{ feature checked='{ID}'; }}"
            ),
            "A::Holder::Actual",
            "memberElement",
            "validateConnectorTypeFeaturing",
        ),
        (
            "kerml",
            format!(
                "class Holder {{ feature Actual {{ feature leaf; }} }} feature '{ID}' {{ feature leaf; }} class C {{ feature checked subsets '{ID}'.leaf; }}"
            ),
            "A::Holder::Actual",
            "chainingFeature",
            "subsetted feature chain is featured",
        ),
        (
            "sysml",
            format!(
                "part def T; part def U; part Actual:U; part '{ID}':T; requirement def R {{ subject s:T; }} requirement req:R; satisfy req by '{ID}';"
            ),
            "A::Actual",
            "memberElement",
            "validateBindingConnectorTypeConformance",
        ),
    ];
    for (dialect, source, actual, key, rule) in cases {
        for (mode, model) in models_in(&source, dialect).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            bind_named_site(&mut r, actual, key);
            for _ in 0..2 {
                let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                    .into_iter()
                    .filter(|(_, d)| d.message.contains(rule))
                    .collect();
                assert_eq!(findings.len(), 1, "{rule}, mode {mode}: {findings:?}");
                assert_eq!(model.unit(findings[0].0).name, format!("A.{dialect}"));
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

const QUANTITY_LIBRARY: &str = "package Quantities { datatype QuantityValue; datatype QuantityPowerFactor; } package Q { feature L; feature T; datatype LengthUnit { feature pf : Quantities::QuantityPowerFactor { feature quantity = Q::L; feature exponent = 1; } } datatype TimeUnit { feature pf : Quantities::QuantityPowerFactor { feature quantity = Q::T; feature exponent = 1; } } datatype Length { feature mRef : LengthUnit; } datatype Time { feature mRef : TimeUnit; } } package ISQ { datatype DurationValue :> Q::Time; }";

#[test]
fn dimension_checks_preserve_root_and_cross_unit_dependency_identity() {
    for (actual, spelled, expected) in [("Time", "Length", "A"), ("Length", "Time", "B")] {
        for expression in [format!("'{ID}' + length"), "bridge + length".into()] {
            let recursive = expression.starts_with("bridge");
            let bridge = if recursive {
                format!("feature bridge = '{ID}';")
            } else {
                String::new()
            };
            for result in [false, true] {
                let root = if result {
                    format!("function checked {{ {expression} }}")
                } else {
                    format!("feature checked = {expression};")
                };
                let source = format!(
                    "feature Actual : Q::{actual}; feature '{ID}' : Q::{spelled}; feature length : Q::Length; {bridge} {root}"
                );
                for (mode, mut model) in models_with_library(&source, "kerml", QUANTITY_LIBRARY)
                    .into_iter()
                    .enumerate()
                {
                    if recursive {
                        model.add_source("use.kerml", "package UA { feature checked=A::bridge + A::length; } package UB { feature checked=B::bridge + B::length; }");
                    }
                    let mut r = ResolvedModel::build(&model);
                    bind_named_site(&mut r, "A::Actual", "memberElement");
                    for _ in 0..2 {
                        let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                            .into_iter()
                            .filter(|(_, d)| d.message.contains("incompatible quantity dimensions"))
                            .collect();
                        assert_eq!(
                            findings.len(),
                            if recursive { 2 } else { 1 },
                            "mode {mode}: {findings:?}"
                        );
                        assert!(
                            findings
                                .iter()
                                .any(|(u, _)| model.unit(*u).name == format!("{expected}.kerml"))
                        );
                        for (unit, d) in findings {
                            if model.unit(unit).name == "use.kerml" {
                                let text = "package UA { feature checked=A::bridge + A::length; } package UB { feature checked=B::bridge + B::length; }";
                                assert_eq!(
                                    &text[d.span.start as usize..d.span.end as usize],
                                    format!("{expected}::bridge + {expected}::length")
                                );
                            }
                        }
                    }
                    if mode == 3 {
                        assert_eq!(model.loaded_library_unit_count(), 0);
                    }
                }
            }
        }
    }
}

#[test]
fn action_contract_checks_preserve_bound_identity() {
    let cases = [
        (
            format!(
                "part def Actual; attribute '{ID}'[1]; action def Work {{ assign '{ID}' := 1; }}"
            ),
            "validateAssignmentActionUsageReferent",
        ),
        (
            format!("port Actual; part '{ID}'; action def Work {{ send 1 to '{ID}'; }}"),
            "validateSendActionUsageReceiver",
        ),
        (
            format!(
                "attribute Actual : ScalarValues::Integer; attribute '{ID}' : ScalarValues::Boolean; action def Work {{ accept when '{ID}'; }}"
            ),
            "validateTriggerInvocationActionWhenArgument",
        ),
        (
            format!(
                "attribute Actual : ScalarValues::Integer; attribute '{ID}' : ScalarValues::Boolean; state def Work {{ state a; state b; transition first a if '{ID}' then b; }}"
            ),
            "validateTransitionFeatureMembershipGuardExpression",
        ),
    ];
    for (source, rule) in cases {
        for (mode, model) in models_in(&source, "sysml").into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            bind_named_site(&mut r, "A::Actual", "memberElement");
            for _ in 0..2 {
                let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                    .into_iter()
                    .filter(|(_, d)| d.code == Some(rule))
                    .collect();
                assert_eq!(findings.len(), 1, "{rule}, mode {mode}: {findings:?}");
                assert_eq!(model.unit(findings[0].0).name, "A.sysml");
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn quantity_factor_queries_preserve_quantity_and_exponent_identity() {
    for exponent in [false, true] {
        let source = if exponent {
            format!(
                "feature Actual=2; feature '{ID}'=1; feature L; datatype Unit {{ feature pf:Quantities::QuantityPowerFactor {{ feature quantity=L; feature exponent='{ID}'; }} }} datatype Amount {{ feature mRef:Unit; }}"
            )
        } else {
            format!(
                "feature Actual; feature '{ID}'; datatype Unit {{ feature pf:Quantities::QuantityPowerFactor {{ feature quantity='{ID}'; feature exponent=1; }} }} datatype Amount {{ feature mRef:Unit; }}"
            )
        };
        for (mode, model) in models_with_library(&source, "kerml", QUANTITY_LIBRARY)
            .into_iter()
            .enumerate()
        {
            let mut r = ResolvedModel::build(&model);
            bind_named_site(&mut r, "A::Actual", "memberElement");
            for _ in 0..2 {
                for package in ["B", "A"] {
                    let amount = r.resolve_qualified(&format!("{package}::Amount")).unwrap();
                    let dims = r.quantity_dims_of_type(amount).unwrap();
                    assert_eq!(
                        dims.render(&r),
                        if exponent {
                            if package == "A" { "L^2" } else { "L" }
                        } else if package == "A" {
                            "Actual"
                        } else {
                            ID
                        },
                        "mode {mode}"
                    );
                }
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn after_trigger_dimension_inference_preserves_source_identity() {
    for (actual, spelled, expected) in
        [("Length", "Time", "A.sysml"), ("Time", "Length", "B.sysml")]
    {
        let source = format!(
            "attribute Actual:Q::{actual}; attribute '{ID}':Q::{spelled}; action def Work {{ accept after ('{ID}' * 1); }}"
        );
        for (mode, model) in models_with_library(&source, "sysml", QUANTITY_LIBRARY)
            .into_iter()
            .enumerate()
        {
            let mut r = ResolvedModel::build(&model);
            bind_named_site(&mut r, "A::Actual", "memberElement");
            for _ in 0..2 {
                let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                    .into_iter()
                    .filter(|(_, d)| d.code == Some("validateTriggerInvocationActionAfterArgument"))
                    .collect();
                assert_eq!(findings.len(), 1, "mode {mode}: {findings:?}");
                assert_eq!(model.unit(findings[0].0).name, expected);
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn declared_multiplicity_query_preserves_bound_identity() {
    for (actual, expected) in [("2", Some((2.0, 2.0))), ("true", None), ("missing", None)] {
        let source = format!("feature Actual={actual}; feature '{ID}'=1; feature sized['{ID}'];");
        for (mode, model) in models(&source).into_iter().enumerate() {
            let mut r = ResolvedModel::build(&model);
            bind_named_site(&mut r, "A::Actual", "memberElement");
            for _ in 0..2 {
                let a = r.resolve_qualified("A::sized").unwrap();
                let b = r.resolve_qualified("B::sized").unwrap();
                assert_eq!(r.declared_multiplicity(a), expected, "mode {mode}");
                assert_eq!(r.declared_multiplicity(b), Some((1.0, 1.0)), "mode {mode}");
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}
