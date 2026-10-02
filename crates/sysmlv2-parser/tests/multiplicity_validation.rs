//! Authored header, body and named ranges share exact validation semantics.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    check, json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};

fn models(library: &str, users: &[(&str, &str)]) -> Vec<Model> {
    let mut base = Model::new();
    base.add_library_source("library.kerml", library);
    assert!(!base.has_errors());
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(41).unwrap(), 41).unwrap());
    (0..4)
        .map(|mode| {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("library.kerml", library);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            for &(name, source) in users {
                let unit = m.add_source(name, source);
                assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            }
            m
        })
        .collect()
}

fn messages(source: &str) -> Vec<String> {
    let mut m = Model::new();
    m.add_source("test.kerml", source);
    assert!(!m.has_errors(), "{source}");
    check::validate_semantics(&m)
        .into_iter()
        .map(|(_, d)| d.message)
        .collect()
}

#[test]
fn authored_ranges_share_numeric_validation_without_duplicate_diagnostics() {
    for (range, error) in [
        ("3..2", "lower bound 3 exceeds upper bound 2"),
        (
            "9007199254740993..9007199254740992",
            "lower bound 9007199254740993 exceeds upper bound 9007199254740992",
        ),
        (
            "170141183460469231731687303715884105729..170141183460469231731687303715884105728",
            "lower bound 170141183460469231731687303715884105729 exceeds upper bound 170141183460469231731687303715884105728",
        ),
        ("1.5", "Natural number"),
        ("true", "Natural number"),
        ("\"two\"", "Natural number"),
        ("*..*", "Natural number"),
        ("negative", "upper bound is negative"),
    ] {
        for declaration in [
            format!("feature p[{range}];"),
            format!("feature p {{ multiplicity [{range}]; }}"),
            format!(
                "multiplicity named[{range}]; feature p {{ multiplicity subsets named; }} feature q {{ multiplicity subsets named; }}"
            ),
        ] {
            let findings = messages(&format!("feature negative = -1; {declaration}"));
            assert_eq!(findings.len(), 1, "{declaration}: {findings:?}");
            assert!(findings[0].contains(error), "{declaration}: {findings:?}");
        }
    }
    for range in [
        "0..*",
        "4",
        "unknown",
        "absent",
        "170141183460469231731687303715884105728",
    ] {
        let findings = messages(&format!(
            "feature unknown; multiplicity named[{range}]; feature p {{ multiplicity [{range}]; }}"
        ));
        assert!(findings.is_empty(), "{range}: {findings:?}");
    }
    assert!(messages("multiplicity a subsets b; multiplicity b subsets a; feature p { multiplicity subsets a; }").is_empty());
}

#[test]
fn range_diagnostics_keep_lexical_scope_and_source_locations_across_replay() {
    let library = "package L { feature n = 2; multiplicity good[4]; multiplicity invalid[8..3]; }";
    let a = "package A { feature n = 5; multiplicity wrong[n..L::n]; feature p { multiplicity subsets wrong; } }";
    let b = "package B { feature n = 1; feature bad { multiplicity [4..n]; } }";
    let mut expected = None;
    for model in models(library, &[("a.kerml", a), ("b.kerml", b)]) {
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            let findings: Vec<_> = check::validate_semantics_with(&mut r, &model)
                .into_iter()
                .map(|(unit, d)| {
                    assert!(!model.is_library_unit(unit));
                    (
                        model.unit(unit).name.clone(),
                        d.span.start,
                        d.span.end,
                        d.message,
                    )
                })
                .collect();
            assert_eq!(findings.len(), 2, "{findings:?}");
            assert_eq!(
                &a[findings[0].1 as usize..findings[0].2 as usize],
                "[n..L::n]"
            );
            assert_eq!(&b[findings[1].1 as usize..findings[1].2 as usize], "[4..n]");
            assert!(findings[0].3.contains("5 exceeds upper bound 2"));
            assert!(findings[1].3.contains("4 exceeds upper bound 1"));
            if let Some(expected) = &expected {
                assert_eq!(&findings, expected);
            } else {
                expected = Some(findings);
            }
        }
    }
}

#[test]
fn validation_rows_do_not_turn_named_domains_into_feature_cardinalities() {
    for (mode, model) in models(
        "package L { multiplicity four[4]; alias named for four; }",
        &[(
            "user.kerml",
            "feature p { multiplicity subsets L::named; } multiplicity local[7]; feature q { multiplicity subsets local; } feature header[3];",
        )],
    ).into_iter().enumerate() {
        if mode == 3 { assert_eq!(model.loaded_library_unit_count(), 0); }
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            assert!(check::validate_semantics_with(&mut r, &model).is_empty());
            for name in ["L::four", "local"] {
                let e = r.resolve_qualified(name).unwrap();
                assert_eq!(r.declared_multiplicity(e), None, "{name}");
                assert_eq!(r.effective_cardinality(e), Some((0, None)), "{name}");
            }
            for (name, n) in [("p", 4), ("q", 7), ("header", 3)] {
                let e = r.resolve_qualified(name).unwrap();
                assert_eq!(r.effective_cardinality(e), Some((n, Some(n))), "{name}");
                assert_eq!(
                    r.declared_multiplicity(e),
                    (name == "header").then_some((3.0, 3.0))
                );
            }
        }
        if mode == 3 { assert_eq!(model.loaded_library_unit_count(), 0); }
    }
}

#[test]
fn body_and_named_bounds_reach_the_existing_result_type_check() {
    for declaration in [
        "feature p[bound];",
        "feature p { multiplicity [bound]; }",
        "multiplicity named[bound];",
    ] {
        let findings = messages(&format!("class C; feature bound : C; {declaration}"));
        assert_eq!(findings.len(), 1, "{declaration}: {findings:?}");
        assert!(
            findings[0].contains("validateMultiplicityRangeResultTypes"),
            "{findings:?}"
        );
    }
}

#[test]
fn body_bounds_resolve_inside_the_constrained_feature() {
    let findings = messages("feature n = 9; feature p { feature n = 2; multiplicity [4..n]; }");
    assert_eq!(
        findings,
        ["multiplicity lower bound 4 exceeds upper bound 2"]
    );
}

#[test]
fn bound_validation_uses_the_reference_source_unit_identity() {
    use std::collections::HashMap;
    let id = "99999999-9999-4999-8999-999999999999";
    for (actual, spelled, expected_unit) in [(2, 9, "A.kerml"), (9, 2, "B.kerml")] {
        let mut model = Model::new();
        for package in ["A", "B"] {
            model.add_source(
                format!("{package}.kerml"),
                &format!(
                    "package {package} {{ feature n = {actual}; feature '{id}' = {spelled};
                feature header[5..'{id}']; feature body {{ multiplicity [5..'{id}']; }}
                multiplicity named[5..'{id}'];
                class Base {{ feature x[0..'{id}']; }}
                class Child specializes Base {{ feature y[0..5] subsets x; }}
            }}"
                ),
            );
        }
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let n = r.resolve_qualified("A::n").unwrap();
        r.override_ids(&HashMap::from([(r.element_id(n), id.parse().unwrap())]));
        let mut hints = HashMap::new();
        for name in ["A::header", "A::body", "A::named", "A::Base::x"] {
            let element = r.resolve_qualified(name).unwrap();
            let range = if name == "A::named" {
                element
            } else {
                r.owned_members(element)[0]
            };
            let upper = r.owned_members(range)[1];
            let membership = r.owned_relationships(upper)[0];
            hints.insert(
                (r.element_id(membership), "memberElement".into()),
                id.parse().unwrap(),
            );
        }
        assert!(
            r.bind_id_spelled_references_with(&mut hints)
                .contains(&id.parse().unwrap())
        );
        for _ in 0..2 {
            let findings = check::validate_semantics_with(&mut r, &model);
            assert_eq!(findings.len(), 4, "{findings:?}");
            assert!(
                findings
                    .iter()
                    .all(|(unit, _)| model.unit(*unit).name == expected_unit)
            );
            assert_eq!(
            findings
                .iter()
                .filter(|(_, d)| d.message == "multiplicity lower bound 5 exceeds upper bound 2")
                .count(),
            3
        );
            assert!(findings.iter().any(|(_,d)| d.message == "subsetting multiplicity upper bound 5 exceeds the subsetted feature's upper bound 2"));
        }
    }
}

#[test]
fn bound_result_type_validation_preserves_reference_identity() {
    use std::collections::HashMap;
    let id = "aaaaaaaa-aaaa-4aaa-8aaa-aaaaaaaaaaaa";
    let mut model = Model::new();
    for package in ["A", "B"] {
        model.add_source(
            format!("{package}.kerml"),
            &format!(
                "package {package} {{ class C; feature bound : C; feature '{id}' = 2;
                feature header['{id}']; feature body {{ multiplicity ['{id}']; }}
                multiplicity named['{id}']; }}"
            ),
        );
    }
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let bound = r.resolve_qualified("A::bound").unwrap();
    r.override_ids(&HashMap::from([(r.element_id(bound), id.parse().unwrap())]));
    let mut hints = HashMap::new();
    for name in ["A::header", "A::body", "A::named"] {
        let e = r.resolve_qualified(name).unwrap();
        let range = if name == "A::named" {
            e
        } else {
            r.owned_members(e)[0]
        };
        let expression = r.owned_members(range)[0];
        let membership = r.owned_relationships(expression)[0];
        hints.insert(
            (r.element_id(membership), "memberElement".into()),
            id.parse().unwrap(),
        );
    }
    assert!(
        r.bind_id_spelled_references_with(&mut hints)
            .contains(&id.parse().unwrap())
    );
    for _ in 0..2 {
        let findings = check::validate_semantics_with(&mut r, &model);
        assert_eq!(findings.len(), 3, "{findings:?}");
        assert!(
            findings
                .iter()
                .all(|(unit, d)| model.unit(*unit).name == "A.kerml"
                    && d.message.contains("validateMultiplicityRangeResultTypes"))
        );
    }
}

#[test]
fn specialization_bound_reads_use_each_declarations_origin() {
    use std::collections::HashMap;
    let id = "cccccccc-cccc-4ccc-8ccc-cccccccccccc";
    for form in 0..3 {
        let mut model = Model::new();
        model.add_source(
            "a.kerml",
            &format!(
                "package A {{ feature n = 2; feature '{id}' = 9; class Base {{ {} }} }}",
                constrained("x", "", &format!("0..'{id}'"), form)
            ),
        );
        model.add_source(
            "b.kerml",
            &format!(
                "package B {{ feature '{id}' = 5; class Child specializes A::Base {{ {} }} }}",
                constrained("y", "subsets x", &format!("0..'{id}'"), form)
            ),
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let n = r.resolve_qualified("A::n").unwrap();
        r.override_ids(&HashMap::from([(r.element_id(n), id.parse().unwrap())]));
        let x = r.resolve_qualified("A::Base::x").unwrap();
        let range = if form == 2 {
            r.resolve_qualified("A::Base::xDomain").unwrap()
        } else {
            r.owned_members(x)[0]
        };
        let expression = r.owned_members(range)[1];
        let membership = r.owned_relationships(expression)[0];
        let mut hints = HashMap::from([(
            (r.element_id(membership), "memberElement".into()),
            id.parse().unwrap(),
        )]);
        assert!(
            r.bind_id_spelled_references_with(&mut hints)
                .contains(&id.parse().unwrap())
        );
        for _ in 0..2 {
            let findings = check::validate_semantics_with(&mut r, &model);
            assert_eq!(findings.len(), 1, "{findings:?}");
            assert_eq!(model.unit(findings[0].0).name, "b.kerml");
            assert_eq!(
                findings[0].1.message,
                "subsetting multiplicity upper bound 5 exceeds the subsetted feature's upper bound 2"
            );
        }
    }
}

#[test]
fn bound_result_types_follow_cross_unit_value_dependency_identity() {
    use std::collections::HashMap;
    let id = "dddddddd-dddd-4ddd-8ddd-dddddddddddd";
    let mut model = Model::new();
    model.add_source("a.kerml", &format!("package A {{ class C; feature bound : C; feature '{id}' = 2; feature carrier = '{id}'; }}"));
    model.add_source("b.kerml", "package B { feature header[A::carrier]; feature body { multiplicity [A::carrier]; } multiplicity named[A::carrier]; }");
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let bound = r.resolve_qualified("A::bound").unwrap();
    r.override_ids(&HashMap::from([(r.element_id(bound), id.parse().unwrap())]));
    let carrier = r.resolve_qualified("A::carrier").unwrap();
    let expression = r.members_via(carrier, "FeatureValue")[0];
    let membership = r.owned_relationships(expression)[0];
    let mut hints = HashMap::from([(
        (r.element_id(membership), "memberElement".into()),
        id.parse().unwrap(),
    )]);
    assert!(
        r.bind_id_spelled_references_with(&mut hints)
            .contains(&id.parse().unwrap())
    );
    for _ in 0..2 {
        let findings = check::validate_semantics_with(&mut r, &model);
        assert_eq!(findings.len(), 3, "{findings:?}");
        assert!(
            findings
                .iter()
                .all(|(unit, d)| model.unit(*unit).name == "b.kerml"
                    && d.message.contains("validateMultiplicityRangeResultTypes"))
        );
    }
}

fn containment(source: &str) -> Vec<String> {
    messages(source)
        .into_iter()
        .filter(|m| {
            m.starts_with("redefining multiplicity") || m.starts_with("subsetting multiplicity")
        })
        .collect()
}

fn constrained(name: &str, specialization: &str, range: &str, form: usize) -> String {
    match form {
        0 => format!("feature {name}[{range}] {specialization};"),
        1 => format!("feature {name} {specialization} {{ multiplicity [{range}]; }}"),
        _ => format!(
            "multiplicity {name}Domain[{range}]; feature {name} {specialization} {{ multiplicity subsets {name}Domain; }}"
        ),
    }
}

#[test]
fn containment_covers_every_header_body_named_pair() {
    for base in 0..3 {
        for child in 0..3 {
            for (kind, range, count) in [
                ("redefines", "1..4", 1),
                ("redefines", "3..6", 1),
                ("redefines", "3..4", 0),
                ("subsets", "0..4", 0),
                ("subsets", "0..6", 1),
            ] {
                let source = format!(
                    "class Base {{ {} }} class Child specializes Base {{ {} }}",
                    constrained("x", "", "2..5", base),
                    constrained("y", &format!("{kind} x"), range, child)
                );
                assert_eq!(
                    containment(&source).len(),
                    count,
                    "{source}: {:?}",
                    messages(&source)
                );
            }
        }
    }
}

#[test]
fn containment_evaluates_both_domains_in_the_specializing_receiver() {
    for base in 0..3 {
        for child in 0..3 {
            for (original, actual, count) in [(3, 6, 0), (6, 3, 1)] {
                let source = format!(
                    "class Base {{ feature n default = {original}; {} }} class Child specializes Base {{ feature n redefines Base::n = {actual}; {} }}",
                    constrained("x", "", "0..n", base),
                    constrained("y", "redefines x", "0..6", child)
                );
                assert_eq!(
                    containment(&source).len(),
                    count,
                    "{source}: {:?}",
                    messages(&source)
                );
            }
        }
    }
}

#[test]
fn named_domain_chains_preserve_exact_endpoints() {
    for upper in [
        "9007199254740993".to_string(),
        "170141183460469231731687303715884105729".to_string(),
        format!("1{}1", "0".repeat(399)),
    ] {
        let lower = format!("{}0", &upper[..upper.len() - 1]);
        let source = format!(
            "multiplicity limit[0..{lower}]; multiplicity linked subsets limit; alias named for linked; feature x {{ multiplicity subsets named; }} feature y subsets x {{ multiplicity [0..{upper}]; }}"
        );
        let found = containment(&source);
        assert_eq!(found.len(), 1, "{source}: {:?}", messages(&source));
        assert!(
            found[0].contains(&upper) && found[0].contains(&lower),
            "{found:?}"
        );
    }
}

#[test]
fn incomplete_or_invalid_domains_do_not_fabricate_containment() {
    for domain in [
        "multiplicity subsets missing;",
        "multiplicity subsets cycle;",
        "multiplicity subsets wrong;",
        "multiplicity [3..2];",
        "multiplicity [0..unknown];",
        "multiplicity [0..1]; multiplicity [0..2];",
    ] {
        for side in [false, true] {
            let (x, y) = if side {
                (domain, "multiplicity [0..9];")
            } else {
                ("multiplicity [0..1];", domain)
            };
            let source = format!(
                "multiplicity cycle subsets cycle; feature wrong; feature unknown; feature x {{ {x} }} feature y subsets x {{ {y} }}"
            );
            assert!(
                containment(&source).is_empty(),
                "{source}: {:?}",
                messages(&source)
            );
        }
    }
    assert!(
        containment("feature x[0..1] { multiplicity [0..2]; } feature y[0..9] subsets x;")
            .is_empty()
    );
    assert!(containment("feature x; feature y[0..9] subsets x;").is_empty());
}

#[test]
fn named_containment_replays_without_hydration_and_keeps_user_spans() {
    let source = "feature y subsets L::x { multiplicity subsets L::wide; }";
    for (mode, model) in models("package L { multiplicity narrow[0..2]; multiplicity wide[0..4]; feature x { multiplicity subsets narrow; } }", &[("user.kerml", source)]).into_iter().enumerate() {
        let mut r = ResolvedModel::build(&model);
        for _ in 0..2 {
            let findings = check::validate_semantics_with(&mut r, &model);
            assert_eq!(findings.len(), 1, "{mode}: {findings:?}");
            let (unit, d) = &findings[0];
            assert_eq!(model.unit(*unit).name, "user.kerml");
            assert_eq!(&source[d.span.start as usize..d.span.end as usize], "L::x");
            assert!(d.message.starts_with("subsetting multiplicity"), "{}", d.message);
        }
        if mode == 3 { assert_eq!(model.loaded_library_unit_count(), 0); }
    }
}

#[test]
fn containment_tracks_root_and_package_formula_dependencies_in_the_receiver() {
    for (original, actual, expected) in [(3, 6, 0), (6, 3, 1)] {
        for package in [false, true] {
            let source = format!(
                "feature bound = Base::n; class Base {{ feature n default = {original}; feature x {{ multiplicity [0..bound]; }} }} class Child specializes Base {{ feature n redefines Base::n = {actual}; feature y[0..6] redefines x; feature z redefines x; }}"
            );
            let source = if package {
                format!("package P {{ {source} }}")
            } else {
                source
            };
            assert_eq!(
                containment(&source).len(),
                expected,
                "{source}: {:?}",
                messages(&source)
            );
            let mut model = Model::new();
            model.add_source("test.kerml", &source);
            let mut r = ResolvedModel::build(&model);
            let y = r
                .resolve_qualified(if package { "P::Child::y" } else { "Child::y" })
                .unwrap();
            assert_eq!(r.effective_cardinality(y), Some((0, Some(6))));
            let z = r
                .resolve_qualified(if package { "P::Child::z" } else { "Child::z" })
                .unwrap();
            assert_eq!(r.effective_cardinality(z), Some((0, Some(actual))));
        }
    }
    // The containing receiver cannot select a value nested in the constrained
    // feature; do not silently replace that unknown with a lexical value.
    assert!(containment("feature x { feature n = 2; multiplicity [0..n]; } feature y subsets x { multiplicity [0..9]; }").is_empty());
}

#[test]
fn root_bound_values_keep_identity_and_effective_cardinality() {
    for (value, expected) in [
        ("2", Some(2)),
        ("other", Some(2)),
        ("other + 1", Some(3)),
        ("missing", None),
    ] {
        let source = format!(
            "feature missing; feature other = 2; feature n = {value}; class Base {{ feature x[0..n]; }} class Child specializes Base {{ feature n = 99; feature y[0..4] subsets x; }} feature root[0..n];"
        );
        assert_eq!(
            containment(&source).len(),
            usize::from(expected.is_some()),
            "{source}"
        );
        let mut model = Model::new();
        model.add_source("test.kerml", &source);
        let mut r = ResolvedModel::build(&model);
        let root = r.resolve_qualified("root").unwrap();
        assert_eq!(
            r.effective_cardinality(root),
            expected.map(|n| (0, Some(n)))
        );
    }
}

fn contextual(source: &str) -> Vec<String> {
    messages(source)
        .into_iter()
        .filter(|m| m.contains("invalid in this specializing context"))
        .collect()
}

#[test]
fn specialization_reports_ranges_made_invalid_by_receiver_values() {
    for form in 0..3 {
        for kind in ["subsets", "redefines"] {
            for own in ["", "[0..4]"] {
                for (range, original, actual, reason) in [
                    ("0..n", "3", "-1", "upper bound -1"),
                    ("0..n", "3", "2.5", "upper bound 2.5"),
                    ("0..n", "3", "true", "upper bound must be a Natural"),
                    ("0..n", "3", "\"bad\"", "upper bound must be a Natural"),
                    ("n..5", "3", "-1", "lower bound -1"),
                    ("n..5", "3", "*", "lower bound inf"),
                    ("2..n", "3", "1", "lower bound 2 exceeds upper bound 1"),
                    ("n", "3", "-1", "upper bound -1"),
                    (
                        "9007199254740993..n",
                        "9007199254740994",
                        "9007199254740992",
                        "lower bound 9007199254740993 exceeds upper bound 9007199254740992",
                    ),
                ] {
                    let source = format!(
                        "class Base {{ feature n default = {original}; {} }} class Child specializes Base {{ feature n redefines Base::n = {actual}; feature y{own} {kind} x; }}",
                        constrained("x", "", range, form)
                    );
                    let errors = contextual(&source);
                    assert_eq!(errors.len(), 1, "{source}: {:?}", messages(&source));
                    assert!(errors[0].contains(reason), "{errors:?}");
                    assert!(containment(&source).is_empty(), "{source}");
                }
            }
        }
    }
}

#[test]
fn contextual_validity_checks_own_named_domains_and_deduplicates_shared_ranges() {
    for (base, shared) in [
        ("feature x;", false),
        ("feature x[0..*];", false),
        ("feature x { multiplicity subsets interval; }", true),
    ] {
        let source = format!(
            "class Base {{ feature n default = 3; multiplicity interval[0..n]; {base} }} class Child specializes Base {{ feature n redefines Base::n = -1; feature y redefines x {{ multiplicity subsets Base::interval; }} }}"
        );
        let errors = contextual(&source);
        assert_eq!(errors.len(), 1, "{source}: {:?}", messages(&source));
        assert!(
            errors[0].starts_with(if shared {
                "multiplicity constraint from"
            } else {
                "specializing multiplicity"
            }),
            "{errors:?}"
        );
    }
}

#[test]
fn contextual_validity_does_not_duplicate_authored_errors_or_guess_unknowns() {
    for (original, actual) in [
        ("-1", "-2"),
        ("missing", "-1"),
        ("3", "missing"),
        ("3", "3"),
        ("3", "*"),
    ] {
        for form in 0..3 {
            let source = format!(
                "feature missing; class Base {{ feature n default = {original}; {} }} class Child specializes Base {{ feature n redefines Base::n = {actual}; feature y redefines x; }}",
                constrained("x", "", "0..n", form)
            );
            assert!(
                contextual(&source).is_empty(),
                "{source}: {:?}",
                messages(&source)
            );
        }
    }
    let incomplete = "class Base { feature n default = 3; feature x[0..n]; } class Child specializes Base, Missing { feature n redefines Base::n = -1; feature y redefines x; }";
    assert!(contextual(incomplete).is_empty());
    let partial = "class Base { feature n default = 3; feature lo default = 0; feature x[lo..n]; } class Child specializes Base { feature missing; feature lo redefines Base::lo = missing; feature n redefines Base::n = -1; feature y redefines x; }";
    assert!(contextual(partial).is_empty());
}

#[test]
fn contextual_validity_preserves_replay_and_specialization_source_spans() {
    let source = "class Child specializes L::Base { feature n redefines L::Base::n = -1; feature y redefines x; }";
    for form in 0..3 {
        let library = format!(
            "package L {{ class Base {{ feature n default = 3; {} }} }}",
            constrained("x", "", "0..n", form)
        );
        for (mode, model) in models(&library, &[("child.kerml", source)])
            .into_iter()
            .enumerate()
        {
            let mut r = ResolvedModel::build(&model);
            for _ in 0..2 {
                let findings = check::validate_semantics_with(&mut r, &model);
                assert_eq!(findings.len(), 1, "{mode}: {findings:?}");
                let (unit, d) = &findings[0];
                assert_eq!(model.unit(*unit).name, "child.kerml");
                assert_eq!(&source[d.span.start as usize..d.span.end as usize], "x");
                assert!(
                    d.message.contains("invalid in this specializing context"),
                    "{}",
                    d.message
                );
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn contextual_validity_uses_bound_reference_identity_across_units() {
    use std::collections::HashMap;
    let id = "eeeeeeee-eeee-4eee-8eee-eeeeeeeeeeee";
    for form in 0..3 {
        let mut model = Model::new();
        model.add_source(
            "base.kerml",
            &format!(
                "package A {{ class Base {{ feature n default = 3; feature '{id}' = 9; {} }} }}",
                constrained("x", "", &format!("0..'{id}'"), form)
            ),
        );
        model.add_source("child.kerml", &format!("package B {{ feature '{id}' = 8; class Child specializes A::Base {{ feature n redefines A::Base::n = -1; feature y redefines x; }} }}"));
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let n = r.resolve_qualified("A::Base::n").unwrap();
        r.override_ids(&HashMap::from([(r.element_id(n), id.parse().unwrap())]));
        let range = if form == 2 {
            r.resolve_qualified("A::Base::xDomain").unwrap()
        } else {
            let x = r.resolve_qualified("A::Base::x").unwrap();
            r.owned_members(x)[0]
        };
        let upper = r.owned_members(range)[1];
        let membership = r.owned_relationships(upper)[0];
        let mut hints = HashMap::from([(
            (r.element_id(membership), "memberElement".into()),
            id.parse().unwrap(),
        )]);
        assert!(
            r.bind_id_spelled_references_with(&mut hints)
                .contains(&id.parse().unwrap())
        );
        for _ in 0..2 {
            let findings = check::validate_semantics_with(&mut r, &model);
            assert_eq!(findings.len(), 1, "{findings:?}");
            assert_eq!(model.unit(findings[0].0).name, "child.kerml");
            assert!(
                findings[0].1.message.contains("upper bound -1"),
                "{findings:?}"
            );
        }
    }
}

#[test]
fn nested_bound_members_do_not_invent_a_different_evaluation_receiver() {
    for kind in ["subsets", "redefines"] {
        for bound in ["inner", "Base::x::inner", "total"] {
            let source = format!(
                "class Base {{ feature outer default = 2; feature x {{ feature inner default = 3; feature total = inner + outer; multiplicity [0..{bound}]; }} }} class Child specializes Base {{ feature outer redefines Base::outer = 9; feature y {kind} x {{ feature renamed redefines Base::x::inner = 5; }} feature z[0..8] subsets y; }}"
            );
            let mut model = Model::new();
            model.add_source("test.kerml", &source);
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            for name in ["Base::x", "Child::y"] {
                let e = r.resolve_qualified(name).unwrap();
                assert_eq!(r.effective_cardinality(e), None, "{source}: {name}");
            }
            assert!(containment(&source).is_empty(), "{source}");
            assert!(contextual(&source).is_empty(), "{source}");
        }
    }
}

#[test]
fn inherited_only_ranges_are_validated_in_the_specializing_receiver() {
    for form in 0..3 {
        for (range, original, actual, reason) in [
            ("0..n", "3", "-1", "upper bound -1"),
            ("0..n", "3", "2.5", "upper bound 2.5"),
            ("0..n", "3", "true", "upper bound must be a Natural"),
            ("n..5", "3", "*", "lower bound inf"),
            ("2..n", "3", "1", "lower bound 2 exceeds upper bound 1"),
            (
                "9007199254740993..n",
                "9007199254740994",
                "9007199254740992",
                "lower bound 9007199254740993 exceeds upper bound 9007199254740992",
            ),
        ] {
            let source = format!(
                "class Base {{ feature n default = {original}; {} }} class Child specializes Base {{ feature n redefines Base::n = {actual}; }}",
                constrained("x", "", range, form)
            );
            let errors = contextual(&source);
            assert_eq!(errors.len(), 1, "{source}: {:?}", messages(&source));
            assert!(errors[0].starts_with("inherited multiplicity of `x`"));
            assert!(errors[0].contains(reason), "{errors:?}");
        }
    }
}

#[test]
fn inherited_only_ranges_preserve_unknowns_and_valid_lexical_baselines() {
    for (original, actual) in [
        ("-1", "-2"),
        ("missing", "-1"),
        ("3", "missing"),
        ("3", "3"),
        ("3", "*"),
    ] {
        for form in 0..3 {
            let source = format!(
                "feature missing; class Base {{ feature n default = {original}; {} }} class Child specializes Base {{ feature n redefines Base::n = {actual}; }}",
                constrained("x", "", "0..n", form)
            );
            assert!(
                contextual(&source).is_empty(),
                "{source}: {:?}",
                messages(&source)
            );
        }
    }
    for source in [
        "class Base { feature n default = 3; feature x[0..n]; } class Child specializes Base, Missing { feature n redefines Base::n = -1; }",
        "class Base specializes Child { feature n default = 3; feature x[0..n]; } class Child specializes Base { feature n redefines Base::n = -1; }",
        "class Base { feature n default = 3; feature lo default = 0; feature x[lo..n]; } class Child specializes Base { feature missing; feature lo redefines Base::lo = missing; feature n redefines Base::n = -1; }",
        "class Base { feature n default = 3; multiplicity a subsets b; multiplicity b subsets a; feature x { multiplicity subsets a; } } class Child specializes Base { feature n redefines Base::n = -1; }",
    ] {
        assert!(
            contextual(source).is_empty(),
            "{source}: {:?}",
            messages(source)
        );
    }
}

#[test]
fn inherited_only_ranges_deduplicate_diamonds_and_preserve_receiver_isolation() {
    for form in 0..3 {
        let source = format!(
            "class Base {{ feature n default = 3; {} }} class Left specializes Base; class Right specializes Base; class Bad specializes Left, Right {{ feature n redefines Base::n = -1; }} class Good specializes Left, Right {{ feature n redefines Base::n = 4; }} class AlsoBad specializes Left, Right {{ feature n redefines Base::n = -2; }}",
            constrained("x", "", "0..n", form)
        );
        let errors = contextual(&source);
        assert_eq!(errors.len(), 2, "{source}: {:?}", messages(&source));
        assert!(errors[0].contains("upper bound -1"), "{errors:?}");
        assert!(errors[1].contains("upper bound -2"), "{errors:?}");
    }
}

#[test]
fn inherited_only_ranges_preserve_prepared_replay_and_receiver_spans() {
    let source = "class Child specializes L::Base { feature n redefines L::Base::n = -1; }";
    for form in 0..3 {
        let library = format!(
            "package L {{ class Base {{ feature n default = 3; {} }} }}",
            constrained("x", "", "0..n", form)
        );
        for (mode, model) in models(&library, &[("child.kerml", source)])
            .into_iter()
            .enumerate()
        {
            let mut r = ResolvedModel::build(&model);
            for _ in 0..2 {
                let findings = check::validate_semantics_with(&mut r, &model);
                assert_eq!(findings.len(), 1, "{mode}: {findings:?}");
                let (unit, d) = &findings[0];
                assert_eq!(model.unit(*unit).name, "child.kerml");
                assert_eq!(
                    &source[d.span.start as usize..d.span.end as usize],
                    "L::Base"
                );
                assert!(d.message.starts_with("inherited multiplicity of `x`"));
            }
            if mode == 3 {
                assert_eq!(model.loaded_library_unit_count(), 0);
            }
        }
    }
}

#[test]
fn inherited_only_ranges_use_bound_identity_across_units_in_both_formats() {
    use std::collections::HashMap;
    use sysmlv2_parser::model::GraphFormat;
    let id = "eeeeeeee-eeee-4eee-8eee-eeeeeeeeeeee";
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for form in 0..3 {
            let mut model = Model::with_graph_format(format);
            model.add_source("base.kerml", &format!(
                "package A {{ class Base {{ feature n default = 3; feature '{id}' = 9; {} }} }}",
                constrained("x", "", &format!("0..'{id}'"), form)
            ));
            model.add_source("child.kerml", &format!("package B {{ feature '{id}' = 8; class Child specializes A::Base {{ feature n redefines A::Base::n = -1; }} }}"));
            assert!(!model.has_errors());
            let mut r = ResolvedModel::build(&model);
            let n = r.resolve_qualified("A::Base::n").unwrap();
            r.override_ids(&HashMap::from([(r.element_id(n), id.parse().unwrap())]));
            let range = if form == 2 {
                r.resolve_qualified("A::Base::xDomain").unwrap()
            } else {
                let x = r.resolve_qualified("A::Base::x").unwrap();
                r.owned_members(x)[0]
            };
            let upper = r.owned_members(range)[1];
            let membership = r.owned_relationships(upper)[0];
            let mut hints = HashMap::from([(
                (r.element_id(membership), "memberElement".into()),
                id.parse().unwrap(),
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&id.parse().unwrap())
            );
            for _ in 0..2 {
                let findings = check::validate_semantics_with(&mut r, &model);
                assert_eq!(findings.len(), 1, "{findings:?}");
                assert_eq!(model.unit(findings[0].0).name, "child.kerml");
                assert!(
                    findings[0].1.message.contains("upper bound -1"),
                    "{findings:?}"
                );
            }
        }
    }
}
