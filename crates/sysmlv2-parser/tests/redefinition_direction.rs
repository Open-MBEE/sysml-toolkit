//! Direction validation and repair hints share context-aware identity proofs.
#![cfg(feature = "json")]
use std::{
    collections::{BTreeSet, HashMap},
    sync::Arc,
};
use sysmlv2_model::{
    check, json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};
const RULE: &str = "validateRedefinitionDirectionConformance";
const ID: &str = "77777777-7777-4777-8777-777777777777";

fn models(library: &str, users: &[(String, String)]) -> Vec<(Model, ResolvedModel)> {
    let mut base = Model::new();
    let u = base.add_library_source("directions.kerml", library);
    assert!(u.diagnostics.is_empty(), "{:?}", u.diagnostics);
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(51).unwrap(), 51).unwrap());
    (0..4)
        .map(|mode| {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("directions.kerml", library);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            for (name, src) in users {
                let u = m.add_source(name.clone(), src);
                assert!(u.diagnostics.is_empty(), "{name}: {:?}", u.diagnostics);
            }
            let r = ResolvedModel::build(&m);
            (m, r)
        })
        .collect()
}
fn user(src: &str) -> Vec<(String, String)> {
    vec![("user.kerml".into(), src.into())]
}
fn direction_count(r: &mut ResolvedModel, m: &Model) -> usize {
    check::validate_semantics_with(r, m)
        .iter()
        .filter(|(_, d)| d.code == Some(RULE))
        .count()
}
fn allowed(target: usize, own: usize) -> bool {
    target == 0 || (target == 3 && own != 0) || target == own
}

#[test]
fn all_direction_pairs_distinguish_missing_from_inout() {
    let dirs = ["", "in ", "out ", "inout "];
    let library = dirs
        .iter()
        .enumerate()
        .map(|(n, d)| format!("classifier B{n} {{{d}feature p;}}"))
        .collect::<String>();
    let mut users = Vec::new();
    let mut expected = BTreeSet::new();
    for target in 0..4 {
        for (own, direction) in dirs.iter().enumerate() {
            let name = format!("case-{target}-{own}.kerml");
            users.push((name.clone(),format!("classifier Child{target}{own} specializes B{target} {{{}feature p redefines B{target}::p;}}",direction)));
            if !allowed(target, own) {
                expected.insert(name);
            }
        }
    }
    for (mode, (m, mut r)) in models(&library, &users).into_iter().enumerate() {
        let loaded = m.loaded_library_unit_count();
        for warm in [false, true] {
            if warm {
                for target in 0..4 {
                    for own in 0..4 {
                        let e = r
                            .resolve_qualified(&format!("Child{target}{own}::p"))
                            .unwrap();
                        r.implied_relationships(e);
                        r.derived(e, "featuringType");
                    }
                }
            }
            let ds = check::validate_semantics_with(&mut r, &m);
            let actual = ds
                .iter()
                .filter(|(_, d)| d.code == Some(RULE))
                .map(|(u, _)| m.unit(*u).name.clone())
                .collect::<BTreeSet<_>>();
            assert_eq!(actual, expected, "mode {mode}, warm {warm}: {ds:?}");
            assert_eq!(ds.iter().filter(|(_, d)| d.code == Some(RULE)).count(), 7);
        }
        assert_eq!(m.loaded_library_unit_count(), loaded);
    }
}

#[test]
fn conjugated_repair_hints_agree_with_spelled_redefinition() {
    for double in [false, true] {
        for (own, direction) in ["", "in ", "out ", "inout "].into_iter().enumerate() {
            let (library, base, required) = if double {
                (
                    "classifier A {in feature p;} classifier B conjugates A;",
                    "B",
                    1,
                )
            } else {
                ("classifier A {in feature p;}", "A", 2)
            };
            let src = format!(
                "classifier C conjugates {base} {{{direction}feature p;}} classifier Spelled conjugates {base} {{{direction}feature p redefines A::p;}}"
            );
            for (mode, (m, mut r)) in models(library, &user(&src)).into_iter().enumerate() {
                let loaded = m.loaded_library_unit_count();
                for _ in 0..2 {
                    let findings = check::inherited_name_collisions(&mut r);
                    let c = r.resolve_qualified("C::p").unwrap();
                    let finding = findings
                        .iter()
                        .find(|f| f.element == c)
                        .unwrap_or_else(|| panic!("mode {mode}: {findings:?}"));
                    assert_eq!(
                        finding.redefinition_target.is_some(),
                        own == required,
                        "double {double}, local {direction:?}, mode {mode}: {finding:?}"
                    );
                    assert_eq!(direction_count(&mut r, &m), usize::from(own != required));
                    r.implied_relationships(c);
                    r.derived(c, "featuringType");
                }
                assert_eq!(m.loaded_library_unit_count(), loaded);
            }
        }
    }
}

#[test]
fn undirected_and_inout_targets_have_distinct_repair_requirements() {
    for (target, td) in [(0, ""), (3, "inout ")] {
        for (own, od) in ["", "in ", "out ", "inout "].into_iter().enumerate() {
            let library = format!("classifier Base {{{td}feature p;}}");
            let src = format!(
                "classifier C specializes Base {{{od}feature p;}} classifier Spelled specializes Base {{{od}feature p redefines Base::p;}}"
            );
            for (m, mut r) in models(&library, &user(&src)) {
                let c = r.resolve_qualified("C::p").unwrap();
                let findings = check::inherited_name_collisions(&mut r);
                let f = findings.iter().find(|f| f.element == c).unwrap();
                assert_eq!(
                    f.redefinition_target.is_some(),
                    allowed(target, own),
                    "{f:?}"
                );
                assert_eq!(
                    direction_count(&mut r, &m),
                    usize::from(!allowed(target, own))
                );
            }
        }
    }
}

#[test]
fn typed_and_transitive_contexts_preserve_direction_requirements() {
    let library = "classifier Base {in feature p;} classifier Mid specializes Base;";
    let src = "classifier Good specializes Mid {in feature p redefines Base::p;}
        classifier Missing specializes Mid {feature p redefines Base::p;}
        feature good : Mid {in feature p redefines Base::p;}
        feature missing : Mid {feature p redefines Base::p;}
        feature wrong : Mid {out feature p redefines Base::p;}";
    for (m, mut r) in models(library, &user(src)) {
        let loaded = m.loaded_library_unit_count();
        for _ in 0..2 {
            assert_eq!(direction_count(&mut r, &m), 3);
        }
        assert_eq!(m.loaded_library_unit_count(), loaded);
    }
}

#[test]
fn incomplete_direction_contexts_do_not_offer_repairs_or_invent_errors() {
    let library = "classifier Base {in feature p;}";
    for (name, extra) in [("Missing", "missing"), ("Cycle", "C")] {
        let src = format!(
            "classifier C specializes Base, {extra} {{feature p;}} classifier Spelled specializes Base, {extra} {{feature p redefines Base::p;}}"
        );
        for (m, mut r) in models(library, &user(&src)) {
            let findings = check::inherited_name_collisions(&mut r);
            let local = r.resolve_qualified("C::p").unwrap();
            let base = r.resolve_qualified("Base::p").unwrap();
            let directed = findings
                .iter()
                .find(|f| f.element == local && f.hidden == Some(base))
                .unwrap_or_else(|| panic!("missing directed collision {name}: {findings:?}"));
            assert!(
                directed.redefinition_target.is_none(),
                "{name}: {directed:?}"
            );
            assert_eq!(direction_count(&mut r, &m), 0);
        }
    }
}

#[test]
fn bound_redefinition_target_identity_is_local_to_its_source_unit() {
    for (actual, spelled, expected) in [("in ", "out ", "B.kerml"), ("out ", "in ", "A.kerml")] {
        let source = format!(
            "classifier Base {{{actual}feature actual;{spelled}feature '{ID}';}} classifier Child specializes Base {{in feature p redefines '{ID}';}}"
        );
        let users = [
            ("A.kerml".into(), format!("package A {{{source}}}")),
            ("B.kerml".into(), format!("package B {{{source}}}")),
        ];
        for (m, mut r) in models("package Empty;", &users) {
            let actual = r.resolve_qualified("A::Base::actual").unwrap();
            r.override_ids(&HashMap::from([(
                r.element_id(actual),
                ID.parse().unwrap(),
            )]));
            let child = r.resolve_qualified("A::Child::p").unwrap();
            let rel = r
                .owned_relationships(child)
                .into_iter()
                .find(|e| r.element_type(*e) == "Redefinition")
                .unwrap();
            let mut hints = HashMap::from([(
                (r.element_id(rel), "redefinedFeature".into()),
                ID.parse().unwrap(),
            )]);
            assert!(
                r.bind_id_spelled_references_with(&mut hints)
                    .contains(&ID.parse().unwrap())
            );
            for _ in 0..2 {
                let ds = check::validate_semantics_with(&mut r, &m);
                let dirs = ds
                    .iter()
                    .filter(|(_, d)| d.code == Some(RULE))
                    .collect::<Vec<_>>();
                assert_eq!(dirs.len(), 1, "{ds:?}");
                assert_eq!(m.unit(dirs[0].0).name, expected);
                let source = &users.iter().find(|(n, _)| n == expected).unwrap().1;
                assert_eq!(
                    &source[dirs[0].1.span.start as usize..dirs[0].1.span.end as usize],
                    format!("'{ID}'")
                );
            }
        }
    }
}

#[test]
fn explicit_featuring_contexts_check_each_proven_direction() {
    let library = "classifier A {in feature p;} classifier Ordinary specializes A; classifier Flipped conjugates A;";
    let src = "in feature good redefines A::p featured by Ordinary;
        feature missing redefines A::p featured by Ordinary;
        in feature mixed redefines A::p featured by Ordinary, Flipped;
        in feature partial redefines A::p featured by Flipped, missingType;
        out feature unknown redefines A::p featured by missingType;";
    for (m, mut r) in models(library, &user(src)) {
        for warm in [false, true] {
            if warm {
                for name in ["good", "missing", "mixed", "partial", "unknown"] {
                    let e = r.resolve_qualified(name).unwrap();
                    r.derived(e, "featuringType");
                }
            }
            assert_eq!(direction_count(&mut r, &m), 3);
        }
    }
}
