//! Filter execution and diagnostics retain declaration source across replay.
#![cfg(feature = "json")]
use std::{collections::HashMap, sync::Arc};
use sysmlv2_parser::{
    check, json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};
const ID: &str = "88888888-8888-4888-8888-888888888888";

fn models(a: &str, b: &str, filters_in_library: bool) -> Vec<Model> {
    let scalars = "package ScalarValues { datatype Integer; datatype Boolean; }";
    let mut base = Model::new();
    base.add_library_source("scalar.kerml", scalars);
    if filters_in_library {
        base.add_library_source("A.sysml", a);
        base.add_library_source("B.sysml", b);
    }
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
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("scalar.kerml", scalars);
                    if filters_in_library {
                        m.add_library_source("A.sysml", a);
                        m.add_library_source("B.sysml", b);
                    }
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            if !filters_in_library {
                m.add_source("A.sysml", a);
                m.add_source("B.sysml", b);
            }
            assert!(!m.has_errors());
            m
        })
        .collect()
}

#[test]
fn import_and_expose_filters_use_their_own_source_identity() {
    for form in ["namespace", "membership", "standalone", "expose"] {
        for reverse in [false, true] {
            let filter = match form {
                "namespace" => format!("package View {{ public import Items::*[@'{ID}']; }}"),
                "membership" => format!("package View {{ public import Items::X[@'{ID}']; }}"),
                "standalone" => {
                    format!("package View {{ filter @'{ID}'; public import Items::*; }}")
                }
                _ => format!("view def View {{ expose Items::*[@'{ID}']; }}"),
            };
            let annotation = if reverse {
                format!("'{ID}'")
            } else {
                "Actual".into()
            };
            let source = |pkg| {
                format!(
                    "package {pkg} {{ metadata def Actual; metadata def '{ID}'; package Items {{ #{annotation} part def X; }} {filter} }}"
                )
            };
            let a = source("A");
            let b = source("B");
            for library in [false, true] {
                for (mode, model) in models(&a, &b, library).into_iter().enumerate() {
                    let mut r = ResolvedModel::build(&model);
                    if !library {
                        let actual = r.resolve_qualified("A::Actual").unwrap();
                        let view = r.resolve_qualified("A::View").unwrap();
                        let candidates = r.elements_of_metaclass("FeatureTyping");
                        let edge = candidates
                            .into_iter()
                            .find(|&edge| {
                                let mut owner = r.owner(edge);
                                while let Some(e) = owner {
                                    if e == view {
                                        return true;
                                    }
                                    owner = r.owner(e);
                                }
                                false
                            })
                            .unwrap();
                        r.override_ids(&HashMap::from([(
                            r.element_id(actual),
                            ID.parse().unwrap(),
                        )]));
                        let mut hints = HashMap::from([(
                            (r.element_id(edge), "type".into()),
                            ID.parse().unwrap(),
                        )]);
                        assert!(
                            r.bind_id_spelled_references_with(&mut hints)
                                .contains(&ID.parse().unwrap())
                        );
                    }
                    for pkg in ["B", "A", "A", "B"] {
                        let view = r.resolve_qualified(&format!("{pkg}::View")).unwrap();
                        let members = if form == "expose" {
                            r.view_exposed_elements(view)
                        } else {
                            r.imported_memberships(view)
                        };
                        let expected = usize::from(if library {
                            reverse
                        } else {
                            (pkg == "A") != reverse
                        });
                        assert_eq!(
                            members.len(),
                            expected,
                            "{form} reverse={reverse} library={library} mode={mode} {pkg}"
                        );
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
fn root_filter_diagnostics_have_their_own_unit_and_span() {
    for (mode, mut model) in models("package A;", "package B;", false)
        .into_iter()
        .enumerate()
    {
        let bad = "filter 1; import A::*[2];";
        let good = "filter true; import B::*[true];";
        model.add_source("bad.kerml", bad);
        model.add_source("good.kerml", good);
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        if mode == 3 {
            // Root filters affect library root imports and require joint resolution.
            assert_eq!(model.loaded_library_unit_count(), 1);
        }
        for _ in 0..2 {
            let found: Vec<_> = check::validate_semantics_with(&mut r, &model)
                .into_iter()
                .filter(|(_, d)| d.code == Some("validateElementFilterMembershipIsBoolean"))
                .collect();
            assert_eq!(found.len(), 2, "mode {mode}: {found:?}");
            let mut values = Vec::new();
            for (u, d) in found {
                assert_eq!(model.unit(u).name, "bad.kerml");
                values.push(&bad[d.span.start as usize..d.span.end as usize]);
            }
            values.sort();
            assert_eq!(values, ["1", "2"]);
        }
        if mode == 3 {
            assert_eq!(model.loaded_library_unit_count(), 1);
        }
    }
}

#[test]
fn metadata_attribute_filter_preserves_source_bound_identity() {
    let source = |package| {
        format!(
            "package {package} {{ metadata def Flag {{attribute actual; attribute '{ID}';}} \
         package Items {{part X {{@Flag {{actual=false; '{ID}'=true;}}}}}} \
         view View {{expose Items::*[(as Flag).'{ID}'];}} }}"
        )
    };
    for (mode, model) in models(&source("A"), &source("B"), false)
        .into_iter()
        .enumerate()
    {
        let loaded = model.loaded_library_unit_count();
        let mut r = ResolvedModel::build(&model);
        let actual = r.resolve_qualified("A::Flag::actual").unwrap();
        let view = r.resolve_qualified("A::View").unwrap();
        let mut members = Vec::new();
        for edge in r.elements_of_metaclass("Membership") {
            let Some(chain) = r.owner(edge) else { continue };
            if r.element_type(chain) != "FeatureChainExpression" {
                continue;
            }
            let mut owner = r.owner(chain);
            while let Some(element) = owner {
                if element == view {
                    members.push(edge);
                    break;
                }
                owner = r.owner(element);
            }
        }
        assert_eq!(members.len(), 1);
        let edge = members[0];
        r.override_ids(&HashMap::from([(
            r.element_id(actual),
            ID.parse().unwrap(),
        )]));
        let mut hints = HashMap::from([(
            (r.element_id(edge), "memberElement".into()),
            ID.parse().unwrap(),
        )]);
        assert!(
            r.bind_id_spelled_references_with(&mut hints)
                .contains(&ID.parse().unwrap())
        );
        for package in ["B", "A", "A", "B"] {
            let view = r.resolve_qualified(&format!("{package}::View")).unwrap();
            let exposed = r.view_exposed_elements(view);
            // A's identical spelling/span is bound to actual=false; B keeps
            // its lexical UUID-shaped attribute=true in its own source unit.
            let expected = if package == "A" {
                Vec::new()
            } else {
                vec![r.resolve_qualified("B::Items::X").unwrap()]
            };
            assert_eq!(exposed, expected, "mode {mode}, package {package}");
        }
        // Rebinding the target UUID must preserve A's source-site identity,
        // while B's lexical UUID-shaped declaration stays lexical.
        let rebound = "99999999-9999-4999-8999-999999999999".parse().unwrap();
        r.override_ids(&HashMap::from([(ID.parse().unwrap(), rebound)]));
        let a = r.resolve_qualified("A::View").unwrap();
        let b = r.resolve_qualified("B::View").unwrap();
        assert!(
            r.view_exposed_elements(a).is_empty(),
            "remapped mode {mode}"
        );
        let bx = r.resolve_qualified("B::Items::X").unwrap();
        assert_eq!(r.view_exposed_elements(b), vec![bx], "remapped mode {mode}");
        assert_eq!(model.loaded_library_unit_count(), loaded);
        if mode == 3 {
            assert_eq!(loaded, 0);
        }
    }
}
