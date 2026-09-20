//! Differential oracle for the conservative import contract.
use super::*;
use crate::model::Model;
use std::{
    fmt::Write as _,
    fs,
    path::{Path, PathBuf},
};

impl ResolvedModel {
    fn namespace_member_names_legacy(&self, e: ElementRef) -> Vec<String> {
        let mut out = Vec::new();
        let mut frontier = vec![(e, 0usize)];
        while let Some((cur, depth)) = frontier.pop() {
            let props = &self.b.elements[cur.0].props;
            for key in ["declaredName", "declaredShortName"] {
                if let Some(name) = props.get(key).and_then(|v| v.as_str()) {
                    out.push(name.to_string());
                }
            }
            if depth < 8 && out.len() < 4096 {
                for m in self.owned_members(cur) {
                    frontier.push((m, depth + 1));
                }
            }
        }
        out
    }

    fn unused_private_imports_legacy(&mut self) -> Vec<(ElementRef, ElementRef, usize, Span)> {
        let candidates: Vec<(usize, Span, usize)> = self
            .b
            .user_imports
            .iter()
            .filter(|imp| {
                imp.visibility == Some(Visibility::Private)
                    && !self.b.used_imports.contains(&imp.rel)
            })
            .map(|imp| (imp.rel, imp.span, self.b.unit_of_elem(imp.rel)))
            .collect();
        let mut out = Vec::new();
        for (rel, span, unit) in candidates {
            // The import's own target (recorded as a ref site inside the
            // member span). An unresolved target already warns
            // referentially — stay quiet here.
            let Some(target) = self
                .b
                .ref_sites
                .iter()
                .find(|s| {
                    s.unit == unit
                        && s.span.start >= span.start
                        && s.span.end <= span.end
                        && (s.kind == "importedNamespace" || s.kind == "importedMembership")
                })
                .map(|s| s.target)
            else {
                continue;
            };
            let sites: Vec<ElementRef> = self
                .b
                .ref_sites
                .iter()
                .filter(|s| {
                    s.unit == unit && !(s.span.start >= span.start && s.span.end <= span.end)
                })
                .map(|s| s.target)
                .collect();
            let mut feeds = false;
            for site_target in sites {
                if site_target == target {
                    feeds = true;
                    break;
                }
                let mut e = site_target;
                for _ in 0..64 {
                    match self.owner(e) {
                        Some(o) if o == target => {
                            feeds = true;
                            break;
                        }
                        Some(o) => e = o,
                        None => break,
                    }
                }
                if feeds {
                    break;
                }
            }
            if !feeds {
                out.push((ElementRef(rel), target, unit, span));
            }
        }
        out
    }
}

fn files(root: &Path, out: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(root).unwrap() {
        let path = entry.unwrap().path();
        if path.is_dir() {
            files(&path, out);
        } else if path
            .extension()
            .is_some_and(|x| x == "sysml" || x == "kerml")
        {
            out.push(path);
        }
    }
}

fn compare(model: &Model) {
    let units: Vec<_> = model
        .units()
        .iter()
        .enumerate()
        .filter_map(|(i, u)| (!u.is_library).then_some(i))
        .collect();
    let mut resolved = ResolvedModel::build(model);
    let expected = resolved.unused_private_imports_legacy();
    let targets: Vec<_> = expected.iter().map(|(_, t, _, _)| *t).collect();
    let names = resolved.namespace_member_names_many(&targets);
    for t in targets {
        assert_eq!(
            names[&t],
            resolved.namespace_member_names_legacy(t),
            "namespace enumeration contract"
        );
    }
    assert_eq!(
        resolved.unused_private_imports(),
        expected,
        "all-unit contract"
    );
    let expected: Vec<_> = expected
        .into_iter()
        .filter(|(_, _, u, _)| units.contains(u))
        .collect();
    assert_eq!(
        resolved.unused_private_imports_for_units(&units),
        expected,
        "unit-filtered contract"
    );
    assert!(resolved.unused_private_imports_for_units(&[]).is_empty());
}

#[test]
fn indexed_imports_match_legacy_on_cold_and_replayed_corpora() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let library = root.join("spec-refs/SysML-v2-Release/sysml.library");
    if !library.is_dir() {
        return;
    }
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache = base.take_recorded_library_cache().unwrap();
    let mut corpora = vec![
        "spec-refs/SysML-v2-Release/sysml/src".to_string(),
        "spec-refs/apollo-11-sysml-v2".to_string(),
    ];
    if let Ok(path) = std::env::var("SYSMLV2_IMPORT_CORPUS") {
        corpora.push(path);
    }
    for corpus in corpora {
        let path = root.join(&corpus);
        if !path.is_dir() {
            continue;
        }
        let mut paths = Vec::new();
        files(&path, &mut paths);
        paths.sort();
        for replay in [false, true] {
            let mut model = Model::new();
            model.load_library_dir(&library).unwrap();
            if replay {
                model.set_library_cache(cache.clone());
            }
            for path in &paths {
                model.add_source(
                    path.display().to_string(),
                    &fs::read_to_string(path).unwrap(),
                );
            }
            compare(&model);
        }
    }
}

#[test]
fn indexed_imports_match_legacy_on_generated_graphs() {
    // Deep grammar nesting needs more stack than the test harness default.
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(|| {
            for depth in [1, 8, 63, 64, 65, 80] {
                let mut model = Model::new();
                let mut defs = String::from("package Defs {");
                for n in 0..depth {
                    let _ = write!(defs, "package N{n} {{");
                }
                defs.push_str("part def Leaf;");
                defs.push_str(&"}".repeat(depth + 1));
                model.add_source("defs.sysml", &defs);
                for unit in 0..3 {
                    let mut source = format!("package U{unit} {{");
                    for _ in 0..12 {
                        source.push_str("private import Defs::*;");
                    }
                    source.push_str("private import Missing::*; public import Defs::*;");
                    let name = format!(
                        "Defs::{}Leaf",
                        (0..depth).map(|n| format!("N{n}::")).collect::<String>()
                    );
                    let _ = write!(source, "part p : {name}; }}");
                    model.add_source(format!("u{unit}.sysml"), &source);
                }
                compare(&model);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}

#[test]
fn namespace_index_preserves_wide_traversal_cutoff() {
    let mut source = String::from("package Defs {");
    for p in 0..12 {
        let _ = write!(source, "package P{p} {{");
        for e in 0..400 {
            let _ = write!(source, "part def E{e};");
        }
        source.push('}');
    }
    source.push('}');
    let mut model = Model::new();
    model.add_source("wide.sysml", &source);
    let mut resolved = ResolvedModel::build(&model);
    let target = resolved.resolve_qualified("Defs").unwrap();
    let expected = resolved.namespace_member_names_legacy(target);
    assert!(expected.len() >= 4096);
    assert!(expected.len() < 4813);
    assert_eq!(resolved.namespace_member_names(target), expected);
}

#[test]
fn ancestry_index_keeps_the_exact_64_owner_limit() {
    std::thread::Builder::new()
        .stack_size(32 * 1024 * 1024)
        .spawn(|| {
            for depth in [63, 64, 65] {
                let defs = format!(
                    "package Defs {{ {} part def Leaf; {}",
                    (0..depth)
                        .map(|i| format!("package N{i} {{"))
                        .collect::<String>(),
                    "}".repeat(depth + 1)
                );
                let mut model = Model::new();
                model.add_source("defs.sysml", &defs);
                model.add_source("user.sysml", "package User { private import Defs::*; }");
                let mut r = ResolvedModel::build(&model);
                let leaf =
                    r.b.elements
                        .iter()
                        .position(|e| {
                            e.props.get("declaredName").and_then(|v| v.as_str()) == Some("Leaf")
                        })
                        .unwrap();
                // Supply a resolved use directly so this boundary test does not
                // depend on the resolver's separate qualified-name depth budget.
                let mut site =
                    r.b.ref_sites
                        .iter()
                        .find(|s| s.unit == 1 && s.kind == "importedNamespace")
                        .unwrap()
                        .clone();
                site.span = Span::new(0, 1);
                site.target = ElementRef(leaf);
                site.kind = "type".into();
                r.b.ref_sites.push(site);
                let expected = r.unused_private_imports_legacy();
                assert_eq!(expected.len(), usize::from(depth >= 64));
                assert_eq!(r.unused_private_imports_for_units(&[1]), expected);
            }
        })
        .unwrap()
        .join()
        .unwrap();
}
