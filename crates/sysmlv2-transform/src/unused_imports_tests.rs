//! Text-stage differential tests; graph parity is tested in the model crate.
use super::*;
fn legacy(resolved: &mut ResolvedModel, texts: &[(usize, String)]) -> Vec<(usize, Span)> {
    let candidates = resolved.unused_private_imports();
    let mut out = Vec::new();
    for (_, target, unit, span) in candidates {
        let Some((_, text)) = texts.iter().find(|(i, _)| *i == unit) else {
            continue; // library unit — never reported
        };
        let names = resolved.namespace_member_names(target);
        let mentioned = names
            .iter()
            .any(|name| !name.is_empty() && mentions_outside(text, name, span));
        if !mentioned {
            out.push((unit, span));
        }
    }
    out
}

fn mentions_outside(text: &str, name: &str, skip: Span) -> bool {
    let bytes = text.as_bytes();
    let is_word = |b: u8| b.is_ascii_alphanumeric() || b == b'_';
    let mut from = 0;
    while let Some(i) = text[from..].find(name) {
        let start = from + i;
        let end = start + name.len();
        from = start + name.chars().next().unwrap().len_utf8();
        if start >= skip.start as usize && end <= skip.end as usize {
            continue;
        }
        let left_ok = start == 0 || !is_word(bytes[start - 1]);
        let right_ok = end >= bytes.len() || !is_word(bytes[end]);
        if left_ok && right_ok {
            return true;
        }
    }
    false
}

fn compare(sources: &[(&str, &str)]) {
    let mut model = Model::new();
    let texts: Vec<_> = sources
        .iter()
        .enumerate()
        .map(|(i, (name, text))| {
            let unit = model.add_source(*name, text);
            assert!(
                unit.diagnostics.is_empty(),
                "{name}: {:?}",
                unit.diagnostics
            );
            (i, text.to_string())
        })
        .collect();
    let mut resolved = ResolvedModel::build(&model);
    let expected = legacy(&mut resolved, &texts);
    assert_eq!(unused_private_imports_with(&mut resolved, &texts), expected);
    assert_eq!(
        unused_private_imports_with(&mut resolved, &texts),
        expected,
        "repeated call"
    );
    assert!(unused_private_imports_with(&mut resolved, &[]).is_empty());
}

#[test]
fn text_index_preserves_conservative_import_contract() {
    for body in [
        "part def Other;",
        "part x : Leaf;",
        "part x : Defs::Leaf;",
        "// Leaf in a comment",
        "/* Leaf */",
        "part 'Leaf';",
        "part LeafSuffix;",
        "part _Leaf;",
        "part PrefixLeaf;",
        "alias Alias for Defs::Leaf; part x : Alias;",
        "package Nested { private import Defs::Leaf; part x : Leaf; }",
        "private import Defs::*;",
        "public import Defs::*;",
        "protected import Defs::*;",
        "private import Missing::*;",
        "part 'é';",
        "/* é */",
        "/* 😀 */",
    ] {
        for import in [
            "private import Defs::*;",
            "private import Defs::Leaf;",
            "private import Defs::**;",
        ] {
            let source = format!("package User {{ {import} {body}\n }}");
            compare(&[
                (
                    "defs.sysml",
                    "package Defs { part def Leaf; part def 'é'; part def '😀'; }",
                ),
                ("user.sysml", &source),
            ]);
        }
    }
    compare(&[
        ("defs.kerml", "package Defs { class Leaf; }"),
        ("user.kerml", "package User { import Defs::*; }"),
    ]);
    compare(&[
        (
            "defs.sysml",
            "package Defs { metadata def M; #M part def Leaf; part def Other; }",
        ),
        (
            "user.sysml",
            "package User { private import Defs::*[@Defs::M]; part x : Leaf; }",
        ),
    ]);
}

#[test]
fn text_extent_handles_overlap_boundaries_and_unicode() {
    assert_eq!(mention_extent("é", "é"), Some((0, 2)));
    assert_eq!(mention_extent("😀 😀", "😀"), Some((0, 9)));
    assert_eq!(mention_extent("ééé", "éé"), Some((0, 6)));
    assert_eq!(mention_extent("xName Name_ Name", "Name"), Some((12, 16)));
    assert_eq!(mention_extent("anything", ""), None);
}

#[test]
fn imports_are_recomputed_after_edits() {
    let mut session = Session::from_sources(vec![
        (
            "defs.sysml".into(),
            "package Defs { part def Leaf; }".into(),
        ),
        (
            "user.sysml".into(),
            "package User { private import Defs::*; part p; }".into(),
        ),
    ])
    .unwrap();
    let before = session.unused_private_imports();
    assert_eq!(before.len(), 1);
    let p = session.resolved().resolve_qualified("User::p").unwrap();
    let mut edit = session.edit();
    edit.replace_member(p, "part p : Leaf;");
    edit.commit().unwrap();
    assert!(session.unused_private_imports().is_empty());
    let p = session.resolved().resolve_qualified("User::p").unwrap();
    let mut edit = session.edit();
    edit.replace_member(p, "part p;");
    edit.commit().unwrap();
    assert_eq!(session.unused_private_imports(), before);
}

#[test]
fn corpus_text_results_match_legacy_with_cold_and_replayed_libraries() {
    let root = sysmlv2_testkit::workspace_root();
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        return;
    }
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    sysmlv2_model::ambient::add_to(&mut base);
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache = base.take_recorded_library_cache().unwrap();
    let prepared = base.prepare_library().unwrap();
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
        sysmlv2_testkit::collect_files(&path, &mut paths);
        paths.sort();
        let mut prior = None;
        for replay in 0..3 {
            let mut model = Model::new();
            if replay == 2 {
                prepared.clone().install(&mut model).unwrap();
            } else {
                model.load_library_dir(&library).unwrap();
                sysmlv2_model::ambient::add_to(&mut model);
            }
            if replay == 1 {
                model.set_library_cache(cache.clone());
            }
            let offset = model.units().len();
            let texts: Vec<_> = paths
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    let source = std::fs::read_to_string(p).unwrap();
                    model.add_source(p.display().to_string(), &source);
                    (offset + i, source)
                })
                .collect();
            let mut resolved = ResolvedModel::build(&model);
            let expected = legacy(&mut resolved, &texts);
            let actual = unused_private_imports_with(&mut resolved, &texts);
            assert_eq!(actual, expected, "{corpus}, replay={replay}");
            if corpus.contains("apollo") {
                assert_eq!(actual.len(), 39);
            }
            sysmlv2_model::check::validate_model_with(&mut resolved, &model);
            sysmlv2_model::check::validate_semantics_with(&mut resolved, &model);
            assert_eq!(
                unused_private_imports_with(&mut resolved, &texts),
                actual,
                "validation must preserve import provenance: {corpus}, replay={replay}"
            );
            if let Some(prior) = prior {
                assert_eq!(actual, prior, "cold/replay parity");
            }
            prior = Some(actual);
        }
    }
}
