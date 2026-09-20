use sysmlv2_model::{
    full, json,
    model::{Model, ParsedSource},
};
use sysmlv2_transform::{CheckFinding, CheckStage, Library, Session};

fn signature(findings: Vec<CheckFinding>) -> Vec<String> {
    findings
        .into_iter()
        .map(|finding| format!("{finding:?}"))
        .collect()
}

#[test]
fn transferred_syntax_preserves_graphs_positions_and_prepared_unit_offsets() {
    let mut library = Model::new();
    library.add_library_source("library.KerML", "package L { class Base; }");
    let prepared = library.prepare_library().unwrap();
    let mut transferred = Model::new();
    let mut direct = Model::new();
    prepared.clone().install(&mut transferred).unwrap();
    prepared.install(&mut direct).unwrap();
    for (name, text) in [
        ("empty.sysml", ""),
        ("types.KerML", "package K { class C :> L::Base; }"),
        (
            "user.sysml",
            "// café\r\npackage U { part p : K::C; part missing : Unknown; }\n",
        ),
    ] {
        // Populate the combined unit view before insertion; it must invalidate.
        let before = transferred.units().len();
        let parsed = ParsedSource::new(name, text);
        assert_eq!(parsed.name(), name);
        assert!(parsed.diagnostics().is_empty());
        assert_eq!(
            parsed.unit().dialect,
            direct.add_source(name, text).unit.dialect
        );
        transferred.add_parsed_source(parsed);
        assert_eq!(transferred.units().len(), before + 1);
        assert!(!transferred.unit(before).is_library);
    }
    assert_eq!(
        json::model_to_compact_json(&transferred),
        json::model_to_compact_json(&direct)
    );
    assert_eq!(
        full::model_to_full_json_with(&transferred, true),
        full::model_to_full_json_with(&direct, true)
    );
    let check = |model: &Model| {
        let mut resolved = json::ResolvedModel::build(model);
        format!(
            "{:?}",
            sysmlv2_model::check::validate_model_with(&mut resolved, model)
        )
    };
    assert_eq!(check(&transferred), check(&direct));
    assert!(!transferred.has_errors());
}

#[test]
fn transferred_broken_syntax_retains_diagnostics_and_line_index() {
    let text = "// café\r\npackage Broken {\n  part p : ;\n}\n";
    let parsed = ParsedSource::new("broken.sysml", text);
    assert!(!parsed.diagnostics().is_empty());
    let positions: Vec<_> = parsed
        .diagnostics()
        .iter()
        .map(|d| {
            let pos = parsed.lines().line_col(d.span.start);
            (pos.line, pos.col)
        })
        .collect();
    let mut direct = Model::new();
    let mut transferred = Model::new();
    let expected = direct.add_source("broken.sysml", text);
    let actual = transferred.add_parsed_source(parsed);
    assert_eq!(
        format!("{:?}", actual.diagnostics),
        format!("{:?}", expected.diagnostics)
    );
    assert_eq!(format!("{:?}", actual.unit), format!("{:?}", expected.unit));
    for (diagnostic, expected) in actual.diagnostics.iter().zip(positions) {
        let pos = actual.lines.line_col(diagnostic.span.start);
        assert_eq!((pos.line, pos.col), expected);
    }
    assert!(transferred.has_errors());
}

#[test]
fn checking_reused_parses_matches_syntax_plus_independent_session() {
    let sources = vec![
        ("broken.sysml".into(), "package Broken { part p : ; }".into()),
        ("types.KerML".into(), "package K { class C; }".into()),
        ("user.sysml".into(), "// café\r\npackage U { import K::*; part p : C; part missing : Unknown; attribute def V; individual def I :> V; }".into()),
        ("empty.sysml".into(), "".into()),
    ];
    let units = vec![(
        "lib.sysml".into(),
        "package Library { part def Base; }".into(),
    )];
    let syntax = sysmlv2_transform::check_sources_syntax(&sources);
    assert!(syntax.iter().any(|f| f.stage == CheckStage::Parse));
    assert!(syntax.iter().any(|f| f.stage == CheckStage::Context));
    assert_eq!(
        signature(sysmlv2_transform::check_sources(&sources, None).unwrap()),
        signature(syntax.clone())
    );
    for library in [
        Library::sources(units.clone()),
        Library::prepared_sources(units, None).unwrap(),
    ] {
        let mut session =
            Session::from_sources_with_library(sources[1..].to_vec(), Some(library.clone()))
                .unwrap();
        let mut expected = syntax.clone();
        expected.extend(
            session
                .check_findings()
                .into_iter()
                .filter(|f| f.stage != CheckStage::Context),
        );
        assert!(expected.iter().any(|f| f.stage == CheckStage::Referential));
        assert!(expected.iter().any(|f| f.stage == CheckStage::Semantic));
        let actual =
            sysmlv2_transform::check_sources_with_library(&sources, Some(&library)).unwrap();
        assert_eq!(signature(actual), signature(expected));
        assert!(
            sysmlv2_transform::check_sources_with_library(&[], Some(&library))
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            signature(
                sysmlv2_transform::check_sources_with_library(&sources[..1], Some(&library))
                    .unwrap()
            ),
            signature(sysmlv2_transform::check_sources_syntax(&sources[..1]))
        );
    }
    let absent = std::env::temp_dir().join(format!("absent-parsed-library-{}", std::process::id()));
    assert!(!absent.exists());
    let missing = Library::dir(&absent);
    assert!(sysmlv2_transform::check_sources_with_library(&[], Some(&missing)).is_err());
    assert!(sysmlv2_transform::check_sources_with_library(&sources[..1], Some(&missing)).is_err());
}
