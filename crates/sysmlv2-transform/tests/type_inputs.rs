use sysmlv2_transform::{GraphFormat, Indent, Library, ModelHandle, Session};

fn inputs(s: &mut Session) -> Vec<String> {
    let r = s.resolved();
    let f = r.resolve_qualified("G").unwrap();
    r.type_input_report(f)
        .inputs
        .unwrap()
        .into_iter()
        .map(|e| r.element_id(e).to_string())
        .collect()
}
#[test]
fn checked_inputs_survive_full_json_replay_and_session_rename() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut model = ModelHandle::with_graph_format(format);
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        let lib = Library::Prepared(model.prepare_library().unwrap());
        let mut s = Session::from_sources_with_graph_format(
            vec![(
                "inputs.kerml".into(),
                "function F { in a; inout b; return answer; } function G specializes F;".into(),
            )],
            Some(lib.clone()),
            format,
        )
        .unwrap();
        let expected = inputs(&mut s);
        let full = s.to_full_json();
        let mut replay = Session::from_interchange_json_with_graph_format(
            &full,
            Some(&lib),
            &["inputs.kerml".into()],
            Indent::default(),
            format,
        )
        .unwrap();
        assert!(replay.warnings().is_empty(), "{:?}", replay.warnings());
        assert_eq!(inputs(&mut replay), expected);
        let a = replay.resolved().resolve_qualified("F::a").unwrap();
        let mut edit = replay.edit();
        edit.rename(a, "renamed");
        edit.commit().unwrap();
        let expected = ["F::renamed", "F::b"]
            .into_iter()
            .map(|name| {
                let e = replay.resolved().resolve_qualified(name).unwrap();
                replay.resolved().element_id(e).to_string()
            })
            .collect::<Vec<_>>();
        assert_eq!(inputs(&mut replay), expected);
    }
}
