use sysmlv2_model::{eval::Value, migration::validate_graph_format};
use sysmlv2_transform::{GraphFormat, Indent, Library, Session};

fn session() -> Session {
    Session::from_sources_with_graph_format(
        vec![(
            "p.sysml".into(),
            "package P { attribute x = if true ? 7 else 1/0; attribute y = x; }".into(),
        )],
        None,
        GraphFormat::CanonicalV3,
    )
    .unwrap()
}
#[test]
fn canonical_sessions_preserve_format_through_edits_and_transport() {
    let mut s = session();
    let base = s.to_compact_json();
    let x = s.resolved().resolve_qualified("P::x").unwrap();
    let mut edit = s.edit();
    edit.rename(x, "renamed");
    edit.commit().unwrap();
    s.minimize_qualifications().unwrap();
    s.load_library_from(Library::sources(vec![(
        "lib.kerml".into(),
        "package L { feature f; }".into(),
    )]))
    .unwrap();
    assert_eq!(s.model().graph_format(), GraphFormat::CanonicalV3);
    assert_eq!(
        s.resolved().evaluate_qualified("P::y"),
        Ok(Value::Integer(7))
    );
    let target = s.to_compact_json();
    validate_graph_format(&target, GraphFormat::CanonicalV3).unwrap();
    let bytes = s.to_compact_cbor();
    assert_eq!(
        sysmlv2_cbor::describe(&bytes).unwrap()["versions"]["scheme"],
        3
    );
    let mut replay = Session::from_compact_cbor(&bytes).unwrap();
    assert_eq!(replay.model().graph_format(), GraphFormat::CanonicalV3);
    assert_eq!(replay.to_compact_json(), target);
    assert_eq!(
        replay.resolved().evaluate_qualified("P::y"),
        Ok(Value::Integer(7))
    );
    let elided = s.to_compact_cbor_elided().unwrap();
    assert_eq!(s.decode_cbor(&elided).unwrap(), target);
    let full = s.to_full_cbor(false);
    assert_eq!(
        sysmlv2_cbor::describe(&full).unwrap()["versions"]["scheme"],
        3
    );
    for elided in [false, true] {
        let bytes = if elided {
            s.delta_cbor_elided_from(&base)
        } else {
            s.delta_cbor_from(&base, false)
        }
        .unwrap();
        assert_eq!(
            sysmlv2_cbor::describe(&bytes).unwrap()["versions"]["scheme"],
            3
        );
        let (applied, report) = s.apply_delta_cbor_to(&bytes, &base, false).unwrap();
        assert!(report.base_matched);
        assert_eq!(sysmlv2_cbor::delta_canonical(&target).unwrap(), applied);
    }
}

#[test]
fn canonical_constructor_ownership_survives_rename_replay_and_deltas() {
    let mut session = Session::from_sources_with_graph_format(
        vec![(
            "constructors.kerml".into(),
            "class Point {feature x;} feature p=new Point(x=if true ? 7 else 8);".into(),
        )],
        None,
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    let base = session.to_compact_json();
    let point = session.resolved().resolve_qualified("Point").unwrap();
    let mut edit = session.edit();
    edit.rename(point, "Position");
    edit.commit().unwrap();
    let target = session.to_compact_json();
    validate_graph_format(&target, GraphFormat::CanonicalV3).unwrap();
    for elided in [false, true] {
        let bytes = if elided {
            session.delta_cbor_elided_from(&base)
        } else {
            session.delta_cbor_from(&base, false)
        }
        .unwrap();
        let (applied, report) = session.apply_delta_cbor_to(&bytes, &base, false).unwrap();
        assert!(report.base_matched);
        assert_eq!(applied, sysmlv2_cbor::delta_canonical(&target).unwrap());
    }
    let mut replay = Session::from_compact_cbor(&session.to_compact_cbor()).unwrap();
    assert_eq!(replay.to_compact_json(), target);
    let point = replay.resolved().resolve_qualified("Position").unwrap();
    let mut edit = replay.edit();
    edit.rename(point, "Point");
    edit.commit().unwrap();
    assert!(replay.warnings().is_empty(), "{:?}", replay.warnings());
    let constructors = replay
        .to_compact_json()
        .as_array()
        .unwrap()
        .iter()
        .filter(|row| row["@type"] == "ConstructorExpression")
        .count();
    assert_eq!(constructors, 1);
    validate_graph_format(&replay.to_compact_json(), GraphFormat::CanonicalV3).unwrap();
}
#[test]
fn canonical_payload_keeps_foreign_explicit_ids_and_legacy_stays_default() {
    let s = session();
    let original = s.to_compact_json();
    let mut document = original.clone();
    let root = document[0]["@id"].as_str().unwrap().to_owned();
    let foreign = "00000000-0000-4000-8000-000000000077";
    document = serde_json::from_str(
        &serde_json::to_string(&document)
            .unwrap()
            .replace(&root, foreign),
    )
    .unwrap();
    let replay = Session::from_interchange_json_with_graph_format(
        &document,
        None,
        &["p.sysml".into()],
        Indent::default(),
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    assert!(replay.warnings().is_empty(), "{:?}", replay.warnings());
    assert_eq!(replay.to_compact_json(), document);
    let bytes = replay.to_compact_cbor();
    assert_eq!(sysmlv2_cbor::from_compact_cbor(&bytes).unwrap(), document);
    assert!(replay.to_compact_cbor_elided().is_err());
    assert_eq!(
        Session::from_compact_cbor(&bytes)
            .unwrap()
            .to_compact_json(),
        document
    );
    let legacy = Session::from_sources(vec![(
        "p.sysml".into(),
        "package P { attribute x = if true ? 7 else 1/0; }".into(),
    )])
    .unwrap();
    assert_eq!(legacy.model().graph_format(), GraphFormat::LegacyV2);
    assert_eq!(
        sysmlv2_cbor::describe(&legacy.to_compact_cbor()).unwrap()["versions"]["scheme"],
        2
    );
}

#[test]
fn canonical_conditional_references_keep_bindings_through_full_replay_and_rename() {
    let sources = vec![("defs.sysml".into(),"package Defs { attribute n = 7; }".into()),("uses.sysml".into(),"package Uses { attribute a = if true ? Defs::n else 1/0; attribute b = null ?? Defs::n; attribute c = false or (Defs::n == 7); }".into())];
    let mut s =
        Session::from_sources_with_graph_format(sources, None, GraphFormat::CanonicalV3).unwrap();
    let check = |s: &mut Session| {
        assert_eq!(
            s.resolved().evaluate_qualified("Uses::a"),
            Ok(Value::Integer(7))
        );
        assert_eq!(
            s.resolved().evaluate_qualified("Uses::b"),
            Ok(Value::Integer(7))
        );
        assert_eq!(
            s.resolved().evaluate_qualified("Uses::c"),
            Ok(Value::Boolean(true))
        );
    };
    check(&mut s);
    let mut replay = Session::from_interchange_json_with_graph_format(
        &s.to_full_json(),
        None,
        &["defs.sysml".into(), "uses.sysml".into()],
        Indent::default(),
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    assert!(replay.warnings().is_empty(), "{:?}", replay.warnings());
    check(&mut replay);
    let n = replay.resolved().resolve_qualified("Defs::n").unwrap();
    let mut edit = replay.edit();
    edit.rename(n, "renamed");
    edit.commit().unwrap();
    check(&mut replay);
}

#[test]
fn canonical_library_reference_identity_survives_nested_wrappers_and_full_replay() {
    let lib = Library::sources(vec![("library.kerml".into(), "standard library package L { datatype Scalar; function Anonymous { return : Scalar; } feature visible; }".into())]);
    let mut s = Session::from_sources_with_graph_format(
        vec![(
            "p.kerml".into(),
            "package P { feature x = if true ? (null ?? L::visible) else L::visible; }".into(),
        )],
        Some(lib.clone()),
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    let r = s.resolved();
    let owner = r.resolve_qualified("L::Anonymous").unwrap();
    let elements: Vec<_> = r.elements().collect();
    let target = elements
        .into_iter()
        .find(|&e| {
            r.element_type(e) == "Feature"
                && r.element_name(e).is_none()
                && r.owner(e) == Some(owner)
        })
        .unwrap();
    let target_id = r.element_id(target).to_string();
    let visible = r.resolve_qualified("L::visible").unwrap();
    let visible_id = r.element_id(visible).to_string();
    let mut document = s.to_compact_json();
    for row in document.as_array_mut().unwrap() {
        if row["@type"] == "Membership" && row["memberElement"]["@id"] == visible_id {
            row["memberElement"] = serde_json::json!({"@id":target_id});
        }
    }
    let mut loaded = Session::from_interchange_json_with_graph_format(
        &document,
        Some(&lib),
        &["p.kerml".into()],
        Indent::default(),
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    assert!(loaded.warnings().is_empty(), "{:?}", loaded.warnings());
    assert_eq!(loaded.to_compact_json(), document);
    assert!(
        loaded
            .resolved()
            .bound_id_reference_sites()
            .iter()
            .all(|(_, _, id)| id.to_string() == target_id)
    );
    assert_eq!(loaded.resolved().bound_id_reference_sites().len(), 2);
    let full = loaded.to_full_json_with(false);
    let mut replay = Session::from_interchange_json_with_graph_format(
        &full,
        Some(&lib),
        &["p.kerml".into()],
        Indent::default(),
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    assert!(replay.warnings().is_empty(), "{:?}", replay.warnings());
    let p = replay.resolved().resolve_qualified("P").unwrap();
    let mut edit = replay.edit();
    edit.rename(p, "Renamed");
    edit.commit().unwrap();
    assert_eq!(replay.resolved().bound_id_reference_sites().len(), 2);
    assert!(
        replay
            .resolved()
            .bound_id_reference_sites()
            .iter()
            .all(|(_, _, id)| id.to_string() == target_id)
    );
}

#[test]
fn canonical_full_replay_with_standard_library_preserves_values_and_typing() {
    let mut model = sysmlv2_transform::ModelHandle::with_graph_format(GraphFormat::CanonicalV3);
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let lib = Library::Prepared(model.prepare_library().unwrap());
    let sources=vec![("standard.sysml".into(),"package P { attribute x : ScalarValues::Integer = 7; attribute y = if true ? x else 1/0; }".into())];
    let original = Session::from_sources_with_graph_format(
        sources,
        Some(lib.clone()),
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    let mut replay = Session::from_interchange_json_with_graph_format(
        &original.to_full_json(),
        Some(&lib),
        &["standard.sysml".into()],
        Indent::default(),
        GraphFormat::CanonicalV3,
    )
    .unwrap();
    assert!(replay.warnings().is_empty(), "{:?}", replay.warnings());
    assert_eq!(
        replay.resolved().evaluate_qualified("P::y"),
        Ok(Value::Integer(7))
    );
    let before = original.to_compact_json();
    let after = replay.to_compact_json();
    assert_eq!(
        before.as_array().unwrap().len(),
        after.as_array().unwrap().len()
    );
    for (before, after) in before
        .as_array()
        .unwrap()
        .iter()
        .zip(after.as_array().unwrap())
    {
        for (key, value) in before.as_object().unwrap() {
            assert_eq!(value, &after[key], "{key}");
        }
    }
}

#[test]
fn unversioned_json_loading_retains_foreign_graph_recovery() {
    let document = session().to_compact_json();
    let mut recovered =
        Session::from_interchange_json_named(&document, None, &["p.sysml".into()]).unwrap();
    assert_eq!(recovered.model().graph_format(), GraphFormat::LegacyV2);
    assert!(
        recovered
            .warnings()
            .iter()
            .any(|w| w.contains("no structural counterpart")),
        "{:?}",
        recovered.warnings()
    );
    assert_eq!(
        recovered.resolved().evaluate_qualified("P::y"),
        Ok(Value::Integer(7))
    );
    assert!(
        Session::from_interchange_json_with_graph_format(
            &document,
            None,
            &["p.sysml".into()],
            Indent::default(),
            GraphFormat::LegacyV2
        )
        .is_err()
    );
}

#[test]
fn legacy_binary_entry_points_keep_foreign_graph_recovery() {
    let document = session().to_compact_json();
    // Historical generic encoders can carry foreign graphs under scheme 2.
    let bytes = sysmlv2_cbor::to_compact_cbor(&document).unwrap();
    let context = Session::from_sources(Vec::new()).unwrap();
    assert_eq!(context.decode_cbor(&bytes).unwrap(), document);
    let mut replay = Session::from_compact_cbor(&bytes).unwrap();
    assert_eq!(replay.model().graph_format(), GraphFormat::LegacyV2);
    assert!(
        replay
            .warnings()
            .iter()
            .any(|w| w.contains("no structural counterpart"))
    );
    assert_eq!(
        replay.resolved().evaluate_qualified("P::y"),
        Ok(Value::Integer(7))
    );
    let explicit_legacy =
        Session::from_sources_with_graph_format(Vec::new(), None, GraphFormat::LegacyV2).unwrap();
    assert!(explicit_legacy.decode_cbor(&bytes).is_err());
    let delta = context.delta_cbor_from(&document, false).unwrap();
    assert!(
        context
            .apply_delta_cbor_to(&delta, &document, false)
            .is_ok()
    );
    assert!(explicit_legacy.delta_cbor_from(&document, false).is_err());
}
