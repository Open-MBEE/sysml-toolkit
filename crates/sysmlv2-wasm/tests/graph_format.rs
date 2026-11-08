//! The opt-in canonical graph format through the binding: a library
//! prepared under it, a session opened on it, the format read back.
use sysmlv2_wasm::{PreparedLibrary, Session};

fn sources(units: &[(&str, &str)]) -> String {
    serde_json::to_string(
        &units
            .iter()
            .map(|(name, text)| serde_json::json!({"name":name,"text":text}))
            .collect::<Vec<_>>(),
    )
    .unwrap()
}

const LIBRARY: &str = "standard library package Base { abstract classifier Anything; abstract feature things : Anything[*] nonunique; }";
const CONDITIONAL: &str =
    "package Cond { class C { feature ready; feature hot; feature ok = ready and not hot; } }";

/// The metaclass of each operand's value of the conditional `and`.
fn operand_kinds(session: &mut Session) -> Vec<String> {
    let json: serde_json::Value = serde_json::from_str(&session.to_compact_json()).unwrap();
    let elements = json.as_array().unwrap().clone();
    let by_id = |id: &serde_json::Value| {
        elements
            .iter()
            .find(|e| &e["@id"] == id)
            .unwrap_or_else(|| panic!("element {id}"))
            .clone()
    };
    let and = elements
        .iter()
        .find(|e| e["@type"] == "OperatorExpression" && e["operator"] == "and")
        .expect("the conditional and");
    and["ownedRelationship"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| by_id(&r["@id"]))
        .filter(|m| m["@type"] == "ParameterMembership")
        .map(|m| {
            let parameter = by_id(&m["ownedRelatedElement"][0]["@id"]);
            let value = parameter["ownedRelationship"]
                .as_array()
                .unwrap()
                .iter()
                .map(|r| by_id(&r["@id"]))
                .find(|r| r["@type"] == "FeatureValue")
                .expect("the parameter's value");
            by_id(&value["ownedRelatedElement"][0]["@id"])["@type"]
                .as_str()
                .unwrap()
                .to_string()
        })
        .collect()
}

#[test]
fn a_session_opens_under_the_selected_graph_format() {
    let users = sources(&[("cond.kerml", CONDITIONAL)]);
    let mut legacy = Session::from_sources(&users).unwrap();
    assert_eq!(legacy.graph_format(), "legacy");
    assert_eq!(
        operand_kinds(&mut legacy),
        ["FeatureReferenceExpression", "OperatorExpression"]
    );
    let mut canonical =
        Session::from_sources_with_graph_format(&users, None, None, Some("canonical".into()))
            .unwrap();
    assert_eq!(canonical.graph_format(), "canonical");
    assert_eq!(
        operand_kinds(&mut canonical),
        ["FeatureReferenceExpression", "FeatureReferenceExpression"]
    );
    // The default and the empty name are the legacy format.
    for name in [None, Some(String::new()), Some("legacy".into())] {
        let session = Session::from_sources_with_graph_format(&users, None, None, name).unwrap();
        assert_eq!(session.graph_format(), "legacy");
    }
    let unknown = Session::from_sources_with_graph_format(&users, None, None, Some("v4".into()));
    assert!(unknown.is_err_and(|error| error.contains("canonical")));
}

#[test]
fn a_prepared_library_carries_its_graph_format_to_its_sessions() {
    let library = sources(&[("base.kerml", LIBRARY)]);
    let users = sources(&[("cond.kerml", CONDITIONAL)]);
    let legacy = PreparedLibrary::new(&library, None).unwrap();
    assert_eq!(legacy.graph_format(), "legacy");
    let mut on_legacy = Session::from_sources_with_prepared_library(&users, &legacy).unwrap();
    assert_eq!(on_legacy.graph_format(), "legacy");
    assert_eq!(
        operand_kinds(&mut on_legacy),
        ["FeatureReferenceExpression", "OperatorExpression"]
    );
    let canonical =
        PreparedLibrary::with_graph_format(&library, None, Some("canonical".into())).unwrap();
    assert_eq!(canonical.graph_format(), "canonical");
    let mut on_canonical = Session::from_sources_with_prepared_library(&users, &canonical).unwrap();
    assert_eq!(on_canonical.graph_format(), "canonical");
    assert_eq!(
        operand_kinds(&mut on_canonical),
        ["FeatureReferenceExpression", "FeatureReferenceExpression"]
    );
    // The same library in each format resolves the same names.
    assert_eq!(on_legacy.check(), on_canonical.check());
    assert!(PreparedLibrary::with_graph_format(&library, None, Some("v4".into())).is_err());
}

/// A prepared snapshot decodes under the format it was written in, and a
/// decode under the other format says which format the snapshot carries.
#[test]
fn a_snapshot_decodes_under_its_own_graph_format() {
    let units: Vec<(String, String)> = vec![("base.kerml".to_string(), LIBRARY.to_string())];
    let library = sources(&[("base.kerml", LIBRARY)]);
    let users = sources(&[("cond.kerml", CONDITIONAL)]);
    let key =
        sysmlv2_model::libcache::hash_units(units.iter().map(|(n, t)| (n.as_str(), t.as_str())));
    let snapshot = |format| match sysmlv2_transform::Library::prepared_sources_with_format(
        units.clone(),
        None,
        format,
    )
    .unwrap()
    {
        sysmlv2_transform::Library::Prepared(prepared) => prepared.to_bytes(key).unwrap(),
        _ => unreachable!(),
    };
    let legacy = snapshot(sysmlv2_transform::GraphFormat::LegacyV2);
    let canonical = snapshot(sysmlv2_transform::GraphFormat::CanonicalV3);
    let decoded = PreparedLibrary::from_snapshot_with_graph_format(
        canonical.clone(),
        &library,
        None,
        Some("canonical".into()),
        None,
    )
    .unwrap();
    assert_eq!(decoded.graph_format(), "canonical");
    let on_decoded = Session::from_sources_with_prepared_library(&users, &decoded).unwrap();
    assert_eq!(on_decoded.graph_format(), "canonical");
    let prepared =
        PreparedLibrary::with_graph_format(&library, None, Some("canonical".into())).unwrap();
    let on_prepared = Session::from_sources_with_prepared_library(&users, &prepared).unwrap();
    assert_eq!(on_decoded.to_compact_json(), on_prepared.to_compact_json());
    // The default decoders read legacy snapshots; a mismatch names the formats.
    let refused = PreparedLibrary::from_snapshot(canonical, &library, None, None);
    assert!(refused.is_err_and(|e| e.contains("canonical graph format") && e.contains("legacy")));
    let refused = PreparedLibrary::from_snapshot_with_graph_format(
        legacy.clone(),
        &library,
        None,
        Some("canonical".into()),
        None,
    );
    assert!(refused.is_err_and(|e| e.contains("legacy graph format") && e.contains("canonical")));
    assert_eq!(
        PreparedLibrary::from_snapshot_with_graph_format(legacy, &library, None, None, None)
            .unwrap()
            .graph_format(),
        "legacy"
    );
}
