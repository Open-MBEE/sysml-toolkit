//! A push between two graph stores: the delta from the receiver's head
//! to the sender's state, both as the stores serve them (s2c
//! snapshots), applies to the receiver's head and lands on the
//! sender's content with its file layout.

use sysmlv2_cbor::index::{BaseIndex, resolve_strict_delta};
use sysmlv2_transform::Session;

fn served(b: &str, b_name: &str) -> Vec<u8> {
    Session::from_sources(vec![
        ("model/A.sysml".into(), "package A { part def X; }".into()),
        (b_name.into(), b.into()),
    ])
    .unwrap()
    .to_compact_cbor()
}

fn normalized(bytes: &[u8]) -> serde_json::Value {
    sysmlv2_cbor::graph_normalize(&sysmlv2_cbor::from_compact_cbor(bytes).unwrap()).unwrap()
}

#[test]
fn a_push_ships_the_changes_and_the_file_layout() {
    let remote = served("package B { part def Y; }", "B.sysml");
    let local = served("package B { part def Y; part def Z; }", "B.sysml");
    let pushed = sysmlv2_cbor::store_delta_cbor(&remote, &local).unwrap();
    assert_eq!(pushed.fallback, None);
    let delta = pushed.bytes;
    assert!(
        delta.len() * 2 < local.len(),
        "{} vs {}",
        delta.len(),
        local.len()
    );

    let base = normalized(&remote);
    let resolved = resolve_strict_delta(&delta, &BaseIndex::from_compact(&base).unwrap()).unwrap();
    let paths: Vec<&str> = resolved.units.iter().map(|(_, p)| p.as_str()).collect();
    assert_eq!(paths, ["model/A.sysml", "B.sysml"]);
    let applied = sysmlv2_cbor::apply_delta_cbor(&delta, &base).unwrap();
    assert_eq!(
        sysmlv2_cbor::state_digest(&applied).unwrap(),
        resolved.result_digest
    );
    // The digest the receiver reports for its new head, in its spelling.
    assert_eq!(
        pushed.result_digest,
        sysmlv2_cbor::state_digest(&sysmlv2_cbor::graph_normalize(&applied).unwrap()).unwrap()
    );
    let names = |v: &serde_json::Value| -> Vec<String> {
        let mut n: Vec<String> = v
            .as_array()
            .unwrap()
            .iter()
            .filter_map(|e| e["declaredName"].as_str().map(str::to_owned))
            .collect();
        n.sort();
        n
    };
    assert_eq!(names(&applied), names(&normalized(&local)));
}

#[test]
fn independently_derived_ids_diff_by_structure() {
    // the same content under another file name derives other ids; the
    // rebase pairs them, so only the real change ships
    let remote = served("package B { part def Y; }", "B.sysml");
    let renamed = served("package B { part def Y; part def Z; }", "other/B2.sysml");
    let delta = sysmlv2_cbor::store_delta_cbor(&remote, &renamed)
        .unwrap()
        .bytes;
    let from_same = sysmlv2_cbor::store_delta_cbor(
        &remote,
        &served("package B { part def Y; part def Z; }", "B.sysml"),
    )
    .unwrap()
    .bytes;
    assert!(
        delta.len() < from_same.len() * 3,
        "rebased delta {} vs same-name delta {}",
        delta.len(),
        from_same.len()
    );
    let base = normalized(&remote);
    let resolved = resolve_strict_delta(&delta, &BaseIndex::from_compact(&base).unwrap()).unwrap();
    assert!(resolved.units.iter().any(|(_, p)| p == "other/B2.sysml"));
}

/// Two elements under one root namespace, `X` and `Q`, by the ids given;
/// each one's membership takes its id with the first group replaced.
fn snapshot(root: &str, x: &str, q: Option<&str>) -> Vec<u8> {
    let membership = |el: &str| format!("11111111{}", &el[8..]);
    let member = |m: &str, el: &str, name: &str| {
        [
            serde_json::json!({"@id":m,"@type":"OwningMembership",
                "owningRelatedElement":{"@id":root},"ownedRelatedElement":[{"@id":el}]}),
            serde_json::json!({"@id":el,"@type":"PartDefinition","declaredName":name,
                "owningRelationship":{"@id":m}}),
        ]
    };
    let mut memberships = vec![serde_json::json!({"@id": membership(x)})];
    let mut rows = member(&membership(x), x, "X").to_vec();
    if let Some(q) = q {
        memberships.push(serde_json::json!({"@id": membership(q)}));
        rows.extend(member(&membership(q), q, "Q"));
    }
    rows.insert(
        0,
        serde_json::json!({"@id":root,"@type":"Namespace","ownedRelationship":memberships}),
    );
    sysmlv2_cbor::to_compact_cbor(&serde_json::Value::Array(rows)).unwrap()
}

#[test]
fn a_rebase_that_collides_falls_back_to_the_targets_own_ids() {
    // The target's `X` pairs with the base's by path and would take the
    // base's id, which the target's `Q` already holds: the rebase
    // refuses, and the delta keeps the target's ids, applied and checked.
    let base = snapshot(
        "00000000-0000-4000-8000-000000000001",
        "00000000-0000-4000-8000-0000000000aa",
        None,
    );
    let target = snapshot(
        "00000000-0000-4000-8000-000000000002",
        "00000000-0000-4000-8000-0000000000bb",
        Some("00000000-0000-4000-8000-0000000000aa"),
    );
    let pushed = sysmlv2_cbor::store_delta_cbor(&base, &target).unwrap();
    let why = pushed.fallback.expect("the rebase collides");
    assert!(why.contains("collides"), "{why}");
    let applied = sysmlv2_cbor::apply_delta_cbor(&pushed.bytes, &normalized(&base)).unwrap();
    let applied = sysmlv2_cbor::graph_normalize(&applied).unwrap();
    assert_eq!(applied, normalized(&target));
    assert_eq!(
        pushed.result_digest,
        sysmlv2_cbor::state_digest(&applied).unwrap()
    );
}

#[test]
fn states_in_different_graph_formats_are_refused() {
    let sources = || {
        vec![(
            "B.sysml".to_string(),
            "package B { part def Y; }".to_string(),
        )]
    };
    let legacy = Session::from_sources(sources()).unwrap().to_compact_cbor();
    let canonical = Session::from_sources_with_graph_format(
        sources(),
        None,
        sysmlv2_transform::GraphFormat::CanonicalV3,
    )
    .unwrap()
    .to_compact_cbor();
    let refused = sysmlv2_cbor::store_delta_cbor(&legacy, &canonical).unwrap_err();
    assert!(refused.to_string().contains("graph-format 2"), "{refused}");
    // An empty base (a new branch) a format-unaware encoder stamped
    // legacy takes the target's format.
    let empty = sysmlv2_cbor::to_compact_cbor(&serde_json::json!([])).unwrap();
    let first = sysmlv2_cbor::store_delta_cbor(&empty, &canonical).unwrap();
    assert_eq!(
        sysmlv2_cbor::graph_format(&first.bytes).unwrap(),
        sysmlv2_transform::GraphFormat::CanonicalV3
    );
    // Within one format the delta is encoded in it.
    let same = sysmlv2_cbor::store_delta_cbor(&canonical, &canonical).unwrap();
    assert_eq!(
        sysmlv2_cbor::graph_format(&same.bytes).unwrap(),
        sysmlv2_transform::GraphFormat::CanonicalV3
    );
}
