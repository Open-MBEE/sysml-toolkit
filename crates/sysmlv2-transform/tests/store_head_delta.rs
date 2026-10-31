//! A delta from a graph store's head: both sides in the store's
//! spelling, so an edit ships as its changes only, applies to the
//! store's head, and lands on the digest the store reconstructs —
//! with the model's file layout riding along.

use sysmlv2_cbor::index::{BaseIndex, resolve_strict_delta};
use sysmlv2_transform::Session;

fn session(b: &str) -> Session {
    Session::from_sources(vec![
        ("model/A.sysml".into(), "package A { part def X; }".into()),
        ("B.sysml".into(), b.into()),
    ])
    .unwrap()
}

#[test]
fn an_edit_ships_as_its_changes_against_the_store_head() {
    let head =
        sysmlv2_cbor::graph_normalize(&session("package B { part def Y; }").to_compact_json())
            .unwrap();
    let edited = session("package B { part def Y; part def Z; }");
    let want = sysmlv2_cbor::state_digest(
        &sysmlv2_cbor::graph_normalize(&edited.to_compact_json()).unwrap(),
    )
    .unwrap();

    let delta = edited.delta_cbor_from_store_head(&head, false).unwrap();
    assert!(
        delta.len() * 2 < edited.to_compact_cbor().len(),
        "a one-definition edit ships far less than the snapshot: {} vs {}",
        delta.len(),
        edited.to_compact_cbor().len()
    );

    let resolved = resolve_strict_delta(&delta, &BaseIndex::from_compact(&head).unwrap()).unwrap();
    assert_eq!(
        resolved.result_digest, want,
        "the store reconstructs the declared result"
    );
    let paths: Vec<&str> = resolved.units.iter().map(|(_, p)| p.as_str()).collect();
    assert_eq!(paths, ["model/A.sysml", "B.sysml"]);

    let applied = sysmlv2_cbor::apply_delta_cbor(&delta, &head).unwrap();
    assert_eq!(sysmlv2_cbor::state_digest(&applied).unwrap(), want);

    // Portable deltas apply too; they carry no unit structure.
    let portable = edited.delta_cbor_from_store_head(&head, true).unwrap();
    let applied = sysmlv2_cbor::apply_delta_cbor(&portable, &head).unwrap();
    assert_eq!(sysmlv2_cbor::state_digest(&applied).unwrap(), want);
}
