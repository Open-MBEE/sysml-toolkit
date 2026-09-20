//! Delta gates: delta computation + verified apply. apply(delta(a,b), a)
//! reproduces delta-canonical(b) exactly in both identity modes;
//! canonicalization is emission-order-independent; the base digest
//! gates strict deltas hard and portable divergence yields the
//! documented report; the empty base is a recognizable constant.

use serde_json::Value;
use std::fmt::Write as _;
use sysmlv2_cbor::{
    DeltaOptions, apply_delta_cbor, apply_delta_cbor_lenient, delta_canonical, delta_compact_cbor,
    empty_base_digest, rebase_ids, state_digest,
};
use sysmlv2_parser::json::model_to_compact_json;
use sysmlv2_parser::model::Model;

fn compact_of(sources: &[(&str, &str)]) -> Value {
    let mut model = Model::new();
    for (name, text) in sources {
        model.add_source(name.to_string(), text);
    }
    model_to_compact_json(&model)
}

const BASE_UNIT: &str = "package P {
    part def V { attribute total; }
    part v : V;
    part def W;
}";

/// The edit: rename an attribute (update subtree), delete `W`, add a
/// new definition (creates).
const TARGET_UNIT: &str = "package P {
    part def V { attribute renamed; }
    part v : V;
    part def N { attribute x; }
}";

fn opts(portable: bool) -> DeltaOptions {
    DeltaOptions::new().with_portable(portable)
}

#[test]
fn apply_reproduces_canonical_target_in_both_modes() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    let want = delta_canonical(&target).unwrap();
    for portable in [false, true] {
        let bytes = delta_compact_cbor(&base, &target, &opts(portable)).unwrap();
        let got =
            apply_delta_cbor(&bytes, &base).unwrap_or_else(|e| panic!("portable={portable}: {e}"));
        assert_eq!(got, want, "portable={portable}");
        // A strict delta is smaller than the full target payload even
        // for this fixture, whose rename churns most of a tiny model;
        // portable pays 17 bytes of id-keyed identity per change, so
        // only real-model proportions keep it under the snapshot.
        let full = sysmlv2_cbor::to_compact_cbor(&target).unwrap();
        if !portable {
            assert!(bytes.len() < full.len(), "strict delta under snapshot");
        }
    }
}

#[test]
fn canonicalization_is_emission_order_independent() {
    let compact = compact_of(&[("m.sysml", BASE_UNIT)]);
    let mut shuffled = compact.as_array().unwrap().clone();
    shuffled.reverse();
    let shuffled = Value::Array(shuffled);
    assert_eq!(
        delta_canonical(&compact).unwrap(),
        delta_canonical(&shuffled).unwrap(),
        "canonical order survives element-array shuffling"
    );
    assert_eq!(
        state_digest(&compact).unwrap(),
        state_digest(&shuffled).unwrap(),
        "state digests are order-independent"
    );
    // No changes between the two orders: the delta is empty and tiny.
    let bytes = delta_compact_cbor(&compact, &shuffled, &opts(false)).unwrap();
    assert!(
        bytes.len() < 64,
        "empty delta stays small ({} bytes)",
        bytes.len()
    );
    assert_eq!(
        apply_delta_cbor(&bytes, &compact).unwrap(),
        delta_canonical(&compact).unwrap()
    );
}

/// The canonical order is computed once, as a permutation, and then
/// either borrowed (digests, diffs) or moved through (apply). All three
/// must land on the identical array — including for a payload with
/// several roots, unreachable elements, and a shuffled emission order,
/// where the walk falls back to appending what it never visited.
#[test]
fn borrowed_and_applied_canonicalization_agree_on_a_ragged_payload() {
    let id = |n: u8| format!("00000000-0000-4000-8000-0000000000{n:02x}");
    let pkg = |n: u8, owned: &[u8]| {
        serde_json::json!({
            "@type": "Package", "@id": id(n),
            "ownedRelationship": owned.iter().map(|&t| serde_json::json!({ "@id": id(t) }))
                .collect::<Vec<_>>(),
        })
    };
    let membership = |n: u8, member: u8| {
        serde_json::json!({
            "@type": "OwningMembership", "@id": id(n),
            "ownedRelatedElement": [{ "@id": id(member) }],
            "memberElement": { "@id": id(member) },
        })
    };
    // Two owning roots plus two elements nothing owns at all.
    let model = Value::Array(vec![
        pkg(1, &[3]),
        pkg(2, &[5]),
        membership(3, 4),
        pkg(4, &[]),
        membership(5, 6),
        pkg(6, &[]),
        pkg(7, &[]),
        pkg(8, &[]),
    ]);
    // The same payload with the owned elements emitted elsewhere; the
    // roots keep their relative order, which is the one thing the
    // canonical walk takes from emission order.
    let shuffled = Value::Array(vec![
        pkg(1, &[3]),
        membership(5, 6),
        pkg(2, &[5]),
        pkg(6, &[]),
        membership(3, 4),
        pkg(4, &[]),
        pkg(7, &[]),
        pkg(8, &[]),
    ]);
    let ids_of = |v: &Value| -> Vec<String> {
        v.as_array()
            .unwrap()
            .iter()
            .map(|e| e["@id"].as_str().unwrap().to_owned())
            .collect()
    };
    let want = delta_canonical(&model).unwrap();
    assert_eq!(
        ids_of(&want),
        [1, 3, 4, 2, 5, 6, 7, 8].map(id).to_vec(),
        "ownership preorder from each root, then what nothing owns"
    );
    assert_eq!(delta_canonical(&shuffled).unwrap(), want);
    assert_eq!(
        state_digest(&model).unwrap(),
        state_digest(&shuffled).unwrap()
    );
    // The applied state canonicalizes through the owned path.
    let empty = Value::Array(Vec::new());
    for portable in [false, true] {
        let bytes = delta_compact_cbor(&empty, &model, &opts(portable)).unwrap();
        assert_eq!(
            apply_delta_cbor(&bytes, &empty).unwrap(),
            want,
            "portable={portable}"
        );
    }
}

#[test]
fn strict_refuses_a_divergent_base_hard() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    let other = compact_of(&[("m.sysml", "package Q { part def Z; }")]);
    let strict = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
    let err = apply_delta_cbor(&strict, &other).unwrap_err().to_string();
    assert!(err.contains("base digest"), "{err}");
    // Lenient application of a strict delta is refused outright.
    let err = apply_delta_cbor_lenient(&strict, &other)
        .unwrap_err()
        .to_string();
    assert!(err.contains("strict-identity"), "{err}");
}

#[test]
fn portable_diverged_apply_reports_noops_and_upserts() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    // The rename travels as create+delete (the attribute's id derives
    // from its name), so the update that exercises upserting is the
    // new member under `v` — `v` itself is updated, and the divergent
    // base below lacks `v` entirely.
    let target = compact_of(&[(
        "m.sysml",
        "package P {
        part def V { attribute renamed; }
        part v : V { attribute z; }
        part def N { attribute x; }
    }",
    )]);
    let bytes = delta_compact_cbor(&base, &target, &opts(true)).unwrap();

    // Divergent base: `W` (the delete target) is already gone, the
    // attribute subtree under V is missing, and so is `v` (the update
    // target — its update upserts).
    let diverged = compact_of(&[(
        "m.sysml",
        "package P {
        part def V;
    }",
    )]);
    let (result, report) = apply_delta_cbor_lenient(&bytes, &diverged).unwrap();
    assert!(!report.base_matched);
    assert!(report.noop_deletes >= 1, "{report:?}");
    assert!(report.upserted_updates >= 1, "{report:?}");
    // Same-named elements carry the same graph-derived ids, so the
    // update to `V`'s membership landed on the corresponding element.
    let names: Vec<&str> = result
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|e| e["declaredName"].as_str())
        .collect();
    assert!(
        names.contains(&"N"),
        "created definition arrived: {names:?}"
    );
    assert!(
        names.contains(&"renamed"),
        "cherry-picked rename landed: {names:?}"
    );

    // Matching base: clean apply, zeroed report.
    let (result, report) = apply_delta_cbor_lenient(&bytes, &base).unwrap();
    assert!(report.base_matched);
    assert_eq!(
        (
            report.noop_deletes,
            report.upserted_updates,
            report.replaced_creates
        ),
        (0, 0, 0)
    );
    assert_eq!(result, delta_canonical(&target).unwrap());
}

#[test]
fn empty_base_makes_an_all_creates_delta() {
    let empty = Value::Array(Vec::new());
    let model = compact_of(&[("m.sysml", BASE_UNIT)]);
    assert_eq!(state_digest(&empty).unwrap(), empty_base_digest());
    let bytes = delta_compact_cbor(&empty, &model, &opts(false)).unwrap();
    assert_eq!(
        apply_delta_cbor(&bytes, &empty).unwrap(),
        delta_canonical(&model).unwrap(),
        "first-commit shape: all creates against the empty base"
    );
}

#[test]
fn plain_decoders_point_delta_payloads_at_apply() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    let bytes = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
    let err = sysmlv2_cbor::from_cbor(&bytes).unwrap_err().to_string();
    assert!(err.contains("apply_delta_cbor"), "{err}");
    // And apply refuses non-delta payloads symmetrically.
    let snapshot = sysmlv2_cbor::to_compact_cbor(&base).unwrap();
    let err = apply_delta_cbor(&snapshot, &base).unwrap_err().to_string();
    assert!(
        err.contains("not a delta") || err.contains("array(6)"),
        "{err}"
    );
}

/// Change counts of a delta payload, per `describe`.
fn changes_of(bytes: &[u8]) -> (u64, u64, u64) {
    let d = sysmlv2_cbor::describe(bytes).unwrap();
    let c = &d["delta"]["changes"];
    (
        c["creates"].as_u64().unwrap(),
        c["updates"].as_u64().unwrap(),
        c["deletes"].as_u64().unwrap(),
    )
}

#[test]
fn rebase_aligns_independently_derived_payloads() {
    // Ids chain from the unit root, which seeds from the unit name —
    // the same text under another name shares *no* ids with the base.
    let base = compact_of(&[("a.sysml", BASE_UNIT)]);
    let renamed = compact_of(&[("b.sysml", BASE_UNIT)]);
    let ids = |v: &Value| -> Vec<String> {
        v.as_array()
            .unwrap()
            .iter()
            .map(|e| e["@id"].as_str().unwrap().to_owned())
            .collect()
    };
    assert!(
        ids(&base).iter().all(|i| !ids(&renamed).contains(i)),
        "premise: independent derivations share no ids"
    );
    // Rebasing adopts the base id at every matching ownership path —
    // an unchanged model rebases to the base payload exactly
    // (`elementId` mirrors included).
    assert_eq!(rebase_ids(&base, &renamed).unwrap(), base);

    // An edited model diffs identically whether or not the derivation
    // was shared; without the rebase this degenerates to full replace.
    let cross = rebase_ids(&base, &compact_of(&[("b.sysml", TARGET_UNIT)])).unwrap();
    let aligned = compact_of(&[("a.sysml", TARGET_UNIT)]);
    for portable in [false, true] {
        let cross_bytes = delta_compact_cbor(&base, &cross, &opts(portable)).unwrap();
        let aligned_bytes = delta_compact_cbor(&base, &aligned, &opts(portable)).unwrap();
        assert_eq!(
            changes_of(&cross_bytes),
            changes_of(&aligned_bytes),
            "portable={portable}: rebased diff is as minimal as the shared-session one"
        );
        assert_eq!(
            apply_delta_cbor(&cross_bytes, &base).unwrap(),
            delta_canonical(&cross).unwrap(),
            "portable={portable}"
        );
    }
}

#[test]
fn rebase_is_identity_on_a_shared_derivation() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    assert_eq!(rebase_ids(&base, &target).unwrap(), target);
}

#[test]
fn rebase_pairs_documents_by_name() {
    // Two documents, reordered and renamed across sessions: roots
    // pair by first member name, so the diff still sees only content.
    let doc_a = "package A { part def D; }";
    let doc_b = "package B { part def E; }";
    let base = compact_of(&[("x.sysml", doc_a), ("y.sysml", doc_b)]);
    let target = compact_of(&[("p.sysml", doc_b), ("q.sysml", doc_a)]);
    let rebased = rebase_ids(&base, &target).unwrap();
    let bytes = delta_compact_cbor(&base, &rebased, &opts(false)).unwrap();
    assert_eq!(
        changes_of(&bytes),
        (0, 0, 0),
        "reordered documents diff empty"
    );
}

#[test]
fn mutated_delta_payloads_never_panic() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    for portable in [false, true] {
        let bytes = delta_compact_cbor(&base, &target, &opts(portable)).unwrap();
        for i in 0..bytes.len() {
            let mut bad = bytes.clone();
            bad[i] ^= 0x01;
            let _ = apply_delta_cbor(&bad, &base);
            let _ = apply_delta_cbor_lenient(&bad, &base);
        }
        for cut in 0..bytes.len() {
            let _ = apply_delta_cbor(&bytes[..cut], &base);
        }
    }
}

// ---- id-elided deltas ----

use sysmlv2_cbor::{apply_delta_cbor_with, delta_compact_cbor_elided};

fn none(_: &str) -> Option<String> {
    None
}

#[test]
fn elided_delta_round_trips_and_drops_created_id_bytes() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    let explicit = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
    let elided = delta_compact_cbor_elided(&base, &target, &opts(false), &none).unwrap();
    // Session-derived created ids all re-derive: the exception map is
    // empty and every created id's 16 bytes leave the wire.
    let d = sysmlv2_cbor::describe(&elided).unwrap();
    assert_eq!(d["delta"]["idsElided"], serde_json::json!(true));
    assert_eq!(d["delta"]["exceptions"], serde_json::json!(0));
    assert!(d["delta"]["createdIds"].as_array().unwrap().is_empty());
    let created = d["delta"]["created"].as_u64().unwrap() as usize;
    assert!(created > 0, "the fixture edit creates elements");
    // 17 bytes per created-table entry leave; the elided section costs
    // ~20 fixed bytes (count + empty map + digest).
    assert!(
        elided.len() + 17 * created <= explicit.len() + 20,
        "elided ({}) drops the created-id table of explicit ({}, {created} creates)",
        elided.len(),
        explicit.len()
    );
    // The applied state is identical to the explicit delta's.
    let want = apply_delta_cbor(&explicit, &base).unwrap();
    let got = apply_delta_cbor_with(&elided, &base, &none).unwrap();
    assert_eq!(got, want);
    assert_eq!(got, delta_canonical(&target).unwrap());
}

#[test]
fn elided_delta_lands_foreign_created_ids_in_exceptions() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    // Give one created element a foreign (underivable) id everywhere.
    let foreign = "11111111-2222-4333-8444-555555555555";
    let old = target
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["declaredName"] == serde_json::json!("N"))
        .and_then(|e| e["@id"].as_str())
        .expect("fixture creates part def N")
        .to_owned();
    let mutated: Value = serde_json::from_str(
        &serde_json::to_string(&target)
            .unwrap()
            .replace(&old, foreign),
    )
    .unwrap();
    let elided = delta_compact_cbor_elided(&base, &mutated, &opts(false), &none).unwrap();
    let d = sysmlv2_cbor::describe(&elided).unwrap();
    // Exceptions are exactly the elements that chain from the foreign
    // payload id: the element itself, its owning membership (named by
    // its member), and its named child (owner-chained) — the
    // divergence stops there, the child's own subtree re-derives.
    assert_eq!(d["delta"]["exceptions"], serde_json::json!(3));
    let got = apply_delta_cbor_with(&elided, &base, &none).unwrap();
    assert_eq!(got, delta_canonical(&mutated).unwrap());
}

#[test]
fn elided_delta_mode_and_resolver_gates() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    let err = delta_compact_cbor_elided(&base, &target, &opts(true), &none)
        .unwrap_err()
        .to_string();
    assert!(err.contains("strict deltas only"), "{err}");
    let elided = delta_compact_cbor_elided(&base, &target, &opts(false), &none).unwrap();
    let err = apply_delta_cbor(&elided, &base).unwrap_err().to_string();
    assert!(err.contains("apply_delta_cbor_with"), "{err}");
    let err = apply_delta_cbor_lenient(&elided, &base)
        .unwrap_err()
        .to_string();
    assert!(err.contains("strict"), "{err}");
}

#[test]
fn elided_delta_tampering_fails_a_digest_hard() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    let bytes = delta_compact_cbor_elided(&base, &target, &opts(false), &none).unwrap();
    // Every single-byte mutation must die cleanly (malformed, digest,
    // or refused header — never a panic, never silent acceptance of a
    // divergent state); some mutation must reach each digest guard.
    let (mut id_digest_failures, mut ok) = (0usize, 0usize);
    for i in 0..bytes.len() {
        let mut bad = bytes.clone();
        bad[i] ^= 0x01;
        match apply_delta_cbor_with(&bad, &base, &none) {
            Err(e) if e.to_string().contains("recovered created ids") => {
                id_digest_failures += 1;
            }
            Err(_) => {}
            Ok(v) => {
                // A mutation that still applies must be a no-op flip
                // landing on the identical state.
                assert_eq!(v, delta_canonical(&target).unwrap());
                ok += 1;
            }
        }
    }
    assert!(
        id_digest_failures > 0,
        "some mutation reached the created-id digest"
    );
    assert_eq!(ok, 0, "no mutation silently applied");
}

#[test]
fn mid_body_insertion_disturbs_no_named_sibling() {
    // The id scheme's edit-stability gate: named members and their
    // memberships chain past the membership ordinal, so inserting a
    // member mid-body re-derives nothing that follows it — the delta
    // is exactly the insertion (creates + the owner update), the same
    // shape as appending at the end of the body.
    let base = compact_of(&[(
        "m.sysml",
        "package P {
            part def V { attribute a; attribute b; }
            part f : V;
            part r : V;
            part def W;
        }",
    )]);
    let target = compact_of(&[(
        "m.sysml",
        "package P {
            part def V { attribute a; attribute b; }
            attribute q;
            part f : V;
            part r : V;
            part def W;
        }",
    )]);
    let bytes = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
    let d = sysmlv2_cbor::describe(&bytes).unwrap();
    assert_eq!(
        d["delta"]["changes"],
        serde_json::json!({ "creates": 2, "deletes": 0, "updates": 1 }),
        "the delta is the inserted member + its membership + the owner"
    );
    assert!(
        bytes.len() < 200,
        "insertion-sized delta stays small ({})",
        bytes.len()
    );
    assert_eq!(
        apply_delta_cbor(&bytes, &base).unwrap(),
        delta_canonical(&target).unwrap()
    );
}

// ---- field-patch update records ----

#[test]
fn patched_updates_make_big_owner_inserts_constant_size() {
    // The dominant real edit: one member inserted into a big package.
    // Whole-element updates re-ship the owner's entire relationship
    // list (O(members)); a splice patch is O(1) — the delta for a
    // 60-member owner stays within a few bytes of the 6-member one.
    let body = |n: usize, extra: bool| {
        let mut s = String::from("package P {\n");
        for k in 0..n {
            writeln!(s, "    part def D{k};").unwrap();
        }
        if extra {
            s.push_str("    attribute q;\n");
        }
        s.push_str("}\n");
        s
    };
    let size_of = |n: usize| {
        let base = compact_of(&[("m.sysml", &body(n, false))]);
        let target = compact_of(&[("m.sysml", &body(n, true))]);
        let bytes = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
        let d = sysmlv2_cbor::describe(&bytes).unwrap();
        assert_eq!(d["delta"]["patchedUpdates"], serde_json::json!(1), "n={n}");
        assert_eq!(
            apply_delta_cbor(&bytes, &base).unwrap(),
            delta_canonical(&target).unwrap(),
            "n={n}"
        );
        bytes.len()
    };
    let (small, big) = (size_of(6), size_of(60));
    // The only size growth allowed is index-width noise (the owner's
    // splice references later positions), not the member count.
    assert!(
        big <= small + 8,
        "append into a 60-member owner ({big} B) stays within bytes of a \
         6-member one ({small} B)"
    );
}

#[test]
fn patch_ops_cover_set_unset_and_splice() {
    // set: a literal value changes in place (same positional identity);
    // unset: a declared short name disappears (the key leaves the
    // element); splice: the owner's member list gains an entry.
    let base = compact_of(&[(
        "m.sysml",
        "package P {\n    attribute <t> total = 2;\n    part def V;\n}",
    )]);
    let target = compact_of(&[(
        "m.sysml",
        "package P {\n    attribute total = 3;\n    part def V;\n    part def W;\n}",
    )]);
    let bytes = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
    let d = sysmlv2_cbor::describe(&bytes).unwrap();
    assert!(
        d["delta"]["patchedUpdates"].as_u64().unwrap() >= 2,
        "value set + short-name unset + owner splice ride patches: {}",
        d["delta"]
    );
    assert_eq!(
        apply_delta_cbor(&bytes, &base).unwrap(),
        delta_canonical(&target).unwrap()
    );
}

#[test]
fn portable_deltas_carry_no_patches() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    let bytes = delta_compact_cbor(&base, &target, &opts(true)).unwrap();
    let d = sysmlv2_cbor::describe(&bytes).unwrap();
    assert_eq!(d["delta"]["patchedUpdates"], serde_json::json!(0));
    // And the applied state matches the strict (patched) delta's.
    let strict = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
    assert_eq!(
        apply_delta_cbor(&bytes, &base).unwrap(),
        apply_delta_cbor(&strict, &base).unwrap()
    );
}

#[test]
fn patched_elided_deltas_compose() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    let bytes = delta_compact_cbor_elided(&base, &target, &opts(false), &none).unwrap();
    let d = sysmlv2_cbor::describe(&bytes).unwrap();
    assert_eq!(d["delta"]["idsElided"], serde_json::json!(true));
    assert!(
        d["delta"]["patchedUpdates"].as_u64().unwrap() >= 1,
        "{}",
        d["delta"]
    );
    assert_eq!(
        apply_delta_cbor_with(&bytes, &base, &none).unwrap(),
        delta_canonical(&target).unwrap()
    );
}

#[test]
fn mutated_patched_delta_payloads_never_panic() {
    let base = compact_of(&[("m.sysml", BASE_UNIT)]);
    let target = compact_of(&[("m.sysml", TARGET_UNIT)]);
    let bytes = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
    let patched = sysmlv2_cbor::describe(&bytes).unwrap()["delta"]["patchedUpdates"]
        .as_u64()
        .unwrap();
    assert!(
        patched >= 1,
        "premise: the fixture exercises the patch reader"
    );
    for i in 0..bytes.len() {
        let mut bad = bytes.clone();
        bad[i] ^= 0x01;
        // A surviving flip must land on the identical state (the
        // result digest gates everything else).
        if let Ok(v) = apply_delta_cbor(&bad, &base) {
            assert_eq!(v, delta_canonical(&target).unwrap());
        }
    }
    for cut in 0..bytes.len() {
        let _ = apply_delta_cbor(&bytes[..cut], &base);
    }
}

// ---- unit structure rides the delta wire ----

fn compact_with_units(sources: &[(&str, &str)]) -> (Value, Vec<(usize, String)>) {
    let mut model = Model::new();
    for (name, text) in sources {
        model.add_source(name.to_string(), text);
    }
    sysmlv2_parser::json::model_to_compact_json_with_units(&model)
}

const UNIT_A: &str = "package P { part def V; part v : V; }";
const UNIT_A2: &str = "package P { part def V { attribute m; } part v : V; }";
const UNIT_B: &str = "package Q { part def W; }";
const UNIT_C: &str = "package R { part def X; }";

/// File add + rename + delete all travel with the delta: the report's
/// units name exactly the target's files, and each index lands on the
/// element that was that unit's root in the target.
#[test]
fn units_ride_the_delta_and_apply_returns_them() {
    let (base, _) = compact_with_units(&[("a.sysml", UNIT_A), ("b.sysml", UNIT_B)]);
    let (target, target_units) = compact_with_units(&[("a2.sysml", UNIT_A2), ("c.sysml", UNIT_C)]);
    // Independently derived payloads — rebase like every cross-session
    // encoder does; element order is preserved, indices stay valid.
    let target = rebase_ids(&base, &target).unwrap();
    let bytes = delta_compact_cbor(
        &base,
        &target,
        &DeltaOptions::new().with_units(target_units.clone()),
    )
    .unwrap();
    let (got, report) = sysmlv2_cbor::apply_delta_cbor_report(&bytes, &base).unwrap();
    assert_eq!(got, delta_canonical(&target).unwrap());
    let arr = got.as_array().unwrap();
    assert_eq!(report.units.len(), target_units.len());
    for (idx, path) in &report.units {
        let (orig_idx, _) = target_units
            .iter()
            .find(|(_, p)| p == path)
            .unwrap_or_else(|| panic!("unexpected unit path `{path}`"));
        assert_eq!(
            arr[*idx]["@id"],
            target.as_array().unwrap()[*orig_idx]["@id"],
            "unit `{path}` root survives at the reported result index"
        );
    }
    // Unit-less payloads keep the old shape and an empty report field.
    let plain = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
    let (_, r2) = sysmlv2_cbor::apply_delta_cbor_report(&plain, &base).unwrap();
    assert!(r2.units.is_empty());
    assert!(
        plain.len() < bytes.len(),
        "units section costs bytes only when carried"
    );
}

/// A rename-only change is a legal delta: empty change list, new
/// units, base digest == result digest.
#[test]
fn rename_only_change_is_a_legal_delta() {
    let (base, _) = compact_with_units(&[("old.sysml", UNIT_A)]);
    let (target, target_units) = compact_with_units(&[("renamed.sysml", UNIT_A)]);
    let target = rebase_ids(&base, &target).unwrap();
    assert_eq!(
        base, target,
        "identical content rebases to identical elements"
    );
    let bytes = delta_compact_cbor(
        &base,
        &target,
        &DeltaOptions::new().with_units(target_units),
    )
    .unwrap();
    let d = sysmlv2_cbor::describe(&bytes).unwrap();
    assert_eq!(
        d["delta"]["changes"],
        serde_json::json!({
            "creates": 0, "updates": 0, "deletes": 0
        })
    );
    assert_eq!(d["delta"]["units"][0]["path"], "renamed.sysml");
    assert_eq!(d["delta"]["baseDigest"], d["delta"]["resultDigest"]);
    let (got, report) = sysmlv2_cbor::apply_delta_cbor_report(&bytes, &base).unwrap();
    assert_eq!(got, delta_canonical(&base).unwrap());
    assert_eq!(report.units.len(), 1);
    assert_eq!(report.units[0].1, "renamed.sysml");
}

/// Unit paths are strict-only: portable result indices are not exact
/// against a divergent base.
#[test]
fn units_refuse_portable() {
    let (base, _) = compact_with_units(&[("a.sysml", UNIT_A)]);
    let (target, units) = compact_with_units(&[("a.sysml", UNIT_A2)]);
    let target = rebase_ids(&base, &target).unwrap();
    let err = delta_compact_cbor(
        &base,
        &target,
        &DeltaOptions::new().with_portable(true).with_units(units),
    )
    .unwrap_err();
    assert!(err.to_string().contains("strict deltas only"), "{err}");
}

/// Units compose with id elision (the versioning-chain shape): the
/// resolver-less encoder ships exceptions, the applier recovers ids
/// under the digest gate, and the units still come back.
#[test]
fn units_compose_with_elision() {
    let (base, _) = compact_with_units(&[("a.sysml", UNIT_A), ("b.sysml", UNIT_B)]);
    let (target, target_units) = compact_with_units(&[
        ("a.sysml", UNIT_A2),
        ("b.sysml", UNIT_B),
        ("c.sysml", UNIT_C),
    ]);
    let target = rebase_ids(&base, &target).unwrap();
    let bytes = sysmlv2_cbor::delta_compact_cbor_elided(
        &base,
        &target,
        &DeltaOptions::new().with_units(target_units),
        &|_| None,
    )
    .unwrap();
    let (got, report) =
        sysmlv2_cbor::apply_delta_cbor_report_with(&bytes, &base, &|_| None).unwrap();
    assert_eq!(got, delta_canonical(&target).unwrap());
    let paths: Vec<&str> = report.units.iter().map(|(_, p)| p.as_str()).collect();
    assert_eq!(paths, ["a.sysml", "b.sysml", "c.sysml"]);
    let d = sysmlv2_cbor::describe(&bytes).unwrap();
    assert_eq!(d["delta"]["idsElided"], true);
    assert_eq!(d["delta"]["units"].as_array().unwrap().len(), 3);
}

const SHIFT_BASE: &str = "package Q {
    part def T;
    part a : T;
    assert constraint { 1 <= 2 }
    assert constraint { 2 <= 3 }
    part z : T {
        attribute w = 1 + 2 + 3;
    }
}";

/// The edit: delete `part a` — every unnamed member after it in the
/// body re-derives its ordinal-chained id.
const SHIFT_TARGET: &str = "package Q {
    part def T;
    assert constraint { 1 <= 2 }
    assert constraint { 2 <= 3 }
    part z : T {
        attribute w = 1 + 2 + 3;
    }
}";

#[test]
fn rebase_aligns_ordinal_shifted_unnamed_siblings() {
    let base = compact_of(&[("u.sysml", SHIFT_BASE)]);
    let target = compact_of(&[("u.sysml", SHIFT_TARGET)]);
    let rebased = rebase_ids(&base, &target).unwrap();
    let bytes = delta_compact_cbor(&base, &rebased, &opts(false)).unwrap();
    let d = sysmlv2_cbor::describe(&bytes).unwrap();
    // Without the alignment pass this churned as ~20 deletes + creates
    // (both assert subtrees and z's expression tree re-derived); with
    // it, only the deleted member's own subtree goes.
    assert_eq!(
        d["delta"]["changes"]["creates"], 0,
        "no spurious creates: {d}"
    );
    let deletes = d["delta"]["changes"]["deletes"].as_u64().unwrap();
    assert!(
        (1..=6).contains(&deletes),
        "only the deleted member's subtree is removed: {d}"
    );
    // The delta still applies to the exact declared result.
    let applied = apply_delta_cbor(&bytes, &base).unwrap();
    assert_eq!(
        state_digest(&applied).unwrap().to_string(),
        d["delta"]["resultDigest"].as_str().unwrap()
    );
}

/// The delta-canonical order as CBOR.md documents it, implemented
/// naively and independently: ownership edges from the two list
/// properties, roots in payload order, preorder with
/// `ownedRelatedElement` targets before `ownedRelationship` targets,
/// first visit wins, unreachable tail in payload order.
fn documented_order(compact: &Value) -> Vec<String> {
    let arr = compact.as_array().unwrap();
    let index: std::collections::HashMap<&str, usize> = arr
        .iter()
        .enumerate()
        .map(|(i, e)| (e["@id"].as_str().unwrap(), i))
        .collect();
    let targets = |e: &Value, key: &str| -> Vec<usize> {
        e.get(key)
            .and_then(Value::as_array)
            .map(|a| {
                a.iter()
                    .filter_map(|v| v["@id"].as_str())
                    .filter_map(|s| index.get(s).copied())
                    .collect()
            })
            .unwrap_or_default()
    };
    let mut owned = vec![false; arr.len()];
    for e in arr {
        for k in ["ownedRelationship", "ownedRelatedElement"] {
            for t in targets(e, k) {
                owned[t] = true;
            }
        }
    }
    fn visit(
        i: usize,
        arr: &[Value],
        targets: &dyn Fn(&Value, &str) -> Vec<usize>,
        seen: &mut [bool],
        out: &mut Vec<usize>,
    ) {
        if seen[i] {
            return;
        }
        seen[i] = true;
        out.push(i);
        for k in ["ownedRelatedElement", "ownedRelationship"] {
            for t in targets(&arr[i], k) {
                visit(t, arr, targets, seen, out);
            }
        }
    }
    let mut seen = vec![false; arr.len()];
    let mut out = Vec::new();
    for (i, o) in owned.iter().enumerate() {
        if !o {
            visit(i, arr, &targets, &mut seen, &mut out);
        }
    }
    for (i, s) in seen.iter().enumerate() {
        if !s {
            out.push(i);
        }
    }
    out.iter()
        .map(|&i| arr[i]["@id"].as_str().unwrap().to_string())
        .collect()
}

fn ids_of(canon: &Value) -> Vec<String> {
    canon
        .as_array()
        .unwrap()
        .iter()
        .map(|e| e["@id"].as_str().unwrap().to_string())
        .collect()
}

#[test]
fn canonical_order_matches_its_documentation() {
    // A real model, and a synthetic payload exercising every clause of
    // the documented rule: two roots, both list properties, a shared
    // target, an ownership cycle, an external (absent) target, and an
    // unreachable pair.
    let real = compact_of(&[("m.sysml", BASE_UNIT)]);
    assert_eq!(
        documented_order(&real),
        ids_of(&delta_canonical(&real).unwrap())
    );

    let e = |id: &str, rels: &[&str], kids: &[&str]| -> Value {
        let refs = |ids: &[&str]| -> Value {
            Value::Array(
                ids.iter()
                    .map(|i| serde_json::json!({ "@id": i }))
                    .collect(),
            )
        };
        serde_json::json!({
            "@id": id,
            "@type": "Namespace",
            "ownedRelationship": refs(rels),
            "ownedRelatedElement": refs(kids),
        })
    };
    let synthetic = Value::Array(vec![
        e("root2", &["shared"], &[]),
        e("cycleB", &["cycleA"], &[]),
        e(
            "root1",
            &["relKid", "external-not-here", "shared"],
            &["kid"],
        ),
        e("island", &["islandKid"], &[]),
        e("kid", &[], &[]),
        e("relKid", &["cycleA"], &[]),
        e("islandKid", &["island"], &[]),
        e("shared", &[], &[]),
        e("cycleA", &["cycleB"], &[]),
    ]);
    let documented = documented_order(&synthetic);
    assert_eq!(documented, ids_of(&delta_canonical(&synthetic).unwrap()));
    // Spot-check the clauses themselves: kids before relationship
    // targets, first reachability winning the shared target, the
    // cycle entered once, the island pair appended in payload order.
    assert_eq!(
        documented,
        [
            "root2",
            "shared",
            "root1",
            "kid",
            "relKid",
            "cycleA",
            "cycleB",
            "island",
            "islandKid",
        ]
    );
}

/// Owner-elision fixtures: hand-built payload-identity states (a store's own
/// ids), exercising owner elision inside delta element records.
mod implied_owner_deltas {
    use super::*;
    use serde_json::json;

    const A: &str = "00000000-0000-4000-8000-00000000000a";
    const B: &str = "00000000-0000-4000-8000-00000000000b";
    const M: &str = "00000000-0000-4000-8000-00000000000e";
    const KID: &str = "00000000-0000-4000-8000-00000000000f";

    fn pkg(id: &str, name: &str, owned: &[&str], owner: &Value) -> Value {
        json!({
            "@type": "Package", "@id": id, "elementId": id,
            "declaredName": name, "isImpliedIncluded": false,
            "ownedRelationship":
                owned.iter().map(|o| json!({"@id": o})).collect::<Vec<_>>(),
            "owningRelationship": owner,
        })
    }

    fn membership(owner: &str) -> Value {
        json!({
            "@type": "OwningMembership", "@id": M, "elementId": M,
            "isImplied": false, "isImpliedIncluded": false,
            "visibility": "public",
            "ownedRelatedElement": [{"@id": KID}],
            "ownedRelationship": [],
            "owningRelatedElement": {"@id": owner},
            "owningRelationship": null,
        })
    }

    fn state(owner: &str) -> Value {
        Value::Array(vec![
            pkg(A, "A", if owner == A { &[M] } else { &[] }, &Value::Null),
            pkg(B, "B", if owner == B { &[M] } else { &[] }, &Value::Null),
            membership(owner),
            pkg(KID, "Kid", &[], &json!({"@id": M})),
        ])
    }

    #[test]
    fn reparent_applies_exactly_in_both_modes() {
        // Moving the membership from A to B: the shipped records'
        // backpointers match derivation over the target, leave the
        // wire, and re-materialize identically on apply.
        let base = state(A);
        let target = state(B);
        for portable in [false, true] {
            let bytes = delta_compact_cbor(&base, &target, &opts(portable)).unwrap();
            let got = apply_delta_cbor(&bytes, &base)
                .unwrap_or_else(|e| panic!("portable={portable}: {e}"));
            assert_eq!(
                got,
                delta_canonical(&target).unwrap(),
                "portable={portable}"
            );
        }
    }

    #[test]
    fn deviant_owner_states_survive_delta_records() {
        // Created elements whose owner state deviates from derivation:
        // absent keys ride the owner-exception section, inconsistent
        // values spell explicitly — apply reproduces them exactly.
        let bare = |id: &str, rels: &[&str]| -> Value {
            json!({
                "@type": "Namespace", "@id": id,
                "ownedRelationship":
                    rels.iter().map(|o| json!({"@id": o})).collect::<Vec<_>>(),
            })
        };
        let inconsistent = json!({
            "@type": "OwningMembership", "@id": M,
            "ownedRelatedElement": [], "ownedRelationship": [],
            // Claims an owner the forward lists do not: stays spelled.
            "owningRelatedElement": {"@id": B},
            "owningRelationship": null,
        });
        // A is owned by M per the forward list but carries no
        // backpointer keys at all (absent-key exceptions), and M is
        // owned by nothing while claiming B.
        let target = Value::Array(vec![bare(A, &[]), inconsistent]);
        let base = Value::Array(Vec::new());
        let bytes = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
        let got = apply_delta_cbor(&bytes, &base).unwrap();
        assert_eq!(got, delta_canonical(&target).unwrap());

        let described = sysmlv2_cbor::describe(&bytes).unwrap();
        assert_eq!(described["delta"]["impliedOwners"], true);
        assert_eq!(
            described["delta"]["ownerExceptions"].as_u64().unwrap(),
            1,
            "the bare Namespace lacks both backpointer keys: {described}"
        );
    }

    #[test]
    fn patched_updates_keep_replaying_owner_changes_exactly() {
        // A patch record carries owner changes as explicit ops and is
        // never post-passed; whole-element records elide. Either way
        // the applied state is exact (locked above) — here lock the
        // wire flag and the empty exception section.
        let base = state(A);
        let target = state(B);
        let bytes = delta_compact_cbor(&base, &target, &opts(false)).unwrap();
        // Whichever shape the planner chose per record, the applied
        // state is exact — locked above; here lock the wire flag too.
        let described = sysmlv2_cbor::describe(&bytes).unwrap();
        assert_eq!(described["delta"]["impliedOwners"], true);
        assert_eq!(described["delta"]["ownerExceptions"], 0);
    }
}
