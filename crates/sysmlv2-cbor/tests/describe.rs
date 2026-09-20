//! Describe gate: `describe` agrees with the encoders across every
//! payload form, and malformed bytes yield clean errors, never a
//! panic.

use serde_json::Value;
use sysmlv2_cbor::{
    DeltaOptions, delta_compact_cbor, describe, state_digest, to_compact_cbor,
    to_compact_cbor_elided, to_full_cbor,
};
use sysmlv2_parser::json::model_to_compact_json;
use sysmlv2_parser::model::Model;

fn compact_of(src: &str) -> Value {
    let mut model = Model::new();
    model.add_source("m.sysml".to_string(), src);
    model_to_compact_json(&model)
}

const BASE: &str = "package P { part def V { attribute total; } part v : V; part def W; }";
const TARGET: &str = "package P { part def V { attribute renamed; } part v : V; part def N; }";

#[test]
fn snapshot_summaries_agree_with_the_encoders() {
    let compact = compact_of(BASE);
    let n = compact.as_array().unwrap().len();

    let plain = to_compact_cbor(&compact).unwrap();
    let d = describe(&plain).unwrap();
    assert_eq!(d["form"], "compact");
    assert_eq!(d["elements"], n);
    assert_eq!(d["idsElided"], false);
    assert_eq!(d["bytes"], plain.len());
    assert_eq!(d["versions"]["supported"], true);
    assert_eq!(d["versions"]["layout"], 1);

    let elided = to_compact_cbor_elided(&compact, &|_| None).unwrap();
    let d = describe(&elided).unwrap();
    assert_eq!(d["form"], "compact");
    assert_eq!(d["idsElided"], true);
    assert_eq!(d["elements"], n);
    assert_eq!(d["exceptions"], 1, "one assigned root per unit");
    assert!(d["idDigest"].is_string());

    let mut model = Model::new();
    model.add_source("m.sysml".to_string(), BASE);
    let full = sysmlv2_parser::full::model_to_full_json_with(&model, false);
    let full_bytes = to_full_cbor(&full).unwrap();
    let d = describe(&full_bytes).unwrap();
    assert_eq!(d["form"], "full");
    assert_eq!(d["elements"], full.as_array().unwrap().len());
}

#[test]
fn delta_summaries_expose_digests_claims_and_changes() {
    let base = compact_of(BASE);
    let target = compact_of(TARGET);
    for portable in [false, true] {
        let opts = DeltaOptions::new()
            .with_portable(portable)
            .with_claims(vec![(1, sysmlv2_cbor::Claim::Id(uuid::Uuid::nil()))]);
        let bytes = delta_compact_cbor(&base, &target, &opts).unwrap();
        let d = describe(&bytes).unwrap();
        assert_eq!(d["form"], "delta");
        assert_eq!(
            d["delta"]["identityMode"],
            if portable { "portable" } else { "strict" }
        );
        assert_eq!(
            d["delta"]["baseDigest"].as_str().unwrap(),
            state_digest(&base).unwrap().to_string()
        );
        assert_eq!(
            d["delta"]["resultDigest"].as_str().unwrap(),
            state_digest(&target).unwrap().to_string()
        );
        assert_eq!(d["delta"]["claims"][0]["key"], 1);
        let ch = &d["delta"]["changes"];
        assert!(ch["creates"].as_u64().unwrap() >= 1, "{ch}");
        assert!(ch["deletes"].as_u64().unwrap() >= 1, "{ch}");
        assert!(ch["updates"].as_u64().unwrap() >= 1, "{ch}");
        assert_eq!(
            d["delta"]["createdIds"].as_array().unwrap().len() as u64,
            d["delta"]["created"].as_u64().unwrap()
        );
        assert_eq!(d["delta"]["targetsTruncated"], false);
    }
}

#[test]
fn mutated_payloads_never_panic_under_describe() {
    let base = compact_of(BASE);
    let target = compact_of(TARGET);
    for bytes in [
        to_compact_cbor(&base).unwrap(),
        to_compact_cbor_elided(&base, &|_| None).unwrap(),
        delta_compact_cbor(&base, &target, &Default::default()).unwrap(),
    ] {
        for i in 0..bytes.len() {
            let mut bad = bytes.clone();
            bad[i] ^= 0x01;
            let _ = describe(&bad);
        }
        for cut in 0..bytes.len() {
            let _ = describe(&bytes[..cut]);
        }
    }
}

// ---- hand-assembled payloads ----

/// A definite-length CBOR head (major type + argument, shortest form).
fn head(out: &mut Vec<u8>, major: u8, arg: u64) {
    let m = major << 5;
    if let Ok(b) = u8::try_from(arg) {
        if b < 24 {
            out.push(m | b);
        } else {
            out.extend_from_slice(&[m | 24, b]);
        }
    } else if let Ok(s) = u16::try_from(arg) {
        out.push(m | 25);
        out.extend_from_slice(&s.to_be_bytes());
    } else if let Ok(w) = u32::try_from(arg) {
        out.push(m | 26);
        out.extend_from_slice(&w.to_be_bytes());
    } else {
        out.push(m | 27);
        out.extend_from_slice(&arg.to_be_bytes());
    }
}

/// A strict delta over a one-element base whose single change record
/// is a field patch with `patch_entries` map entries declared; the
/// caller appends the entries (if any) and the trailing sections.
fn strict_delta_with_patch_head(patch_entries: u64) -> Vec<u8> {
    let mut b = sysmlv2_cbor::MAGIC.to_vec();
    head(&mut b, 4, 7); // array(7): header … owner exceptions
    let header = (u64::from(sysmlv2_cbor::LAYOUT_VERSION) << 32)
        | (u64::from(sysmlv2_cbor::tables::CBOR_TABLES_VERSION) << 16)
        | (u64::from(sysmlv2_cbor::ID_SCHEME_VERSION) << 8)
        | u64::from(sysmlv2_cbor::FLAG_DELTA | sysmlv2_cbor::FLAG_IMPLIED_OWNERS);
    head(&mut b, 0, header);
    head(&mut b, 4, 3); // base section
    head(&mut b, 2, 16);
    b.extend_from_slice(&[0; 16]);
    head(&mut b, 2, 16);
    b.extend_from_slice(&[0; 16]);
    head(&mut b, 5, 0); // claims
    head(&mut b, 0, 1); // base element count
    head(&mut b, 4, 0); // externals
    head(&mut b, 4, 0); // created ids
    head(&mut b, 4, 1); // one change record
    head(&mut b, 4, 2);
    head(&mut b, 0, 0); // target: base index 0
    head(&mut b, 5, patch_entries); // the patch map head
    b
}

#[test]
fn patch_map_headers_are_gated_against_the_payload() {
    // A well-formed patch (ordinal 0 → unset) describes as one patched
    // update, proving the assembly reaches the patch branch.
    let mut ok = strict_delta_with_patch_head(1);
    head(&mut ok, 0, 0);
    head(&mut ok, 4, 2);
    head(&mut ok, 0, 1); // OP_UNSET
    ok.push(0xF6); // null
    head(&mut ok, 5, 0); // owner exceptions
    let d = describe(&ok).unwrap();
    assert_eq!(d["delta"]["patchedUpdates"], 1);
    assert_eq!(d["delta"]["changes"]["updates"], 1);
    // A patch map claiming 2^63 entries must be an error, never an
    // overflow while sizing the skip. Which error depends on the
    // target's pointer width: where a length does not fit a `usize` the
    // reader refuses it as a length before the payload gate sees it, so
    // both spellings are the refusal this pins.
    for claimed in [1u64 << 63, u64::MAX, 1 << 32, 1 << 20] {
        let mut bad = strict_delta_with_patch_head(claimed);
        head(&mut bad, 5, 0);
        let err = describe(&bad).unwrap_err().to_string();
        assert!(
            err.contains("longer than payload") || err.contains("length overflow"),
            "{claimed}: {err}"
        );
    }
}

/// Index-keyed sections must be strictly ascending, and inspection
/// holds the same rule the decoders do — it used to walk the owner and
/// unit maps without looking at their keys at all.
#[test]
fn descending_section_indices_are_refused() {
    let mut ok = strict_delta_with_patch_head(1);
    head(&mut ok, 0, 0); // ordinal 0
    head(&mut ok, 4, 2);
    head(&mut ok, 0, 1); // OP_UNSET
    ok.push(0xF6); // null
    // Two owner-exception entries whose keys ascend: accepted.
    let mut good = ok.clone();
    head(&mut good, 5, 2);
    for key in [0u64, 1] {
        head(&mut good, 0, key);
        head(&mut good, 0, 1); // bits
    }
    assert_eq!(describe(&good).unwrap()["delta"]["ownerExceptions"], 2);
    // The same two entries, descending: refused.
    let mut bad = ok;
    head(&mut bad, 5, 2);
    for key in [1u64, 0] {
        head(&mut bad, 0, key);
        head(&mut bad, 0, 1);
    }
    let err = describe(&bad).unwrap_err().to_string();
    assert!(err.contains("not ascending"), "{err}");
}
