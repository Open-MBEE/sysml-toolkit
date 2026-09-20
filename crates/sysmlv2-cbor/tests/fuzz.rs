//! Fuzz gates, dependency-free and deterministic (fixed-seed
//! xorshift): random well-typed element lists round-trip
//! Value-identically, and the decoder never panics on mutated or
//! arbitrary bytes.

use serde_json::{Map, Number, Value, json};
use sysmlv2_cbor::tables::{
    ENUM_TABLES, K_BOOL, K_ELEMENT_ID, K_ENUM, K_LITERAL, K_REF, K_REF_LIST, K_STR, K_STR_LIST,
    METACLASS_FIELDS,
};
use sysmlv2_cbor::{from_compact_cbor, to_compact_cbor};
use uuid::Uuid;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        // xorshift64* — deterministic, no dependency.
        self.0 ^= self.0 >> 12;
        self.0 ^= self.0 << 25;
        self.0 ^= self.0 >> 27;
        self.0.wrapping_mul(0x2545_F491_4F6C_DD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn chance(&mut self, percent: u64) -> bool {
        self.next() % 100 < percent
    }
}

fn uuid_str(rng: &mut Rng, tag: u8) -> String {
    let mut b = rng.next().to_be_bytes().repeat(2);
    b[6] = 0x40 | (b[6] & 0x0F); // RFC 4122 version/variant bits
    b[8] = 0x80 | (b[8] & 0x3F);
    b[15] = tag; // uniqueness within a generated model
    Uuid::from_bytes(b.try_into().unwrap()).to_string()
}

fn short_name(rng: &mut Rng) -> String {
    let n = 1 + rng.below(8);
    (0..n)
        .map(|_| (b'a' + rng.below(26) as u8) as char)
        .collect()
}

fn random_ref(rng: &mut Rng, ids: &[String]) -> Value {
    match rng.below(3) {
        0 => json!({ "@id": ids[rng.below(ids.len())] }),
        1 => json!({ "@id": uuid_str(rng, 0xEE) }), // external
        _ => json!({ "@ref": short_name(rng) }),
    }
}

fn random_literal(rng: &mut Rng) -> Value {
    match rng.below(5) {
        0 => Value::Bool(rng.chance(50)),
        1 => Value::Number(Number::from(rng.next() >> 8)),
        2 => Value::Number(Number::from(-(rng.below(1 << 30) as i64))),
        3 => {
            let f = (rng.below(1 << 20) as f64) / 64.0 - 8192.0;
            Value::Number(Number::from_f64(f).unwrap())
        }
        _ => Value::String(short_name(rng)),
    }
}

/// A random well-typed element list: every element a real metaclass,
/// every present field kind-correct, references local or external.
fn random_model(rng: &mut Rng) -> Value {
    let n = 1 + rng.below(10);
    let ids: Vec<String> = (0..n).map(|i| uuid_str(rng, i as u8)).collect();
    let mut out = Vec::with_capacity(n);
    for (i, id) in ids.iter().enumerate() {
        let code = rng.below(METACLASS_FIELDS.len());
        let (ty, fields) = METACLASS_FIELDS[code];
        let mut obj = Map::new();
        obj.insert("@id".into(), Value::String(id.clone()));
        obj.insert("@type".into(), Value::String(ty.to_owned()));
        for (prop, kind, etbl, dflt) in fields {
            if rng.chance(45) {
                continue; // absent
            }
            let value = match *kind {
                K_BOOL => Value::Bool(if rng.chance(60) {
                    *dflt == 1
                } else {
                    *dflt != 1
                }),
                K_STR => {
                    if rng.chance(30) {
                        Value::Null
                    } else {
                        Value::String(short_name(rng))
                    }
                }
                K_STR_LIST => Value::Array(
                    (0..rng.below(3))
                        .map(|_| Value::String(short_name(rng)))
                        .collect(),
                ),
                K_REF => {
                    if rng.chance(30) {
                        Value::Null
                    } else {
                        random_ref(rng, &ids)
                    }
                }
                K_REF_LIST => {
                    Value::Array((0..rng.below(4)).map(|_| random_ref(rng, &ids)).collect())
                }
                K_ENUM => {
                    let table = ENUM_TABLES[*etbl as usize];
                    if rng.chance(25) {
                        Value::Null
                    } else {
                        Value::String(table[rng.below(table.len())].to_owned())
                    }
                }
                K_LITERAL => random_literal(rng),
                K_ELEMENT_ID => Value::String(if rng.chance(80) {
                    id.clone()
                } else {
                    uuid_str(rng, 0xD0 | i as u8) // divergent mirror
                }),
                _ => unreachable!(),
            };
            obj.insert((*prop).to_owned(), value);
        }
        out.push(Value::Object(obj));
    }
    Value::Array(out)
}

#[test]
fn random_well_typed_models_round_trip() {
    let mut rng = Rng(0x5EED_CB02 ^ 0xA5A5_A5A5_A5A5_A5A5);
    for case in 0..300 {
        let model = random_model(&mut rng);
        let bytes =
            to_compact_cbor(&model).unwrap_or_else(|e| panic!("case {case}: encode: {e}\n{model}"));
        let back = from_compact_cbor(&bytes)
            .unwrap_or_else(|e| panic!("case {case}: decode: {e}\n{model}"));
        assert_eq!(back, model, "case {case}: round-trip Value-identical");
    }
}

/// One mutation of a payload: flip a bit, cut it short, or overwrite a
/// byte outright.
fn mutate(rng: &mut Rng, bytes: &[u8]) -> Vec<u8> {
    let mut out = bytes.to_vec();
    if out.is_empty() {
        return out;
    }
    match rng.below(3) {
        0 => {
            let i = rng.below(out.len());
            out[i] ^= 1 << rng.below(8);
        }
        1 => out.truncate(rng.below(out.len())),
        _ => {
            let i = rng.below(out.len());
            out[i] = rng.next() as u8;
        }
    }
    out
}

/// Arbitrary bytes of arbitrary length.
fn noise(rng: &mut Rng) -> Vec<u8> {
    let len = rng.below(200);
    (0..len).map(|_| rng.next() as u8).collect()
}

#[test]
fn mutated_payloads_never_panic() {
    let mut rng = Rng(0xDEAD_BEEF_0BAD_CAFE);
    let base = to_compact_cbor(&random_model(&mut Rng(42))).unwrap();
    for _ in 0..4000 {
        // Err is fine; panicking is not.
        let _ = from_compact_cbor(&mutate(&mut rng, &base));
    }
}

#[test]
fn arbitrary_bytes_never_panic() {
    let mut rng = Rng(0x0123_4567_89AB_CDEF);
    for _ in 0..4000 {
        let _ = from_compact_cbor(&noise(&mut rng));
    }
}

#[test]
fn mutated_elided_payloads_never_panic() {
    let mut rng = Rng(0x00D1_6E57_0000_0001);
    let model = random_model(&mut Rng(7));
    let base = sysmlv2_cbor::to_compact_cbor_elided(&model, &|_| None).unwrap();
    for _ in 0..4000 {
        let bytes = mutate(&mut rng, &base);
        let _ = sysmlv2_cbor::from_compact_cbor_elided(&bytes, &|_| None);
    }
}

#[test]
fn mutated_full_form_payloads_never_panic() {
    let mut rng = Rng(0xF011_F011_0000_0001);
    let base = sysmlv2_cbor::to_full_cbor(&random_model(&mut Rng(11))).unwrap();
    for _ in 0..4000 {
        let _ = sysmlv2_cbor::from_full_cbor(&mutate(&mut rng, &base));
        let _ = sysmlv2_cbor::from_full_cbor(&noise(&mut rng));
    }
}

/// A base and a target that differ: the target drops one element and
/// adds another, so the delta carries creates, deletes and updates.
fn delta_fixture(seed: u64) -> (Value, Value) {
    let base = random_model(&mut Rng(seed));
    let mut target = base.as_array().unwrap().clone();
    target.pop();
    let extra = random_model(&mut Rng(seed ^ 0xFFFF));
    target.extend(extra.as_array().unwrap().iter().cloned());
    // Re-derived ids can collide across the two draws; keep the first.
    let mut seen = std::collections::HashSet::new();
    target.retain(|e| seen.insert(e["@id"].as_str().unwrap().to_owned()));
    (base, Value::Array(target))
}

#[test]
fn mutated_deltas_never_panic_on_apply() {
    use sysmlv2_cbor::{
        DeltaOptions, apply_delta_cbor, apply_delta_cbor_lenient, apply_delta_cbor_report,
    };
    let mut rng = Rng(0xDE17_A000_0000_0001);
    let (base, target) = delta_fixture(23);
    for portable in [false, true] {
        let opts = DeltaOptions::new().with_portable(portable);
        let delta = sysmlv2_cbor::delta_compact_cbor(&base, &target, &opts).unwrap();
        // The unmutated delta applies cleanly — the fixture is a real
        // delta, not a payload every mutation would reject anyway.
        assert!(
            apply_delta_cbor(&delta, &base).is_ok(),
            "portable={portable}"
        );
        for _ in 0..4000 {
            let bytes = mutate(&mut rng, &delta);
            let _ = apply_delta_cbor(&bytes, &base);
            let _ = apply_delta_cbor_report(&bytes, &base);
            let _ = apply_delta_cbor_lenient(&bytes, &base);
            let _ = apply_delta_cbor(&noise(&mut rng), &base);
        }
    }
}

#[test]
fn mutated_and_arbitrary_bytes_never_panic_under_describe() {
    let mut rng = Rng(0xDE5C_21BE_0000_0001);
    let (base, target) = delta_fixture(31);
    let forms = [
        to_compact_cbor(&base).unwrap(),
        sysmlv2_cbor::to_full_cbor(&base).unwrap(),
        sysmlv2_cbor::to_compact_cbor_elided(&base, &|_| None).unwrap(),
        sysmlv2_cbor::delta_compact_cbor(&base, &target, &Default::default()).unwrap(),
    ];
    for form in &forms {
        for _ in 0..4000 {
            let _ = sysmlv2_cbor::describe(&mutate(&mut rng, form));
            let _ = sysmlv2_cbor::describe(&noise(&mut rng));
        }
    }
}

/// A mutated base-index artifact dies at its checksum, so these
/// iterations pin the seal, not the reader behind it: the body's own
/// sweep re-seals what it mutates and lives beside the reader. The delta
/// halves below are not sealed and do reach resolution.
#[test]
fn mutated_deltas_and_sealed_artifacts_never_panic_on_resolution() {
    use sysmlv2_cbor::index::{BaseIndex, resolve_portable_delta, resolve_strict_delta};
    let mut rng = Rng(0x10DE_C0DE_0000_0001);
    let (base, target) = delta_fixture(47);
    let index = BaseIndex::from_compact(&base).unwrap();
    let artifact = index.to_bytes();
    let strict = sysmlv2_cbor::delta_compact_cbor(&base, &target, &Default::default()).unwrap();
    let portable = sysmlv2_cbor::delta_compact_cbor(
        &base,
        &target,
        &sysmlv2_cbor::DeltaOptions::new().with_portable(true),
    )
    .unwrap();
    // The unmutated inputs resolve, so the loop below is mutating
    // something that otherwise works.
    assert!(resolve_strict_delta(&strict, &index).is_ok());
    assert!(resolve_portable_delta(&portable).is_ok());
    for _ in 0..4000 {
        let _ = BaseIndex::from_bytes(&mutate(&mut rng, &artifact));
        let _ = BaseIndex::from_bytes(&noise(&mut rng));
        let _ = resolve_strict_delta(&mutate(&mut rng, &strict), &index);
        let _ = resolve_portable_delta(&mutate(&mut rng, &portable));
        let _ = resolve_strict_delta(&noise(&mut rng), &index);
        let _ = resolve_portable_delta(&noise(&mut rng));
    }
}

/// One structural mutation of a well-typed model: the shapes a
/// malformed producer emits — wrong value kinds, non-object
/// references, nulls, missing `@id`/`@type`, arrays where scalars
/// belong.
fn mutate_model(rng: &mut Rng, model: &Value) -> Value {
    let mut arr = model.as_array().unwrap().clone();
    if arr.is_empty() {
        return Value::Array(arr);
    }
    let at = rng.below(arr.len());
    match rng.below(9) {
        0 => arr[at] = Value::String(short_name(rng)),
        1 => arr[at] = Value::Array(vec![arr[at].clone()]),
        2 => {
            arr[at].as_object_mut().unwrap().remove("@id");
        }
        3 => {
            arr[at].as_object_mut().unwrap().remove("@type");
        }
        4 => {
            arr[at]["@type"] = Value::String(short_name(rng));
        }
        5 => {
            arr[at][short_name(rng)] = Value::Bool(true);
        }
        6 => return Value::Object(serde_json::Map::new()),
        _ => {
            // Replace one property's value with a foreign shape.
            let obj = arr[at].as_object_mut().unwrap();
            let keys: Vec<String> = obj.keys().cloned().collect();
            let key = keys[rng.below(keys.len())].clone();
            obj.insert(
                key,
                match rng.below(6) {
                    0 => Value::Null,
                    1 => Value::Bool(rng.chance(50)),
                    2 => json!(rng.next() >> 8),
                    3 => Value::String(short_name(rng)),
                    4 => json!([short_name(rng)]),
                    _ => json!({ "@ref": rng.next() }),
                },
            );
        }
    }
    Value::Array(arr)
}

#[test]
fn structurally_mutated_models_are_errors_not_panics() {
    use sysmlv2_cbor::{
        DeltaOptions, delta_compact_cbor, state_digest, to_compact_cbor_elided, to_full_cbor,
    };
    let mut rng = Rng(0xE4C0_DE00_0000_0001);
    let well_typed = random_model(&mut Rng(101));
    let opts = DeltaOptions::new();
    for _ in 0..4000 {
        let model = mutate_model(&mut rng, &well_typed);
        // Err or Ok, never a panic, on every encoding entry point.
        let _ = to_compact_cbor(&model);
        let _ = to_full_cbor(&model);
        let _ = state_digest(&model);
        let _ = to_compact_cbor_elided(&model, &|_| None);
        let _ = delta_compact_cbor(&well_typed, &model, &opts);
        let _ = delta_compact_cbor(&model, &well_typed, &opts);
        let _ = sysmlv2_cbor::graph_normalize(&model);
        let _ = sysmlv2_cbor::index::BaseIndex::from_compact(&model);
    }
}

/// Reference-list items and single references that are not
/// `{"@id": …}` / `{"@ref": …}` objects are encoder errors on every
/// entry point that encodes — never a panic.
#[test]
fn malformed_references_are_errors_not_panics() {
    use sysmlv2_cbor::{delta_compact_cbor, state_digest, to_compact_cbor_elided};
    let id = "00000000-0000-4000-8000-000000000001";
    let empty = json!([]);
    for item in [
        json!("x"),
        Value::Null,
        json!(1),
        json!([]),
        json!({}),
        json!({ "@id": 1 }),
        json!({ "@ref": null }),
        json!({ "@id": id, "@ref": "x" }),
    ] {
        let model = json!([{ "@type": "Package", "@id": id, "ownedRelationship": [item] }]);
        assert!(to_compact_cbor(&model).is_err(), "{item}");
        assert!(state_digest(&model).is_err(), "{item}");
        assert!(to_compact_cbor_elided(&model, &|_| None).is_err(), "{item}");
        let opts = sysmlv2_cbor::DeltaOptions::default();
        assert!(delta_compact_cbor(&empty, &model, &opts).is_err(), "{item}");
        assert!(delta_compact_cbor(&model, &empty, &opts).is_err(), "{item}");
    }
    for member in [json!("x"), json!(1), json!([]), json!({})] {
        let model = json!([{ "@type": "OwningMembership", "@id": id, "memberElement": member }]);
        assert!(to_compact_cbor(&model).is_err(), "{member}");
    }
}
