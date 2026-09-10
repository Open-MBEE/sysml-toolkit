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

#[test]
fn mutated_payloads_never_panic() {
    let mut rng = Rng(0xDEAD_BEEF_0BAD_CAFE);
    let base = to_compact_cbor(&random_model(&mut Rng(42))).unwrap();
    for _ in 0..4000 {
        let mut bytes = base.clone();
        match rng.below(3) {
            0 => {
                let i = rng.below(bytes.len());
                bytes[i] ^= 1 << rng.below(8);
            }
            1 => bytes.truncate(rng.below(bytes.len())),
            _ => {
                let i = rng.below(bytes.len());
                bytes[i] = rng.next() as u8;
            }
        }
        let _ = from_compact_cbor(&bytes); // Err is fine; panicking is not
    }
}

#[test]
fn arbitrary_bytes_never_panic() {
    let mut rng = Rng(0x0123_4567_89AB_CDEF);
    for _ in 0..4000 {
        let len = rng.below(200);
        let bytes: Vec<u8> = (0..len).map(|_| rng.next() as u8).collect();
        let _ = from_compact_cbor(&bytes);
    }
}

#[test]
fn mutated_elided_payloads_never_panic() {
    let mut rng = Rng(0x00D1_6E57_0000_0001);
    let model = random_model(&mut Rng(7));
    let base = sysmlv2_cbor::to_compact_cbor_elided(&model, &|_| None).unwrap();
    for _ in 0..4000 {
        let mut bytes = base.clone();
        match rng.below(3) {
            0 => {
                let i = rng.below(bytes.len());
                bytes[i] ^= 1 << rng.below(8);
            }
            1 => bytes.truncate(rng.below(bytes.len())),
            _ => {
                let i = rng.below(bytes.len());
                bytes[i] = rng.next() as u8;
            }
        }
        let _ = sysmlv2_cbor::from_compact_cbor_elided(&bytes, &|_| None);
    }
}
