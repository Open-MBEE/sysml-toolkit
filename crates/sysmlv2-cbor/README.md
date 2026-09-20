# sysmlv2-cbor

**s2c** — a deterministic binary encoding of the OMG SysML v2 / KerML **compact JSON interchange form** (the flat element array of KerML 10.4.4). Decoding reproduces the compact JSON `Value` byte-for-byte, so the binary form composes with every JSON consumer (lift, full-form derivation, checking, visualization) while costing an order of magnitude fewer bytes on the wire.

Every payload is one valid RFC 8949 CBOR item opening with the RFC 9277 file magic — tag 55799 wrapping application tag `0x24533243` (`$S2C`) — under the `.s2c` extension and the `application/vnd.sysmlv2.s2c+cbor` media type. Where the bytes go: `@id`s intern once as 16 raw bytes, references become 1–3-byte indices, property names become field ordinals, default values become presence bits, `@type` and enums become table codes. No external CBOR dependency; wasm-clean.

```rust
use sysmlv2_cbor::{to_compact_cbor, from_compact_cbor};

let bytes = to_compact_cbor(&compact_value)?;      // Value -> .s2c
assert_eq!(from_compact_cbor(&bytes)?, compact_value);
```

## The four payload forms

| form | emit / read | what it is |
|---|---|---|
| **compact** | `to_compact_cbor` / `from_compact_cbor` | the interchange snapshot; the only ingest form |
| **compact, id-elided** | `to_compact_cbor_elided` / `from_compact_cbor_elided` | graph-derivable ids omitted (`IDS.md`); exception map + integrity digest, verified on decode |
| **full** | `to_full_cbor` / `from_full_cbor` | derived properties + implied relationships; an emit view for clients that skip derivation |
| **delta** | `delta_compact_cbor` / `apply_delta_cbor[_lenient]` | element-granular change records against a digest-named base; strict (indexed) or portable (id-keyed, cherry-pickable) identities |

`from_cbor` / `from_cbor_with` accept whichever form the header flags declare. Forms refuse each other's decoders with pointed messages; the header word versions the wire layout, the generated metamodel tables, and the id-derivation scheme independently.

## Measured (real corpora)

Against minified compact JSON: **9.9–10.5×** raw and **~2.1×** after both sides deflate; with `--elide-ids` **17.5–18.9×** raw and **7.0–7.8×** after deflate (the interned UUID table is the only incompressible part, and elision removes it). Full form lands ~11×. An edit-sized delta commit is a few hundred bytes against megabyte snapshots. In the corpus benchmark, decoding takes about 1.3× JSON parsing time; the size advantage does not imply a faster decoder. Numbers, methodology, and the wire specification: [`CBOR.md`](../../CBOR.md) (reproduce with `cargo run --release -p sysmlv2-cbor --example corpus_bench`).

## Layered use

This crate is a leaf at the serialization boundary (`Value ↔ bytes`). Higher layers wrap it: `sysmlv2-transform` (`Session::to_compact_cbor`, `::to_compact_cbor_elided`, `::to_full_cbor`, `::from_compact_cbor`, `::delta_cbor_from`), the `sysmlv2` CLI (`convert --to compact-cbor | full-cbor`, `--elide-ids`, `--delta-base`, `.s2c` inputs), and the wasm / Python bindings (`toCompactCbor` / `to_compact_cbor` etc.).
