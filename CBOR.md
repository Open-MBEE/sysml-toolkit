# Compact-form CBOR

A deterministic binary re-encoding of the **compact JSON interchange form** (the flat element array of KerML 10.4.4), implemented by the `sysmlv2-cbor` crate. Decoding reproduces the compact JSON `Value` byte-for-byte — same key sets, same defaults, same reference spellings — so the binary form composes with every existing JSON consumer (lift, full-form derivation, checking, viz) with no semantic surface of its own.

The payload is a single valid RFC 8949 CBOR item from byte 0 (definite lengths, shortest heads, 64-bit floats): two identifying tags wrap the body array (see *File format & media type* below), and any off-the-shelf CBOR reader walks the whole structure. The *meaning* of the small integers comes from generated tables (`sysmlv2-model/src/cbor_tables.rs`, from the vendored normative metamodel XMI + JSON schemas by `tools/gen_cbor_tables.py`).

## File format & media type

Every payload — snapshot, full form, elided, delta — opens with the fixed eight-byte **RFC 9277 file magic** (the "tag-wrapped" method): the self-described-CBOR tag 55799 wrapping application tag `0x24533243`, whose big-endian bytes spell **`$S2C`** ("SysML v2 CBOR"). The body array is the tags' content, so the whole file is one valid CBOR item from byte 0:

```
D9 D9F7          # tag(55799) — "this is CBOR" (RFC 8949 section 3.4.6)
   DA 24533243   # tag(0x24533243) — "$S2C", ours (RFC 9277 app tag)
      84 …       # the array(4) / array(6) body, unchanged
```

Which payload kind it is lives in the body's own header flags, never in the name.

- **File extension:** `.s2c`. The CLI keys input detection on it (`sysmlv2 convert model.s2c --to text`).
- **Magic:** the fixed prefix `D9 D9 F7 DA 24 53 32 43` — the literal `$S2C` bytes sit at offset 4, so `grep`/hexdump readers still see the string, while a generic CBOR tool parses the file and can even report *whose* data it holds via the tag. Decoders refuse a payload without the prefix by name, so a mis-routed JSON or foreign CBOR file fails immediately and legibly. The application tag should be registered in IANA's first-come-first-served CBOR tag registry (RFC 9277 encourages mnemonic four-byte tags; `0x24533243` is in range with no zero bytes).
- **Media type (HTTP content negotiation):**

  ```
  application/vnd.sysmlv2.s2c+cbor
  ```

  The `+cbor` structured-syntax suffix (RFC 6839) is legitimate precisely because the RFC 9277 construction keeps the entire payload valid CBOR — suffix-aware middleware and generic CBOR handlers can match on it. An optional `form` parameter lets a client negotiate a specific payload kind rather than inspect the header flags: `form=compact` (default), `form=compact-elided`, `form=full`, `form=delta`. Examples:

  ```
  Accept: application/vnd.sysmlv2.s2c+cbor;form=compact-elided,
          application/vnd.sysmlv2.s2c+cbor;q=0.9,
          application/json;q=0.1
  Content-Type: application/vnd.sysmlv2.s2c+cbor;form=delta
  ```

  The type is unregistered vendor-tree for now; register it (and the application tag) before any public service exposes them.

## Layout

```
array(4):
  [0] uint            header word: layout u8 · tables u16 ·
                      scheme u8 · flags u8 (big-endian packed)
  [1] array(M) bstr16 external-UUID table (sorted)
  [2] array(N) bstr16 id table — element k's @id, raw 16 bytes
  [3] array(N)        elements
  [4] map(uint→uint)  owner exceptions (only with flag 0x20): element
                      index → absent-key bits (1 = owningRelationship,
                      2 = owningRelatedElement), ascending indices
  [5] map(uint→tstr)  unit structure (only with flag 0x10): element
                      index of each unit's root namespace → that
                      unit's source path, ascending indices
element := array(3):
  [0] uint            type code (concrete metaclass, sorted index)
  [1] uint            presence bits — bit i: field ordinal i is
                      present with its default value (0 value bytes)
  [2] map(uint→value) non-default fields, ordinal-keyed, ascending
```

(The arity is `4 + 1 per set section flag`; the owner-exception section precedes the unit structure when both are present.)

**Implied ownership backpointers (flag 0x20).** The two backpointers are exact metamodel inverses of the forward ownership lists — `owningRelationship` inverts membership in some element's `ownedRelatedElement`, `owningRelatedElement` inverts membership in some element's `ownedRelationship` — so for a well-formed payload they carry no information. Under this flag (set by every compact snapshot emitter) a backpointer whose value equals its derivation is simply not spelled: the decoder re-derives it by the shared rule (*first claimant in element order, then list order, wins*) and re-materializes the key. Deviations still travel exactly: a value that differs from derivation stays a map entry, an explicit `null` under a derived owner stays a presence bit, and an element whose source JSON lacked the key entirely rides the owner-exception section — decode is Value-identical for every input, consistent or not. Measured on the standard-library payload this removes ~10% of the wire (91,311 backpointer refs). Two invariants keep the digest world stable: **the digest space is untouched** (state digests canonicalize through an owners-spelled encoding, so digests recorded before this flag existed remain valid), and pre-flag payloads decode unchanged while pre-flag decoders refuse flagged payloads by name.

**Delta records elide too.** Delta payloads carry the flag as well: change records that ship whole elements (creates and whole-element updates) elide backpointers matching derivation over the **canonical target** — the identical array, in the identical order, that application reconstructs, canonicalizes, and re-derives over, with the result digest as the end-to-end proof. Field patches never participate: a patch replays literally over the held base element, so an owner change or removal travels as an explicit `set`/`unset` op and stays exact; verbatim base copies are never touched. The delta body grows the same owner-exception section (change-record ordinal → absent-key bits), so `array(6)` becomes `array(6 + 1 per section flag)` with the exception section before the units section.

**Unit structure (flag 0x10).** Snapshot payloads emitted from a session carry the model's original file layout: one entry per user unit, pairing the element-array index of the unit's root namespace with the unit's source path (the full relative path, not just a basename). The body is `array(5)` exactly when the flag is set; an empty table encodes identically to no table. Decoders that restore a session from the payload name its units by these paths — so the round trip reproduces the original files *and*, because path-seeded id derivation sees the same unit names, the original element ids. Delta payloads do not carry the section (their base does).

Where the bytes go, relative to compact JSON:

- `@id`/`elementId`/`@type` strings → 16 raw bytes once in the id table + a 1–2-byte type code; `elementId` re-materializes from the mirror rule (a presence bit).
- `{"@id": …}` reference objects (~52 characters) → 1–3-byte indices (locals first, then externals). The hermetic `{"@ref": name}` spelling stays a text string — CBOR's major type distinguishes it from an index with no tag.
- Property names → 1-byte ordinals into the metaclass's sorted field list.
- Default-valued properties (`isImpliedIncluded: false`, `isUnique: true`, `visibility: "public"`, `null`s, empty lists) → presence bits. The compact emitter's key sets are *instance-dependent*, so presence is explicit rather than assumed — absent and present-with-default reproduce exactly.
- Closed vocabularies (`visibility`, `direction`, the `*Kind`s) → small uints; `@type` names never appear on the wire.

**Versioning.** The header word carries three independent axes plus the flags byte, refused with axis-specific messages:

- **layout (u8)** — the array shapes, presence encoding, reference index spaces, and delta framing. Refused unconditionally on mismatch.
- **tables (u16)** — the generated metamodel tables (type codes, field ordinals, kinds, defaults; currently from the 20250201 normative release). Refused on any decode, since every element record reads through them — but independently of layout, so a tables-only regeneration is diagnosable as exactly that.
- **scheme (u8)** — the id-derivation scheme (`IDS.md`; wire scheme 1 is that document's graph-derived derivation). Consulted **only** where derivation is in play (id-elided payloads, snapshot or delta): explicit-id payloads decode regardless of it. Digest failures on matched-scheme payloads therefore come pre-diagnosed: not a scheme skew, so library skew or corruption.

**Flags.** `elideIds` (1), `fullForm` (2), `delta` (4), `deltaPortable` (8), `unitPaths` (16), `impliedOwners` (32), and `explicitIds` (64): a compact snapshot whose ids are not all the graph derivation of `IDS.md` — a session that loaded a document from another producer, or under other unit names, keeps the ids it was given and marks the payload so a receiver never re-derives them; such a session refuses id elision. Informational for decoders, which always read the id table; `describe` reports it as `explicitIds`.

Unknown flag bits are refused, so a decoder never misreads a payload kind it does not know. **Determinism:** byte output is a pure function of the input Value (canonical type/field/table ordering); an exact byte fixture in `crates/sysmlv2-cbor/tests/determinism.rs` pins the wire format.

## Using it

- **CLI** — `sysmlv2 convert model.sysml --to compact-cbor -o m.s2c`; a `.s2c` input decodes up front and flows like `.json` (`sysmlv2 convert m.s2c --to text`). Binary stdout when `-o` is omitted. `--flexo` is JSON-only (the change-record envelope wraps JSON; CBOR carries the bare element array).
- **Rust** — `sysmlv2_cbor::{to_compact_cbor, from_compact_cbor}` (`Value ↔ bytes`), or `Session::{to_compact_cbor, from_compact_cbor[_with_library]}` in `sysmlv2-transform`.
- **wasm** — `session.toCompactCbor(): Uint8Array`, `Session.fromCompactCbor(bytes, libSources?, libSnapshot?, indent?)`.
- **Python** — `session.to_compact_cbor() -> bytes`, `Session.from_compact_cbor(data, lib=None)`.

Every Rust entry point fails with one `sysmlv2_cbor::Error`, whose `Display` explains the refusal and whose `kind()` classifies it for callers that act on the classes differently: `MissingMagic` (not an s2c payload), `UnsupportedVersion` (a wire-layout, table, id-scheme, base-index or resolver-artifact generation this build does not implement), `NeedsResolver` (an id-elided payload at an entry point that carries no name resolver), `WrongForm` (a well-formed payload of another kind — the message names the entry point to use), `BaseDigestMismatch` (the held base is not the one the delta names), `Truncated`, and `Malformed` for everything else. The enum is `#[non_exhaustive]`: later wire generations will distinguish more, so match with a wildcard arm.

## Compact-form canonicalization

The presence-faithful round-trip means the codec never bridges the *default elision split*: a producer that wire-elides schema-default spellings (`isUnique: true`, `isAbstract: false`, `visibility: "public"`, `null`s, empty lists, the `elementId` mirror) and one that spells them explicitly emit different JSON for the same state, and no digest over either spelling can compare them. `sysmlv2_cbor::canonicalize_compact(json) -> json` (wasm free function `canonicalizeCompact`) closes it: every element is materialized through its metaclass field table and re-emitted with each absent property spelled at its metaclass-specific default from the generated tables. Present values and `@id`s are preserved verbatim, element order is untouched, literal-valued fields (no default) stay absent, and the pass is idempotent — both producers land on the same canonical document, so digest comparison becomes sound. Strict like the encoder: unknown `@type`s and non-compact-form keys (derived properties included) are errors. Gate: `crates/sysmlv2-cbor/tests/canonical.rs` (golden corpus under a simulated wire elision) + `sysmlv2-wasm/tests/api.rs`.

`sysmlv2_cbor::graph_normalize(&Value) -> Value` / `graph_normalize_compact(json) -> json` (wasm free function `graphNormalizeCompact`) is the **mirror twin** in the opposite direction: it re-spells a compact document in the *graph-normal* (stored/wire-normal) form a graph-backed store reconstructs after materializing the document as triples — every default-valued property elided, derived canonical properties (`owner`, `qualifiedName`, …) dropped as such a store's ingest accepts-and-drops them (keys outside even the full schema stay errors), `elementId` always spelled, absent ownership backpointers completed by the same first-claimant forward-list derivation the wire-elision flag uses, and elements sorted by `@id` (root order is digest-relevant). The point: `state_digest(graph_normalize(doc))` is the digest such a store reconstructs after ingesting `doc`, so snapshots — and strict deltas whose base digests are declared in the same domain — encoded from the graph-normal spelling pass the store's end-to-end digest verification, which kernel-spelled documents by design do not ("declared X, reconstructed Y"). Idempotent; `graph_normalize(canonicalize(D)) == graph_normalize(D)` — the two spelling domains collapse from either side. Same gates.

## Measured comparison (real corpora)

Two pinned corpora, measured with toolkit implementation `15a9de5` on Apple Silicon/macOS arm64. Reproduce with `cargo run --release -p sysmlv2-cbor --example corpus_bench` (medians of five runs; deflate level 8). This harness measures each serialization stage; it does not exercise the CLI’s prepared-library cache. Times are descriptive single-machine results, not performance guarantees.

The official library pin is `de1070ae8e79c21532b8004fc663d47b35d0e9fa`; Apollo is `6e9c93fe7d80c5ca3534bb14b10ab374a643ef2d`.

**Library** — 94 textual units loaded as user sources, 91,405 compact elements.

| form | bytes | +deflate |
|---|---:|---:|
| pretty JSON | 45432828 | 4575775 |
| minified JSON | 35432925 | 4351340 |
| compact CBOR | 3579835 | 2077326 |
| compact CBOR --elide-ids | 2029539 | 558533 |
| ratio min-JSON / CBOR | 9.90x | 2.09x |

**Apollo 11** — 28 textual units resolved against the standard library, 23,276 compact elements.

| form | bytes | +deflate |
|---|---:|---:|
| pretty JSON | 11917868 | 1177849 |
| minified JSON | 9275587 | 1125537 |
| compact CBOR | 886602 | 547650 |
| compact CBOR --elide-ids | 491485 | 160052 |
| ratio min-JSON / CBOR | 10.46x | 2.06x |

| stage | library ms | Apollo ms |
|---|---:|---:|
| text → model (parse) | 10.5 | 17.2 |
| model → element array (lower+resolve+Value) | 252.6 | 234.8 |
| Value → minified JSON | 28.1 | 7.5 |
| Value → CBOR | 127.9 | 30.5 |
| minified JSON → Value | 88.4 | 23.7 |
| CBOR → Value | 116.1 | 30.9 |
| Value → CBOR --elide-ids (derive+verify) | 251.2 | 55.6 |
| CBOR --elide-ids → Value (derive+digest) | 262.2 | 62.3 |
| Value → textual notation (lift+print) | 112.1 | 29.0 |

Compact CBOR is 9.9–10.5× smaller than minified JSON, or about 2.1× after deflate. In this run, encoding takes about 4.1–4.6× JSON serialization time and decoding takes about 1.3× JSON parsing time. Smaller payloads can reduce transfer/storage costs, but this measurement does not establish a faster decoder. Id elision adds graph derivation and digest work. Lowering and resolution remain a substantial part of the complete pipeline.

Full-form CBOR is 10.9–11.6× smaller than minified full JSON (1.78× after deflate). Appending the harness’s small package yields strict deltas of 338 bytes for the library and 316 bytes for Apollo; portable deltas are 345 bytes for both.

## Delta payloads

`delta_compact_cbor(base, target)` / `apply_delta_cbor(bytes, base)` encode element-granular change sets — identity + payload per change, null payload = delete — matching the Systems Modeling API's commit model. (On the wire a strict update may travel as a **field patch** instead of a whole element — see below — but application always produces whole-element results, so the commit model is unchanged.) A delta names its base by **claims + proof**: an optional map of spec-canonical version identifiers (project/commit ids, a service URI — opaque routing hints) and a mandatory content digest. Digests and diffs operate on the **delta-canonical element order** (ownership preorder, `delta_canonical`), so the same model state digests identically regardless of who emitted it or in what order; `empty_base_digest()` is the recognizable constant for the API's first-commit case, and a snapshot remains a semantically different thing from an all-creates delta (complete state vs edit).

### The delta-canonical order (normative)

Strict-delta indices, the state digest, and the array `apply` returns all live in one element order, derived from the payload content alone. An independent implementation reproduces it as follows:

1. **Ownership edges** are the `@id` references in each element's `ownedRelationship` and `ownedRelatedElement` list properties, in list order, ignoring targets not present in the payload. An element any such edge points at is *owned*.
2. **Roots** are the non-owned elements, kept in payload order.
3. From each root in turn, walk depth-first **preorder**: visit the element, then recurse into its `ownedRelatedElement` targets in list order, then its `ownedRelationship` targets in list order. An element already visited is not visited again (first reachability wins), so shared or cyclic ownership cannot double-count.
4. Elements unreachable from every root are appended in payload order.

Only root order and the unreachable tail depend on payload order — and root order is semantic (a multi-unit model's units). Everything under a root is fully ownership-derived, which is what makes the digest emitter-independent.

A strict delta's base references (`updateTargets`, `deleteTargets`, element back-references) are positions in the **base's** sequence; the array a successful `apply` returns is the **result's** sequence. A store that records the id sequence alongside each state can therefore resolve a strict delta's indices to element ids — and gate on the base digest — without holding the base payload itself. `payload --ids` (CLI.md section 15.2) prints the sequence and digest of any snapshot, so a recorded sequence is always checkable against the reference implementation.

Two identity modes:

- **strict/indexed** (default): change targets and base references are indices into the digest-pinned base order — smallest bytes. The digest gate is *hard*: an index against a different base would silently edit the wrong element, so it never applies there.
- **portable/id-keyed** (`--delta-portable`): raw element ids, upsert-flavored like the API. `apply_delta_cbor_lenient` applies best-effort to a divergent base and reports no-op deletes, upserted updates, and replaced creates. Graph-derived ids make cherry-picks land on the same-named element of the other base.

Bases and targets need not share an id derivation. Element ids chain from a unit-root seed that varies with how a payload was produced (unit name, single- vs multi-unit build, another producer entirely), so two independently derived payloads can agree on every element yet share **no** ids — diffed raw, that degenerates to full replacement (all creates + all deletes, zero updates). `rebase_ids(base, target)` closes the gap before diffing: a target element whose ownership path (the IDS.md segment chain) matches a base element's adopts that element's id — `elementId` mirrors and in-payload references rewritten, documents pairing by first member name — so unchanged elements coincide by identity whoever produced the base. The CLI applies it automatically under `--delta-base`; same-session diffs (`Session::delta_cbor_from`) don't need it and must not use it — session identity survives moves, which path matching cannot see.

A result digest verifies the applied state end-to-end when the base matched. Surfaces: `Session::delta_cbor_from(base, portable)`, CLI `--delta-base <base.json|cbor>` (emit a delta with `--to compact-cbor`, or apply a delta `.s2c` input), and the codec functions. Measured on the real corpora, an edit-sized commit (append a small package) is **~345–385 bytes** against snapshots of 1.0–4.0 MB — and the near-empty update set is the id scheme's edit stability (`IDS.md`) made visible: the unchanged 91k elements kept their ids.

**Field-patch updates** (strict identity only, automatic). An update re-shipping a whole element pays O(its property count) — for the dominant real edit, one member spliced into a big owner, that meant re-shipping the owner's entire relationship list. Strict updates now diff at the field level: a `map` payload of `ordinal → [opcode, arg]` ops — set (field present with a value), unset (field absent), splice (`[at, del, [items…]]` on a list field) — replayed over the held base element. The payload head already tells the three update shapes apart (null = delete, element record, patch map), so patches need no extra framing; the encoder encodes both forms and ships the smaller (a pure function of the inputs). A planner self-check (replay must reproduce the target exactly) falls back to the whole element rather than ever risking a divergent applied state, and the result digest still verifies end-to-end. Effect: inserting a member into a 6-, 60-, or 300-member owner costs 132/137/142 delta bytes — index-width noise, where it was O(members). Portable deltas keep whole elements (their upserts must materialize on divergent bases).

**Id-elided deltas** (`--elide-ids --delta-base`, strict identity only). The only id bytes a strict delta carries are its created-id table (16 per create) and externals; with elision the created-id table gives way to a count, an exception map (created ordinal → id, for foreign or underivable ids), and a recovered-id digest. Creates decode under placeholder ids; the applier re-derives their ids from the **applied** graph — surviving base elements pin their known ids, exceptions override, everything else chains per `IDS.md` — then proves the digest before rewriting the placeholders. Created-id churn therefore costs **zero wire bytes**, whatever the edit shape. These payloads consult the scheme axis (like elided snapshots) and need the applier to resolve external names against the same `--lib` version; portable + elide is refused on both ends — the portable mode exists to carry explicit ids to divergent bases, which elision contradicts. Surfaces: `delta_compact_cbor_elided` / `apply_delta_cbor_with`, `Session::delta_cbor_elided_from` (session-side apply resolves through the loaded library), CLI `--elide-ids` alongside `--delta-base` on emit, automatic on apply.

## Full-form CBOR (emit view)

`to_full_cbor` / `from_full_cbor` re-encode the **full** interchange form (derived properties + implied relationships) in its own ordinal space (`FULL_METACLASS_FIELDS`; classes reach 138 properties, so presence travels as a byte-string bitmap where a u64 no longer fits). A header flag distinguishes the forms and each refuses the other's decoder; `from_cbor` accepts either. Full-form CBOR is an **emit view** for clients that want the materialized element list without running derivation — never an ingest format: transport compact, expand at the edge. Surfaces: `Session::to_full_cbor(recover_refs)` (recovery annotations compose — they are ordinary elements), CLI `--to full-cbor` (and full `.s2c` inputs normalize to compact like full JSON), wasm `toFullCbor`, py `to_full_cbor`.

Because the full form materializes every schema property — most at their defaults — presence bits absorb even more of it than compact:

| corpus | minified full JSON | full CBOR | raw ratio | after deflate |
|---|---:|---:|---:|---:|
| library | 160,840,657 | 14,725,369 | **10.9×** | **1.8×** |
| model | 44,823,307 | 3,906,925 | **11.5×** | **1.8×** |

## Id elision (`--elide-ids`, opt-in)

With user-element ids graph-derived (`IDS.md`), the encoder can **verify and omit** them: each id that re-derives from the graph is dropped; roots, foreign ids, and anything underivable ride a per-element exception map, and a mandatory 16-byte digest — `uuid5` over the final id sequence — lets the decoder prove its recovered ids are exactly the ones elided. Verification is per element, so *any* payload encodes: a foreign document simply lands wholly in the exception map at ≈ the non-elided size. A digest mismatch is a hard error naming the likely causes (library skew — encode and decode against the same `--lib` version; derivation drift; exception-map corruption). The digest guards **id recovery**, not content integrity — transport checksums or a signing envelope own that.

Surfaces: `to_compact_cbor_elided`/`from_compact_cbor_elided` (+ `from_cbor_with`), `Session::to_compact_cbor_elided`, CLI `--to compact-cbor --elide-ids` (elided `.s2c` inputs decode automatically, using `--lib` for the effective-name targets). Compact-form only; decoders without a resolver refuse elided payloads cleanly.

The id table was the dominant *incompressible* remainder of the un-elided format, so elision pays off most after compression:

| corpus | CBOR | elided | CBOR+deflate | elided+deflate |
|---|---:|---:|---:|---:|
| library | 3,579,835 | 2,029,539 | 2,077,326 | 558,533 |
| Apollo | 886,602 | 491,485 | 547,650 | 160,052 |

Against minified JSON, elision gives **17.5–18.9× raw** and **7.0–7.8× after both sides deflate** in the benchmark above. Derivation and digest verification roughly double ordinary CBOR encode/decode time; see the stage table for the measured costs.
