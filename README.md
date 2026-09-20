# sysml-toolkit

A Rust toolchain for [OMG SysML v2](https://www.omg.org/sysml/sysmlv2/) and KerML — library crates, the `sysmlv2` CLI, a language server, and Python and WebAssembly bindings covering the full pipeline, not just parsing:

- **Parse** `.sysml` / `.kerml` sources into a fully-typed, span-carrying AST, with error recovery and rustc-style diagnostics.
- **Format** with a canonical, idempotent printer that preserves notes.
- **Resolve** names across files and against the vendored standard library (normative KerML 9.1 element IDs, verified against the published XMI).
- **Interchange JSON in both directions** — emit the compact (KerML 10.4) and full (derived properties + implied relationships) forms, and read JSON back to text.
- **Binary interchange (s2c)** — a deterministic CBOR encoding of the compact form (`.s2c`, RFC 9277 file magic): ~10× under minified JSON, optional id elision (~15–19× with an integrity digest), full-form emit, and digest-verified delta payloads for commit-sized changes.
- **Validate** — body-context legality, duplicate names, referential checks, and semantic constraints (usage typing, multiplicity bounds, specialization cycles, redefinition compatibility, argument binding, and quantity dimensions).
- **Lint** — configurable project-policy rules (style, hygiene, dead model) with optional auto-fixes, additive beside `check`; both verbs report as rustc-style text or as one JSON document.
- **Evaluate** expressions exactly: rational arithmetic with no rounding (`0.1 + 0.2 == 0.3`), KerML Function Library intrinsics, lambdas, quantities with exact unit conversion, user-defined calculations, featuring-context rollups.
- **Verify constraints** to satisfied / violated / undecided verdicts, and **solve** the undecided ones with Z3 (witnesses, unsatisfiability and validity proofs) or the built-in interval propagator.
- **Transform** — rename, set value, insert, remove, retarget, extract and inline definitions as span-anchored text splices that preserve formatting and notes byte-for-byte, with commits that reparse, re-resolve, and verify untouched references kept their targets.
- **Visualize** as PlantUML — seven views (structure tree, interconnection, state, action, sequence, use case, mixed) with comment notes, metadata stereotypes, inherited members, color palettes, and clickable source hyperlinks carried into rendered SVG.
- **Edit** with a Language Server (diagnostics, outline, semantic tokens, formatting, navigation, completion, inlay hints, code lenses, refactorings) and its VS Code client extension.

Worked tours with real outputs: [`CLI.md`](CLI.md) walks every subcommand; [`SDK.md`](SDK.md) walks the transformation SDK from Python. [`CBOR.md`](CBOR.md) specifies the binary interchange form and carries its measured numbers; [`IDS.md`](IDS.md) specifies element identity; [`INTEROP.md`](INTEROP.md) records the interchange representation rules.

```rust
use sysmlv2_parser::model::Model;
use sysmlv2_parser::json::model_to_compact_json;

let mut model = Model::new();
model.load_library_dir("spec-refs/SysML-v2-Release/sysml.library".as_ref())?;
model.add_source("demo.sysml", r#"
    package Demo {
        import ScalarValues::*;
        part def Vehicle { attribute mass : Real = 1500.0; }
        part car : Vehicle { attribute :>> mass = 1800.0; }
    }
"#);
let json = model_to_compact_json(&model);
// `mass : Real` now references "14c0aa22-5489-59b5-b438-ded26e83ba31" —
// the normative, published element ID of ScalarValues::Real.
```

```sh
# The sysmlv2 CLI (cargo install --path crates/sysmlv2-cli  /  cargo run --bin sysmlv2 --)
sysmlv2 convert model.sysml --to compact-json --lib sysml.library/
sysmlv2 convert model.json --to text --lib sysml.library/   # JSON → textual notation
sysmlv2 convert model.sysml --to compact-cbor -o model.s2c  # binary interchange
sysmlv2 fmt --check src/*.sysml        # canonical formatter (notes preserved)
sysmlv2 check model.sysml --lib sysml.library/   # validation + referential/semantic checks
sysmlv2 check --strict --lib sysml.library/ *.sysml  # warnings fail too (gate a commit)
sysmlv2 lint model.sysml --fix         # project-policy rules, auto-fixable ones applied
sysmlv2 lint --format json model.sysml  # findings as one JSON document on stdout (check too)
sysmlv2 eval model.sysml --lib sysml.library/    # evaluate feature values
sysmlv2 verify model.sysml --solve     # constraint verdicts; Z3 for the undecided
sysmlv2 query model.sysml 'ownedFeature(Demo::Vehicle)->select { in p; p istype Demo::Wheel }'
sysmlv2 refactor extract model.sysml Demo::car # usage↔definition refactorings (extract / split / inline)
sysmlv2 payload after.s2c --delta-from before.s2c -o commit.s2c  # inspect, diff, and apply interchange payloads
sysmlv2 describe model.sysml Demo::car         # one element: metaclass, owner, typing, position
sysmlv2 viz model.sysml --view mixed --color | java -jar plantuml.jar -tsvg -p > model.svg
sysmlv2 lsp                            # the language server over stdio
sysmlv2 parse model.sysml --ast        # debug AST dump
```

Every subcommand's `--help` carries a description and worked examples (enforced by `tests/cli.rs`).

### Standard-library cache

Loading a standard library with `--lib` is cached automatically. The first run prepares its parsed units, resolved graph and static-analysis indexes, then saves a build- and content-identified snapshot at `~/.cache/sysmlv2/stdlib-<hash>.prepared`. A resolution recording (`stdlib-<hash>.libcache`) is saved beside it for the rare builds that must resolve jointly. Later processes load the snapshot without parsing or resolving library sources. Directory-backed SDK sessions can also share a live prepared library across edits. Library snapshots store property and relationship rows in contiguous tables, share decoded property strings, and omit redundant headers from fixed-layout records. Library source text is retained and syntax trees are reconstructed only when requested or needed for joint resolution. Scope names and identity indexes load as checked sorted tables; expression metadata remains available for calculations. Typed graph properties, direct ownership indexes and cached unit/dimension results reduce repeated work. Connector checks reuse the same ownership and binary target indexes as other validators. Static-fact adjacency tables read checked offsets and contiguous values directly; only edited library rows and new model rows need private storage. Each model adds private elements, scopes and index entries over the immutable library prefix; user resolution, semantic checks and import analysis still run. Rust callers use `prepared::load_library_with_cache` for this path; `Model::load_library_dir` parses directly. `Model::units()` requests every syntax tree; `unit_count()` and `is_library_unit(index)` avoid reconstruction, and `unit(index)` requests one tree. `ModelUnit.unit` is `Arc<SourceUnit>`. Root declarations or root-level imports that supply a name the library looked up and missed select a joint build, which replays the recording for every outcome those names cannot reach. Edited libraries, toolkit changes and damaged snapshots trigger rebuilding; an unwritable cache does not prevent analysis. Initial preparation costs more than a warm load. The existing resolution-only snapshot APIs remain available for in-memory library bundles.

Two environment variables control it:

| Variable | Effect |
|---|---|
| `SYSMLV2_CACHE_DIR=<dir>` | relocate the cache (hermetic CI, benchmarking) |
| `SYSMLV2_LIB_CACHE=off` | disable caching for this invocation |

### Ambient libraries and model context

Every model that loads a library also sees the generated Web platform libraries under [local-packages/](local-packages/) (`Web::DOM`, `Web::HTML::Elements`, `Template`, `Svelte`, `WebApp`, `SvelteKit`, `TransformMeta`) without naming their files; `SYSMLV2_AMBIENT=off` switches them off. `SYSMLV2_MODEL_DIR` and `SYSMLV2_LIB_DIR` supply inputs and the library for verbs invoked without file arguments.

### Calculation and static-analysis boundaries

Calculations with expression results, local feature values, and positional or named inputs can be evaluated. Duplicate bindings and missing required inputs fail explicitly; omitted inputs use their own defaults without capturing same-named caller parameters. Bodies requiring assignments, loops, or action execution return `Unsupported`, including direct reads of their output initializers, and are not inlined by the solver. Behavioral execution belongs to a separate layer. Lambda bodies with unmodelled local declarations also fail explicitly.

Dimensional arithmetic is checked from declared quantity types even when parameter values are unbound. Unknown dimensions remain undecided. This check is conservative: it does not yet infer dimensions through arbitrary invocations or lambda bodies. The pinned [OpenSysML negative fixtures](crates/sysmlv2-parser/tests/fixtures/opensysml/) record both diagnostic baselines and remaining gaps; accepting a negative fixture is not counted as validation success.

### Partial models

Work-in-progress models with unresolved references are first-class: `check` reports them as warnings (promote with `--strict`), and full-form JSON and CBOR carry schema-valid recovery annotations by default (standard `TextualRepresentation` elements) so the exact source references are restored on conversion back to text — a partial model committed to a repository round-trips losslessly.

## Crates

The repository is a Cargo workspace. Everything is licensed under Apache-2.0; the bindings ship as a wheel and an npm package.

| Crate | What it provides |
|---|---|
| [`sysmlv2-syntax`](crates/sysmlv2-syntax) | Lexer, hand-written parsers for both dialects, spans, the syntax-faithful AST, printer/formatter, body-context validation |
| [`sysmlv2-model`](crates/sysmlv2-model) | Element graph, name resolution, deterministic and normative element IDs, compact/full JSON interchange in both directions, referential and semantic checks, expression evaluation, constraint verdicts |
| [`sysmlv2-solve`](crates/sysmlv2-solve) | SMT-LIB 2 translation of the decidable constraint fragment, the Z3 subprocess driver (witnesses, proofs), and a solver-free interval propagator |
| [`sysmlv2-lint`](crates/sysmlv2-lint) | Configurable lint rules over the resolved model with optional auto-fixes |
| [`sysmlv2-cbor`](crates/sysmlv2-cbor) | The s2c binary interchange codec: table-driven, deterministic, byte-for-byte reconstructable; elided ids, full-form emit, delta payloads |
| [`sysmlv2-transform`](crates/sysmlv2-transform) | Span-splice transformation engine: semantic navigation, minimal text edits, and a commit pipeline that verifies resolution outcomes are preserved; sessions over text or interchange payloads |
| [`sysmlv2-viz`](crates/sysmlv2-viz) | PlantUML emission, seven views |
| [`sysmlv2-lsp`](crates/sysmlv2-lsp) | The Language Server Protocol server (stdio and an embeddable push-driven core) |
| [`sysmlv2-parser`](crates/sysmlv2-parser) | Compatibility facade re-exporting `sysmlv2-syntax` and `sysmlv2-model` under one crate; hosts the corpus test suites and triage examples |
| [`sysmlv2-cli`](crates/sysmlv2-cli) | The `sysmlv2` binary — every capability above as subcommands, plus `.kpar` project archives, Flexo change-record payloads, and a wasi build for browsers; the verbs are also a library (`run(args)` and one function per verb) so a host drives them in process |
| [`sysmlv2-py`](crates/sysmlv2-py) | Python binding (module `sysmlv2`): the whole session surface — `Session.from_files(...)`, queries, find-usages, batch edits with verified commits — as abi3 wheels via maturin |
| [`sysmlv2-wasm`](crates/sysmlv2-wasm) | WebAssembly/JavaScript binding (`@sysml/wasm`): sessions, checking, interchange, diagrams, and the language server, with the standard library bundled |
| [`sysmlv2-testkit`](crates/sysmlv2-testkit) | Dev-only corpus helpers shared by the workspace's tests and examples (not published) |

Alongside the crates:

- [`editors/vscode`](editors/vscode) — the VS Code extension: semantic highlighting with a TextMate fallback, plus the language-server client.
- [`local-packages/`](local-packages) — the generated ambient libraries and their provenance sidecars; checked-in sources work without a generator.
- [`spec-refs/`](spec-refs) — the pinned normative grammars, JSON schemas, and metamodel XMI, plus the official corpus and an external validation corpus as submodules (see [spec-refs/README.md](spec-refs/README.md)).
- [`tools/`](tools) — the generators for the spec-derived tables (`gen_cbor_tables.py`, `gen_metaclass_hierarchy.py`, `xmi_props.py`), the `SDK.md` doctest runner, and the release and public-export scripts.

## Status

| Capability | State |
|---|---|
| Lexer (shared by both dialects) | ✅ complete, per the normative terminal rules |
| SysML v2 textual grammar | ✅ complete — all definition/usage kinds, connectors, actions, states, transitions, calculations, constraints, requirements, cases, views, metadata, variability |
| KerML textual grammar | ✅ complete — type/feature kinds, standalone relationships, multiplicity declarations, namespaces, function bodies |
| Expression grammar (KerML Expressions) | ✅ complete, exact precedence ladder |
| Corpus gate (`cargo test`) | ✅ **345/345** official files parse clean **and** emit JSON |
| Compact JSON (KerML 10.4) | ✅ flat element array, memberships, relationships, expressions |
| Multi-file models + standard-library resolution | ✅ `model::Model`; 99.92% of corpus references resolve |
| Normative library element IDs (KerML 9.1) | ✅ verified against published OMG XMI |
| Textual printer + formatter (`sysmlv2 fmt`) | ✅ idempotency/semantic/note gates over the corpus |
| `sysmlv2` CLI with example-rich `--help` | ✅ convert / payload / fmt / check / lint / verify / eval / query / render / describe / members / parse / viz / refactor / lsp |
| JSON reader (`lift`) + conversion matrix: text ⇄ compact JSON, full-JSON input normalized | ✅ corpus round-trip gate (`emit∘parse∘print∘lift = id`) |
| Full JSON form (derived props + implied relationships, `--to full-json`) | ✅ 52,048 corpus elements validate against the published schema |
| Binary interchange (`--to compact-cbor` / `full-cbor`, `.s2c`) | ✅ deterministic, byte-for-byte reconstructable; elided ids; digest-verified deltas |
| `.kpar` project archives | ✅ read and write (KerML 10.3) |
| Post-parse validation + referential checks (`sysmlv2 check [--lib]`) | ⚠️ body-context matrix, visibility/ambiguity-aware resolution, and a growing normative-rule registry; 85/180 unique pinned XMI `validate…` names are registered across structural and semantic checks; this is an inventory, not a complete conformance claim |
| Semantic constraints (`check --lib`) | Usage-kind typing, multiplicity types/ranges, specialization cycles, redefinition compatibility, invocation binding, metadata/variation, connector ends and bindings, static action/state contracts, and conservative dimensional arithmetic; official-corpus gate pins two confirmed dimensional defects |
| Configurable lint rules (`sysmlv2 lint`) | ✅ project-policy rules with auto-fixes, configured per project; text or JSON report (`--format json`, shared with `check`) |
| Expression evaluation (`sysmlv2 eval`) | ✅ operators (rational Int division per KFL), sequences, feature refs, featuring contexts, KFL intrinsics + lambdas, quantities (`10 [mm]`), user-defined calc invocation (incl. `return x = expr;`), `new` constructors — 82.8% of corpus feature values compute |
| Constraint verdicts (`sysmlv2 verify`) | ✅ satisfied / violated / undecided per constraint/requirement/invariant body |
| Constraint solving (`sysmlv2 verify --solve`, Z3) | ✅ witnesses for unbound features, unsatisfiability/validity proofs — the `sysmlv2-solve` crate drives the `z3` binary as a subprocess (no libz3 link); interval propagation answers without a solver where it can |
| Ad-hoc model queries (`sysmlv2 query`) | ✅ KerML expressions evaluated at the root namespace, plus query-only extensions: closed-world `istype` on model elements and the reflection functions `ownedMember(x)` / `ownedFeature(x)` — find parts by usage type in one line |
| Transformation engine (`sysmlv2-transform`) | ✅ rename / set value / insert / remove / retarget / extract / inline as span-anchored text splices — notes and formatting preserved byte-for-byte outside the edit; commits reparse, re-resolve, and verify untouched references kept their targets (or roll back), reporting old→new element ids; interchange payloads (compact, full, or Flexo change records) open as sessions and re-emit id-stable |
| PlantUML emission (`sysmlv2 viz`) | ✅ seven views, deterministic, tolerant of unresolved references |
| Language server (`sysmlv2 lsp`) + VS Code extension | ✅ diagnostics, outline, semantic tokens, formatting, navigation, completion, hover, inlay hints, code lenses, refactorings; syntax tier standalone, semantic tier with a library |
| Python binding (`sysmlv2-py`, module `sysmlv2`) | ✅ the whole session surface from Python — abi3 wheels via maturin, generation-guarded handles (stale ones raise instead of mis-resolving) |
| WebAssembly binding (`sysmlv2-wasm`) | ✅ the same session surface plus the language server for browsers and Node, standard library bundled with a sealed resolution snapshot |

The latest implementation gate passed the full default-member release test suite and workspace/all-target Clippy with `-D warnings`. Corpus counts above use the pinned submodules; initialize them to run those gates.

## Architecture and design choices

```
source text ──lexer──▶ tokens ──parser──▶ syntax AST ──build──▶ element graph ──resolve──▶ JSON / CBOR (compact/full)
     ▲                                        │                       │
     └────────── printer / formatter ─────────┘         checks · lint · evaluation · constraint
                                                        verdicts ──undecided──▶ Z3 (solve)
```

**Hand-written recursive descent, not a parser generator.** The normative grammar is LL(\*) with syntactic predicates, ~170 contextual keywords, multi-word keyword sequences (`part def`, `use case def`, `defined by`, `succession flow`), and constructs whose classification needs several tokens of lookahead (`perform a.b;` vs `perform action x {…}`; `if g then t;` vs `if g {…}`). Recursive descent with explicit lookahead and small checkpoint/rewind spots transcribes the Xtext rules almost one-to-one and gives precise diagnostics — the approach of `syn` and rust-analyzer.

**Contextual keywords, per-dialect reservation.** The lexer never classifies keywords: words are `Ident` tokens and the parser matches them by text. Each dialect reserves only its own word set (per Xtext keyword reservation), so `part` is an ordinary KerML name and `struct` an ordinary SysML name — exactly as in the pilot implementation.

**Lexical subtleties taken from the terminals, not folklore.** `/* … */` is a *significant* token (it is the body of `comment`/`doc`/`rep` elements) while `// …` and `//* … */` notes are trivia; real literals are parser-level compositions (`1.5` is three tokens), which is what makes `1..5` lex correctly as a range; `::*`/`::**`/`$::` are token sequences.

**Two-layer model.** The parser produces a *syntax-faithful* AST — what the text says, spans everywhere, cross-references kept as qualified names, one `Definition`/`Usage` struct with kind enums mirroring the grammar's uniform declaration pattern rather than 50 node types. Lowering to the abstract syntax (metaclass instances, `Membership` wrappers, resolved IDs) is a separate build phase. This split keeps "arbitrary model operations" cheap at the syntactic layer and makes the compact-vs-full JSON distinction a property of the build phase, not the parser.

**Superset parsing.** Bodies accept the union of member kinds across contexts (a state member is not rejected inside a part body). Context validation is a semantic-checker concern; keeping it out of the parser simplified the grammar dramatically without losing any conforming model.

**Error tolerance.** Lexer and parser never abort: they emit diagnostics with byte spans (plus a `LineIndex` for line/column) and recover at member boundaries, so one pass reports many errors and the AST remains usable on broken input. Trailing result expressions (`constraint { mass <= limit }`) are disambiguated from member declarations by checkpoint-and-backtrack.

**Name resolution** follows KerML scoping: per scope, owned members (declared *and* short names) → aliases → membership imports → inherited members → namespace imports, with imports followed transitively (re-exports like `ISQ::mass`) and recursively for `::**`. Inherited-member lookup walks explicit specialization/typing targets **plus** the implied library bases of SysML Tables 31/32 (every `action` sees `Actions::Action`'s `start`/`done`) — used for resolution only, never serialized. All paths are cycle-guarded and cached per scope.

**JSON serialization (KerML clause 10.4, compact form).** One flat JSON array per model; each element carries `@type` (exact metaclass name), `@id` = `elementId`, owned properties, and `{"@id": …}` references; no implied relationships (`isImplied: false`, `isImpliedIncluded: false` throughout). Metaclass selection is dialect-aware (a keyword-less feature is a `ReferenceUsage` in SysML but a `Feature` in KerML; `binding` maps to `BindingConnectorAsUsage` vs `BindingConnector`).

**Deterministic and normative IDs.** User-model element IDs are graph-derived: chained UUIDv5 through ownership and names ([`IDS.md`](IDS.md)), so the same source always serializes identically (diffable, snapshot-testable) and every non-root id is recomputable from the interchange graph alone. Standard-library elements get the **normative** IDs of KerML clause 9.1: `uuid5(NameSpace_URL, "https://www.omg.org/spec/{KerML,SysML}/"
+ packageName)` for top-level standard library packages (KerML prefix for kernel libraries, SysML for Systems/Domain libraries), then `uuid5(packageUuid, qualifiedName)` for named elements, with restricted-name escaping (`SI::'ampere per metre'`) — so references in the output are interoperable with any conformant SysML v2 tool.

**Transformations edit text, not trees.** A session navigates the resolved model but every edit is a span-anchored splice into the original source, so formatting and notes outside the edit survive byte-for-byte. A commit reparses and re-resolves, then compares every untouched reference's target before and after; a change that would silently rebind a reference rolls back with a report instead of landing.

## Validation

- **Spec grounding.** The grammars implemented are the normative machine-readable Xtext files of the 2025 formal specifications (KerML 1.0, SysML 2.0, metamodel `20250201`), vendored in [spec-refs/](spec-refs/) together with provenance notes. The JSON mapping follows KerML clause 10.4; owned-vs-derived property decisions come from the published XMI; implied relationships follow KerML 8.4.2 / SysML Tables 31–33.
- **Corpus gate.** Every `cargo test` run parses all **345** official files — the complete OMG standard library (Systems, Domain, and Kernel libraries), all 42 training topics, all examples, and all validation suites — asserting zero diagnostics *and* successful compact-JSON emission for each (139,656 compact elements when files are emitted independently; `examples/jsoncheck` run).
- **External rule fixtures.** [462 pinned OpenSysML fixtures](crates/sysmlv2-parser/tests/fixtures/opensysml/README.md) have per-stage baselines, with 147 paired rejection contracts and one adjudicated acceptance. An unrelated diagnostic does not establish intended-rule coverage.
- **External corpus.** Airbus Central R&T's Apollo 11 mission model — the first substantial model independent of the OMG pilot lineage — is a pinned submodule with its own ratcheted gates (parse, checks, formatter, round-trip, evaluation, constraint verdicts, SMT solving).
- **Resolution coverage.** The `examples/modelcheck` run over 251 non-library corpus files yields 48,251 compact elements, 112,245 resolved `{"@id"}` references and 90 symbolic `{"@ref"}`s (99.92% resolved). `examples/modelcheck` counts 160,496 `@id` occurrences; subtract the 48,251 element declarations to count references only. Feature chains (`a.b.c`) serialize per the normative grammar — an owned `Feature` with one `FeatureChaining` per link — with each link resolved in the previous link's scope (owned + inherited-via-typing members).
- **Full-form schema validation.** `--to full-json` output — implied relationships (normative library targets, anti-redundancy) plus the complete per-metaclass property set generated from the published `SysML.json` — validates for **all 52,048 corpus elements** against the schema's exact-type definitions (`tests/full_json.rs`, `examples/fullcheck`). The representation rules, including the approximations at the API's passthrough level (expression `result`, `inheritedMembership`), are documented in [INTEROP.md](INTEROP.md).
- **Normative-ID test vectors.** Library IDs are verified in [tests/model.rs](crates/sysmlv2-parser/tests/model.rs) against elementIds extracted from the published OMG XMI serializations: `ScalarValues` → `40bb440c-5036-58e1-8675-5afccb8b8f1d`, `ScalarValues::Real` → `14c0aa22-5489-59b5-b438-ded26e83ba31`, `Parts::Part` → `0774a545-39e3-5bc1-9607-63beabc6bf65`. The algorithm (UUIDv5/SHA-1, the RFC 4122 `NameSpace_URL` namespace, escaped qualified names) was confirmed against both the spec text and the pilot implementation's Java source.
- **Round-trip gates.** Text → JSON → text, JSON → CBOR → JSON, and transformation inverses (rename and back, extract then inline) are gated over the corpus so every representation stays faithful to every other.

### Known limitations

- The compact form deliberately does not satisfy the published JSON schemas' `required` lists — those describe the *full* (derived) form, which `--to full-json` produces.
- Body contexts parse as a superset; `sysmlv2 check` closes the gap post-parse (body-context legality, duplicate names, variant ownership, import visibility). Remaining syntax fidelity limits include effect-only transition shorthands and result-expression-last positioning. Metadata-body implicit redefinitions and their static value checks are implemented.
- Unnamed library elements keep deterministic local IDs instead of the normative positional `path()` IDs (never referenced from user text).
- The [generated Web library](local-packages/README.md) has nine invalid attribute typings when checked as user input; its generator mappings need correction. Library-mode loading suppresses those library diagnostics.
- Behavioral execution is not implemented. Calculations that require statement execution return an explicit unsupported error; unbound inputs may yield an indeterminate value. Static action/state checks do not execute behaviors.
- Only the decidable fragment of constraint expressions reaches the SMT translator; the rest stay `undecided` with a stated reason.

## Development

Rust 1.97 or newer is required. Development and CI use the toolchain pinned in `rust-toolchain.toml`.

```sh
git submodule update --init --filter=blob:none   # the corpus (sparse checkout is enough; see spec-refs/README.md)
cargo test                                    # all suites incl. the 345-file corpus gate
cargo clippy --workspace --all-targets -- -D warnings
cargo run --example failstats  -- <dir>       # parse-coverage stats for a corpus dir
cargo run --example failfiles  -- <dir>       # first-diagnostic context per failing file
cargo run --example jsoncheck                 # per-file JSON emission over the corpus
cargo run --example modelcheck                # library-resolved emission + @ref counts
cargo run --example fmtcheck   -- <dir>       # formatter gates with failure context
cargo run --example liftcheck  -- <dir>       # JSON round-trip gate with diffs
cargo run --example fullcheck                 # full-form schema validation, corpus-wide
```

The Python binding builds with `maturin develop` in `crates/sysmlv2-py` (it is outside the workspace's default members so plain `cargo test` never needs a Python toolchain); `tools/sdk_doctour.py` then runs every `pycon` block of `SDK.md` as a doctest. The npm package is assembled by `node crates/sysmlv2-wasm/npm/build.mjs` (wasm-pack, the standard-library bundle, and the wasi CLI).

## License

Apache License 2.0 — Copyright 2026 Open-MBEE (see [LICENSE](LICENSE)). Reference material under `spec-refs/` keeps its upstream licenses (EPL-2.0 grammars, LGPL-3.0 corpus, MPL-2.0 external corpus).
