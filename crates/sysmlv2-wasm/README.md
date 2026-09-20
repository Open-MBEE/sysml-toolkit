# @sysml/wasm

SysML v2 / KerML toolkit for the browser: parsing, semantic checking, interchange JSON (KerML 10.4 compact + full form), KerML expression queries, and PlantUML diagram emission — the [sysmlv2] Rust toolkit compiled to WebAssembly. No server, no JVM, no Pilot Implementation.

Built with wasm-pack's `web` target: call `init()` once with the module URL, then everything is synchronous. Works in pages, web workers, and bundlers without wasm-specific configuration.

```js
import init, { Session, check, version } from "@sysml/wasm/sysmlv2.js";

await init(new URL("@sysml/wasm/sysmlv2_bg.wasm", import.meta.url));

// Sources cross the boundary as JSON: [{name, text}].
const sources = JSON.stringify([
  { name: "demo.sysml", text: "package Demo { part def Vehicle; part car : Vehicle; }" },
]);

// Diagnostics: [{severity, stage, message, unit, line, col, endLine, endCol}].
const findings = JSON.parse(check(sources));

// Sessions: navigation, queries, interchange JSON, diagrams.
const session = Session.fromSources(sources);
const car = session.resolve("Demo::car");
console.log(session.metaclass(car));            // "PartUsage"
const uml = session.toPlantuml(JSON.stringify({ view: "tree" }));
const interchange = session.toFullJson(true);

// Lint: the same {findings, summary} document `sysmlv2 lint --format json` emits.
const lint = JSON.parse(session.lint(/* sysmlint.json text, optional */));
```

`session.lint(config)` runs the configurable project-policy rules over the session's user units — `config` is `sysmlint.json` text, omitted for every rule at its default — and returns the report document shared with the CLI's `--format json`: each finding carries `rule`, `severity` (`error` / `warn` / `info` / `hint`), `message`, `unit` / `unitName`, byte offsets and 1-based positions, `element`, `suggest`, and any `fix` (byte-offset edits; `deletes` and `semantic` mark fixes to gate behind explicit consent). `lintRules()` lists the rule inventory with defaults, scopes and options.

## Errors

Input the binding can describe is refused by throwing a string: `check`, `Session.fromSources` and every session method reject malformed JSON, unknown options and unresolvable names that way, so `try`/`catch` around a call gets a message you can show.

A defect in the toolkit is different. It aborts the call with `RuntimeError: unreachable` and leaves the module instance trapped — every later call into it fails too, and a session caught mid-edit may be half-mutated. The panic report (message and location) is written to `console.error` as the instance traps, so the console says what happened even though the thrown value does not. **A host that catches a `RuntimeError` must discard the module instance and `init()` a fresh one**; reusing it, or its sessions, is not safe. Reload the sources into the new instance to carry on.

## The standard library

The package ships the OMG standard library under `stdlib/`:

- `sysml-library.json.gz` — the 94 library units as `[{name, text}]` (array order is load order — pass the decompressed text through unchanged).
- `sysml-library.libcache.gz` — a sealed resolution snapshot recorded against exactly that bundle; passing it makes library resolution replay instead of search (several times faster). Stale or corrupt bytes are rejected safely and the build falls back to a cold resolve.
- `manifest.json` — toolkit version, unit count, sizes.

Serve the two `.gz` files statically and load them once (cache them — they change only with the toolkit version):

```js
const gunzip = async (resp) =>
  new Response(resp.body.pipeThrough(new DecompressionStream("gzip")));

const bundle = await (await gunzip(await fetch(stdlibBase + "/sysml-library.json.gz"))).text();
const snapshot = new Uint8Array(
  await (await gunzip(await fetch(stdlibBase + "/sysml-library.libcache.gz"))).arrayBuffer()
);

const findings = JSON.parse(check(sources, bundle, snapshot));   // full semantic checks
const session = Session.fromSources(sources);
session.loadLibrarySources(bundle, snapshot);                    // library-aware navigation
```

Without a bundle, `check(sources)` runs parse and structural checks. Supplying a bundle adds referential and semantic checks; this API does not report unused private imports. Its sealed resolution snapshot is distinct from the native CLI’s directory-backed `.prepared` graph cache.

`Session.fromInterchangeJson(json, bundle, snapshot)` accepts the same pair for lifting library-typed interchange payloads (Flexo `{payload, identity}` change records included).

For repeated builds in a worker, prepare the final library bundle once and share
its immutable graph. Each session keeps its own resolver state:

```js
import { PreparedLibrary, Session } from "@sysml/wasm/sysmlv2.js";
const library = new PreparedLibrary(bundle, snapshot);
const session = Session.fromSourcesWithPreparedLibrary(sources, library);
const findings = JSON.parse(session.check());
library.free(); // the session retains the library through subsequent edits
session.free();
```

Use a new handle when library text or unit order changes. Preparation costs are
paid once per handle, so retain it across builds to amortize them. Existing source
and snapshot APIs remain available. `fromInterchangeJsonWithPreparedLibrary`,
`fromCompactCborWithPreparedLibrary`, and `loadPreparedLibrary` accept the same
handle; attaching a library invalidates existing element handles.

## Running the command-line module

The package ships the toolkit's command line as a `wasm32-wasip1` module under `cli/`, version-locked to the kernel module beside it. It reserves a 16 MiB stack, because the parser's recursion bounds are sized to report a finding on deep input rather than exhaust the stack, and that reservation is the module's declared initial memory.

Run it under **Node 24 or newer**. Node 22 on x86_64 faults inside its own WASI host on a module this shape: over 40 runs of one artifact, 6 ended in a segmentation fault of the node process — not a trap the module can raise, since it imports no means of raising a signal. The rate follows the declared initial memory, and Node 20 and 24 on the same architecture, and Node 22 on arm64, were clean over the same count. The kernel module (`sysmlv2_bg.wasm`), which reserves no such stack, is unaffected.

## Building from source

`node crates/sysmlv2-wasm/npm/build.mjs` (needs wasm-pack, both the `wasm32-unknown-unknown` and `wasm32-wasip1` targets, node ≥ 18 to build and ≥ 24 to run the smokes, and the SysML-v2-Release submodule for the stdlib). Output: `npm/pkg/` (the package) and `npm/dist/sysml-wasm-<version>.tgz`. The release workflow attaches the tarball to tagged releases. It also attempts registry publishing of `@sysml/wasm` on tag/manual runs when `NPM_TOKEN` is configured; otherwise that step is skipped. A local build does not publish.

[sysmlv2]: https://github.com/Open-MBEE/sysml-toolkit

### Reference spelling

`session.qualifiedName(element)` is the specification's derived qualified name:
a reserved word used as a name stays bare (`part::view` for `part 'view';`
inside `package 'part'`), which is also what the normative library ids hash. That
string does not parse as a reference. `session.referenceSpelling(element)` and
the free `spellReference(qualifiedName, dialect?)` quote such segments
(`'part'::'view'`) — omit `dialect` for text that must parse in either dialect,
or pass `"sysml"` / `"kerml"` for a known unit — so use them, not
`qualifiedName`, to generate `import` and `expose` targets.

### Lookup by interchange ID

`session.elementById(id)` returns the same kind of generation-checked handle as
`session.resolve(qualifiedName)`, including for anonymous elements emitted by
`toGraph`. It returns `undefined` for malformed or missing UUIDs. Qualified names
remain absent for genuinely anonymous elements; IDs are not display names.
Library elements can be inspected by ID but remain read-only. Reacquire handles
after an edit or library reload; IDs refer to the current model state and can
change when an element's ownership path changes.
