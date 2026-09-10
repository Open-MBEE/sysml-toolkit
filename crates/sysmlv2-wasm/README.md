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

// Diagnostics: [{severity, message, unit, line, col}].
const findings = JSON.parse(check(sources));

// Sessions: navigation, queries, interchange JSON, diagrams.
const session = Session.fromSources(sources);
const car = session.resolve("Demo::car");
console.log(session.metaclass(car));            // "PartUsage"
const uml = session.toPlantuml(JSON.stringify({ view: "tree" }));
const interchange = session.toFullJson(true);
```

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

`Session.fromInterchangeJson(json, bundle, snapshot)` accepts the same pair for lifting library-typed interchange payloads (Flexo `{payload, identity}` change records included).

## Building from source

`node crates/sysmlv2-wasm/npm/build.mjs` (needs wasm-pack, the `wasm32-unknown-unknown` target, node ≥ 18, and the SysML-v2-Release submodule for the stdlib). Output: `npm/pkg/` (the package) and `npm/dist/sysmlv2-wasm-<version>.tgz`. The tarball is attached to each GitHub release; the package is not published to npm.

[sysmlv2]: https://github.com/Open-MBEE/sysml-toolkit
