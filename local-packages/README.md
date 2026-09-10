# Generated SysML libraries

Every `.sysml` file here is a library the toolkit carries **ambiently**: `sysmlv2 check --lib`, `lint`, `query`, the language server, and the browser kernel's standard-library bundle load them after the standard library, so a model may reference `Web::DOM::Element`, `Web::HTML::Elements::Div`, `Template::EachBlock` or `Svelte::OnDirective` without naming a file. Only `TransformMeta.sysml` is maintained by hand.

| file | contents | generated from |
|---|---|---|
| `Web.sysml` | `Web::DOM`, `Web::HTML`, `Web::HTML::Elements` | the standards' machine-readable WebIDL corpus and HTML element metadata (`@webref/idl`, `@webref/elements`, pinned in the generator's `package.json`) |
| `Template.sysml` | the engine-neutral template core | the component-template compiler's public AST declarations (`svelte`, pinned) through the generator's core schema (`src/template.mjs`) |
| `Svelte.sysml` | the compiler's overlay | the same declarations, mechanically |
| `WebApp.sysml` | the framework-neutral application layer (entries, assets, navigation) | the generator's application schema (`src/template.mjs`) |
| `SvelteKit.sysml` | the route/SSR overlay (route tree, roles and loci, declared render policies, hooks, matchers, boundary diagnostics, adapter) | the generator's route schema (`src/template.mjs`) |
| `*.provenance.json` | per-element provenance (spec, interface, member, URL, IDL type, dataset revisions) | the generator |

Never edit the generated files: regenerate them.

## Reproducing the libraries

The generator is the separate `websysml` repository (not yet published). It expects this toolkit checked out as a sibling directory named `sysmlv2` (or `SYSMLV2_ROOT` pointing at it) and writes into this directory.

Prerequisites: Node 22.3 or newer, the Rust toolchain with the `wasm32-unknown-unknown` target, and `wasm-pack` (the wasm crate's `npm/` folder installs one).

```bash
# 1. In this repository: the kernel the generator validates through —
#    the nodejs wasm build and the standard-library bundle (once, and
#    after toolkit changes).
node crates/sysmlv2-wasm/npm/build.mjs

# 2. In the websysml checkout: the generator's pinned inputs (corpus
#    packages, compiler, parser), then regenerate every library and
#    sidecar into this directory. The generator refuses to write
#    anything that is not strict-check-clean against the standard
#    library or not formatter-idempotent.
npm ci
npm run generate

# 3. Verify, as CI does: outputs current, tests green (in websysml) …
node src/cli.mjs generate --check
npm test

# … and the CLI gates (in this repository).
SYSMLV2_AMBIENT=off cargo run --release -p sysmlv2-cli -- check --strict --lib spec-refs/SysML-v2-Release/sysml.library local-packages/Web.sysml local-packages/Template.sysml local-packages/Svelte.sysml local-packages/WebApp.sysml local-packages/SvelteKit.sysml
cargo run --release -p sysmlv2-cli -- fmt --check local-packages/Web.sysml local-packages/Template.sysml local-packages/Svelte.sysml local-packages/WebApp.sysml local-packages/SvelteKit.sysml
```

`SYSMLV2_AMBIENT=off` keeps the toolkit's built-in copies out of a check, so a regenerated file can be validated as a candidate (and so `sysmlv2` can run against a bare standard library when wanted). The generator's own tests do the same through a core-only kernel bundle.

To take a newer corpus or compiler, bump the exact version in the generator's `package.json`, run `npm install` there, regenerate, and review the diff: the goldens in the generator's `test/` directory and the sidecars make every change visible. The library headers name the dataset revisions they were generated from.

The generator's README documents the pipeline, scope, options, and the document/template import commands.
