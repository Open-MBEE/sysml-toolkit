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

## Using and validating the libraries

The generated sources and provenance sidecars are included in this repository. No generator is needed to use them. Dataset revisions and per-element origins are recorded in the file headers and sidecars; do not edit generated sources by hand. The generation tool is not distributed with this repository.

With the standard-library submodule initialized, validate the checked-in sources locally:

```sh
SYSMLV2_AMBIENT=off cargo run --release -p sysmlv2-cli -- check --strict --lib spec-refs/SysML-v2-Release/sysml.library local-packages/Web.sysml local-packages/Template.sysml local-packages/Svelte.sysml local-packages/WebApp.sysml local-packages/SvelteKit.sysml
cargo run --release -p sysmlv2-cli -- fmt --check local-packages/Web.sysml local-packages/Template.sysml local-packages/Svelte.sysml local-packages/WebApp.sysml local-packages/SvelteKit.sysml
```

Both commands pass clean. Two earlier candidate-validation failures are closed — the `Base::Anything` attribute typings, and an operation repeating a name inherited through a mixin, which the generator now leaves to the inherited declaration and records in the sidecar's omission ledger. Do not suppress a check or patch generated files by hand: correct the generator, then regenerate sources and provenance together. Library-mode loading suppresses library diagnostics, so ordinary consumers never see a candidate-validation failure.

`SYSMLV2_AMBIENT=off` keeps the toolkit’s built-in copies out of a check, so these files are validated as candidates. It also allows analysis against a bare standard library.
