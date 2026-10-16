# Ambient libraries

Libraries the toolkit carries **ambiently**: `sysmlv2 check --lib`, `lint`, `query`, the language server, and the browser kernel's standard-library bundle load them after the standard library, so a model may reference their members without naming the files. They are maintained by hand; `crates/sysmlv2-model/src/ambient.rs` is their build-time mirror.

- `TransformMeta.sysml` — the metadata vocabulary that generated elements and their provenance records are annotated with (`#TransformMeta::Generated` on a generated element, `#TransformMeta::ProvenanceStore` on the package holding the records); the lint's generated-element checks read these annotations.
- `StringPatterns.sysml` — `Pattern`, the metadata that names the lexical form of a string-encoded attribute definition (`regex`, an optional broader `accepts` form reported at a reduced severity, and a human-readable `form`), applied in the definition's body or `about` a definition the annotating package does not own. It carries the application for the standard library's `Time::Iso8601DateTimeEncoding`, whose format the standard library states only in documentation. The `literal-pattern` lint reads these annotations.

`SYSMLV2_AMBIENT=off` keeps the built-in copies out of a run, so an edited copy can be checked as a candidate without the two colliding:

```sh
SYSMLV2_AMBIENT=off cargo run --release -p sysmlv2-cli -- check --strict --lib spec-refs/SysML-v2-Release/sysml.library local-packages/TransformMeta.sysml
SYSMLV2_AMBIENT=off cargo run --release -p sysmlv2-cli -- check --strict --lib spec-refs/SysML-v2-Release/sysml.library local-packages/StringPatterns.sysml
```
