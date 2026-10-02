# Ambient library

`TransformMeta.sysml` is a library the toolkit carries **ambiently**: `sysmlv2 check --lib`, `lint`, `query`, the language server, and the browser kernel's standard-library bundle load it after the standard library, so a model may reference `TransformMeta::Generated` or `TransformMeta::TransformProvenance` without naming the file. It is the metadata vocabulary that generated elements and their provenance records are annotated with (`#TransformMeta::Generated` on a generated element, `#TransformMeta::ProvenanceStore` on the package holding the records); the lint's generated-element checks read these annotations. It is maintained by hand.

`SYSMLV2_AMBIENT=off` keeps the built-in copy out of a run, so an edited copy can be checked as a candidate without the two colliding:

```sh
SYSMLV2_AMBIENT=off cargo run --release -p sysmlv2-cli -- check --strict --lib spec-refs/SysML-v2-Release/sysml.library local-packages/TransformMeta.sysml
```
