# Specification references and test corpus

Reference material vendored for grammar fidelity and corpus testing. None of it is compiled into the library.

| Path | What | Source | License |
|---|---|---|---|
| `KerML.xtext` | Normative KerML structural grammar | [SysML-v2-Pilot-Implementation](https://github.com/Systems-Modeling/SysML-v2-Pilot-Implementation) `org.omg.kerml.xtext` (master, fetched 2026-07-08; metamodel 20250201) | EPL-2.0 |
| `KerMLExpressions.xtext` | Normative terminals + expression grammar (shared by both dialects) | same, `org.omg.kerml.expressions.xtext` | EPL-2.0 |
| `SysML.xtext` | Normative SysML v2 textual-notation grammar | same, `org.omg.sysml.xtext` | EPL-2.0 |
| `SysML.schema.json` | Normative abstract-syntax JSON schema (drives the full-form property catalog + validation gates) | https://www.omg.org/spec/SysML/20250201/SysML.json | OMG spec file |
| `KerML.schema.json` | Normative KerML abstract-syntax JSON schema | https://www.omg.org/spec/KerML/20250201/KerML.json | OMG spec file |
| `KerML.xmi` | Normative KerML metamodel XMI — the authoritative owned-vs-derived property split (`isDerived`), defaults, and multiplicities per metaclass (drives the property-audit gate via `tools/xmi_props.py`) | https://www.omg.org/spec/KerML/20250201/KerML.xmi (fetched 2026-07-16) | OMG spec file |
| `SysML.xmi` | Normative SysML v2 metamodel XMI (93 classes generalizing into `KerML.xmi` by href) | https://www.omg.org/spec/SysML/20250201/SysML.xmi (fetched 2026-07-16) | OMG spec file |
| `SysML-v2-Release/` | Test corpus: `sysml.library/` (standard + domain + kernel libraries), `sysml/src/{examples,training,validation}` — git submodule; a sparse, blob-filtered checkout of those four directories is enough (`git submodule update --init --filter=blob:none spec-refs/SysML-v2-Release`, then `git -C spec-refs/SysML-v2-Release sparse-checkout set sysml.library sysml/src/examples sysml/src/training sysml/src/validation`) — the corpus gates read only them | [SysML-v2-Release](https://github.com/Systems-Modeling/SysML-v2-Release) | LGPL-3.0 |
| `apollo-11-sysml-v2/` | External validation corpus: Airbus Central R&T's Apollo 11 mission model (28 files, five-layer CoSMA framework) — git submodule, the first substantial model independent of the OMG pilot lineage; gates in `tests/apollo.rs` skip when uninitialized | [airbus/apollo-11-sysml-v2](https://github.com/airbus/apollo-11-sysml-v2) | MPL-2.0 |

Related normative documents (not vendored):

- KerML 1.0 — https://www.omg.org/spec/KerML/ (clause 8.2 concrete syntax, 8.3 abstract syntax, 8.4.2 implied relationships, 9.1 library UUIDs, 10.4 JSON serialization)
- SysML 2.0 — https://www.omg.org/spec/SysML/
- Systems Modeling API & Services 1.0 — https://www.omg.org/spec/SystemsModelingAPI/
- Machine-readable schemas/XMI: `https://www.omg.org/spec/{KerML,SysML,SystemsModelingAPI}/20250201/`
