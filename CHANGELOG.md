# Changelog

## v0.9.1

- Added summary mode for large tree graphs: collapsed containers report hidden element counts, references to hidden elements are grouped with counts, and excess notes are counted on their targets.
- Added configurable member and note limits, with per-container overrides to show every direct member.
- Added WebAssembly controls to expand containers by qualified name or element ID, report unresolved selections, and reveal an element's containing path with `revealPath`.
- Included the pinned Rust toolchain configuration in the public source release.

## v0.9.0

### Added

- Derived-property access in Rust, Python, and WebAssembly for names, ownership, annotations, types, connector ends, behaviors, expressions, requirements, and views. Property catalogs report which values are exact, approximate, or not computed.
- Optional inheritance and import closures in derived properties and full-form export, including implied library inheritance. Closure expansion is opt-in.
- JSON reports for `check` and `lint`, with consistent positions, stages, severities, rule identifiers, fixes, and summary counts.
- Checks for conflicting inherited member names, an `inherited-name-shadow` lint with a redefinition fix, and editor actions to fix all findings of one rule.
- Editor requests to preview and apply package splitting: `sysmlv2/splitPlan` and `sysmlv2/split`.
- Reusable prepared libraries across in-memory sessions, including a WebAssembly `PreparedLibrary` handle, and reusable parsed-source inputs for validation.
- Session checks reuse the session's resolved model without changing lint or unused-import findings; syntax-only checks are available separately.
- Python `Error` and `RefusedError` exceptions; Python checks release the interpreter lock while running.

### Fixed

- Interchange sessions preserve supplied element IDs across loading, edits, and export. Compact and full forms retain the same identities, including references to external elements.
- JSON and CBOR round trips preserve long expressions and owned element graphs. Cycles, excessive depth, and incomplete reconstruction report errors instead of silently dropping content.
- Numeric literals that exceed JSON numeric precision retain their exact text. Full-form output preserves external references and derives names, implied relationships, and connector structure consistently.
- Evaluation keeps type defaults unknown through unbound subjects, references, and inputs, including aliases, nested members, and calculation calls. Fixed formulas use the receiver's redefinitions; unsupported nested solver paths remain undecided.
- Parser handling of accept actions, conditional triggers, `else` branches, word-operator operands, and escaped names and strings. Binding and connector printing preserves ends in both dialects, including one-ended and multi-ended bindings.
- Deep nesting and long operator chains produce bounded diagnostics; parsing entry points reserve sufficient stack space and report reservation failures. Evaluation budgets cover all materialized values.
- Refactorings reject edits to library declarations and blank source names, avoid conflicting renames and overlapping qualification edits, and remove whole member lines correctly with either line ending. Inferred typing fixes account for values and redefinitions.
- Language-server sessions survive malformed requests and recoverable panics, report model and library failures, handle encoded file paths and large offsets correctly, and process documents in a stable order.
- Model-file extensions are recognized regardless of case. CLI output handles closed pipes quietly, and project archives validate offsets and total expanded size.
- Library caches handle concurrent writes and invalid data safely, with clearer failures and fewer repeated warnings.
- CBOR readers reject malformed references, invalid map lengths, and out-of-range integers and type codes without panicking or truncating values.
- Solver propagation continues tightening one-sided ranges, supports enumerations beyond 128 literals, and avoids repeated operand evaluation. Solver failures preserve their causes and clean up child processes.
- Diagram labels, notes, and links escape line breaks, backslashes, and delimiters correctly.
- Generated web libraries pass inherited-name checks; displayed element names follow the specification's naming rules.

### Performance

- Reduced repeated parsing, graph construction, metaclass lookup, import resolution, and full-form export work. Linting, editor diagnostics, binary conversion, and diagram generation reuse indexes and shared data.

### Upgrade notes

- Rust 1.97 or newer is required. Development and WebAssembly package builds use the pinned toolchain.
- Rust diagram options use default construction and setters. Several public error and result types are now typed or non-exhaustive; callers may need updated matches and error handling.
- Compact CBOR marks explicit IDs with a new flag. Sessions with explicit IDs reject ID-elided snapshots and delta export.
- JSON consumers must accept numeric literal values as either numbers or exact-text strings; the string form is a documented departure from the interchange schema.

## v0.8.0

### Added

- Guided lint repairs for incompatible usage kinds, composite port members, unqualified enumeration literals, inaccessible private members, and import visibility, with editor quick fixes and a fix-all action.
- Package splitting into per-child files through the transformation API, `refactor split`, and editor move actions.
- Opt-in repair of parse-broken sources for session construction, with records of removed or appended text and any unrepaired units.
- Diagnostic stages distinguish parse, context, reference-resolution, and semantic findings.
- Inherited-member enumeration and dialect-aware reference spelling in the model API and bindings.
- WebAssembly view information and view-directed diagrams based on exposed elements.

### Fixed

- Generated references and edits quote reserved words for the source dialect.
- Named dependencies, documentation, comments, and textual representations resolve in their namespaces. Inheritance and recursive imports respect lookup precedence and import order.
- Full-form interchange derives ownership, annotation endpoints, and type multiplicity correctly.
- Diagrams resolve library renderings, retain explicitly inherited library ports, omit generic implied ports, and draw nothing for views with no exposed elements.
- Anonymous comments keep their indentation; editor symbols always have nonempty labels; CLI diagnostics handle multibyte text safely.
- Diagnostic rendering and full-form relationship export reuse indexes to reduce repeated work.

## v0.7.2

- Constraint propagation uses exact rational interval endpoints, preserving decimal bounds without rounding drift. Solver witnesses also retain exact rational values.
- Editor and WebAssembly range reports provide marked approximate decimals alongside exact ranges.
- **Rust API change:** `WitnessValue::Real` now carries a rational value.

## v0.7.1

- Fixed diagram occurrence endpoints and implicit action succession, preserving the identity of connected elements.

## v0.7.0

### Added

- Exact rational arithmetic for numeric evaluation, comparisons, unit scales, and solver literals, exposed through Python and WebAssembly. Editor hints mark approximate displays of non-terminating decimals.
- Broader static checks for typing, dimensions, structure, relationships, expressions, connector accessibility, and action/state contracts, plus warnings for declarations that shadow standard-library roots.
- Evaluation limits for steps, ranges, strings, cumulative allocation, and exact-number size.
- WebAssembly lookup of anonymous elements by interchange ID.

### Fixed

- Anonymous redefinitions no longer target sibling declarations. KerML feature chains resolve in the preceding feature's context, and indexing is distinguished from quantity diagnostics.
- Full-form export includes effective qualified names for redefined elements and correct library-element flags. Calculation results receive typing and dimension checks.
- WebAssembly packaging selects the current package when older archives are present; generated web attributes with unrestricted types use `Base::DataValue`.

### Performance

- Prepared library graphs, shared lookup tables, deferred syntax loading, and compact semantic storage reduce library startup, memory use, and repeated validation work. Connector and unused-import checks reuse indexes; failed cache saves warn once per process.
