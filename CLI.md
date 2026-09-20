# `sysmlv2` CLI tour

A tour of every `sysmlv2` subcommand using real models from the OMG SysML-v2-Release corpus vendored under `spec-refs/`. Every output shown here is the actual output of the command above it.

Setup — build the CLI and set two shell variables used throughout:

```console
$ cargo build --release
$ sysmlv2=target/release/sysmlv2
$ corpus="spec-refs/SysML-v2-Release"
```

The centerpiece example is the SysML v2 specification's own Annex A vehicle model — 1,581 lines covering parts, ports, interfaces, actions, states, requirements, use cases, analysis cases, variability, and views:

```console
$ vehicle="$corpus/sysml/src/examples/Vehicle Example/SysML v2 Spec Annex A SimpleVehicleModel.sysml"
```

---

## 1. `parse` — syntax check one file

```console
$ $sysmlv2 parse "$vehicle"
spec-refs/SysML-v2-Release/sysml/src/examples/Vehicle Example/SysML v2 Spec Annex A SimpleVehicleModel.sysml: 1 top-level member(s), 0 diagnostic(s)
```

Exit code 0 on a clean parse, 1 if there are diagnostics. Both dialects are supported; the dialect is chosen by extension (`.kerml` → KerML), and extensions are matched whatever case they are spelled in (`Model.SysML` is a model source, `Lib.KerML` is KerML):

```console
$ $sysmlv2 parse "$corpus/sysml.library/Kernel Libraries/Kernel Data Type Library/ScalarValues.kerml"
spec-refs/SysML-v2-Release/sysml.library/Kernel Libraries/Kernel Data Type Library/ScalarValues.kerml: 1 top-level member(s), 0 diagnostic(s)
```

### Dump the syntax tree

`--ast` pretty-prints the syntax-faithful AST. `-` reads stdin anywhere a file path is accepted:

```console
$ printf 'part def Vehicle {\n    attribute mass : ISQ::MassValue;\n}\n' | $sysmlv2 parse - --ast
SourceUnit {
    dialect: Sysml,
    members: [
        Member {
            visibility: None,
            leading_then: false,
            kind: Definition(
                Definition {
                    prefix: DefPrefix { ... },
                    kind: Part,
                    id: Identification {
                        short_name: None,
                        name: Some(Name { value: "Vehicle", span: 9..16 }),
                    },
                    ...
```

---

## 2. `check` — static validation

`check` reports parse diagnostics, validates body contexts on cleanly parsed files, then resolves those files together and runs referential and semantic checks. These local checks run even without `--lib`; supply the library to resolve standard types and enable unused-private-import warnings. Structural checks include member legality, duplicate names, `variant` ownership, and import visibility. `--strict` fails on warnings as well as errors.

A self-contained model is clean without a library:

```console
$ printf 'package Demo { part def Vehicle; part car : Vehicle; }\n' > clean.sysml
$ $sysmlv2 check clean.sysml
$ echo $?
0
```

A file that parses fine but breaks context rules:

```sysml
package Demo {
    import Definitions::*;

    part def Vehicle {
        transition first parked then driving;
        subject v;
    }
    part def Gearbox {
        variant part manual;
    }
}
```

```console
$ $sysmlv2 check broken.sysml
error: an import must declare an explicit visibility (`public`, `private`, or `protected`)
  --> broken.sysml:2:5
   |
   |     import Definitions::*;

error: a transition usage is not allowed in a definition or usage body
  --> broken.sysml:5:9
   |
   |         transition first parked then driving;

error: validateSubjectMembershipOwningType: a `subject` member is not allowed in a definition or usage body
  --> broken.sysml:6:9
   |
   |         subject v;

error: a `variant` member is only allowed in the body of a `variation` definition or usage
  --> broken.sysml:9:9
   |
   |         variant part manual;

warning: unresolved reference `Definitions`
  --> broken.sysml:2:12
   |
   |     import Definitions::*;

warning: unresolved reference `parked`
  --> broken.sysml:5:26
   |
   |         transition first parked then driving;

warning: unresolved reference `driving`
  --> broken.sysml:5:38
   |
   |         transition first parked then driving;

3 warning(s)
4 error(s)
$ echo $?
1
```

The legality matrix is transcribed from the normative Xtext grammars' `*BodyItem` rules and is gated at zero false positives over all 345 corpus files (`tests/check.rs`).

### Referential checks (`--lib`)

With `--lib`, all input files form one model resolved against the standard library, and unresolved references, missing alias targets and import cycles are **warnings**; ambiguous references are **errors**. Without `--lib`, local references are still checked and missing standard-library dependencies may produce warnings. Warnings affect the exit code only with `--strict`:

```sysml
package Demo {
    private import ScalarValues::*;
    private import Missing::*;

    part def Vehicle {
        attribute mass : Real;
        attribute speed : Vel;
    }
    alias v for Vehicel;
    package A { public import B::*; }
    package B { public import A::*; }
}
```

```console
$ $sysmlv2 check refs.sysml --lib "$corpus/sysml.library"
warning: unresolved reference `Missing`
  --> refs.sysml:3:20
   |
   |     private import Missing::*;

warning: unresolved reference `Vel`
  --> refs.sysml:7:27
   |
   |         attribute speed : Vel;

warning: alias target `Vehicel` does not resolve
  --> refs.sysml:9:17
   |
   |     alias v for Vehicel;

warning: circular namespace import: `B` transitively imports this namespace back
  --> refs.sysml:10:31
   |
   |     package A { public import B::*; }

warning: circular namespace import: `A` transitively imports this namespace back
  --> refs.sysml:11:31
   |
   |     package B { public import A::*; }

5 warning(s)
$ echo $?
0
```

(Run against the corpus, the only import cycles found are the deliberate `CircularImport.sysml` test fixture — gated by `tests/check.rs::corpus_referential_ratchet`.)

A root package (or any other root declaration) named like a standard-library root package is reported at its declaration: the diagnostic states whether references resolve to the library or the name is ambiguous. In the following package collision, the library wins qualified lookup.

```sysml
package Requirements {
    requirement def Speed;
}
package Uses {
    requirement s : Requirements::Speed;
}
```

```console
$ $sysmlv2 check shadow.sysml --lib "$corpus/sysml.library"
warning: root package `Requirements` shadows the standard library package `Requirements`; references resolve to the library
  --> shadow.sysml:1:9
   |
   | package Requirements {

warning: unresolved reference `Requirements::Speed`
  --> shadow.sysml:5:21
   |
   |     requirement s : Requirements::Speed;

2 warning(s)
```

Nesting the package under a differently named root, or renaming it, clears both warnings.

### Semantic constraints (`--lib`)

Semantic checks run with or without a library; `--lib` supplies additional type and relationship information. The example below exercises multiplicity bounds (evaluated with the expression evaluator, so a bound can be an expression), self/circular specialization (errors), and duplicate specialization targets (warnings). Errors are raised only for what is *provably* wrong — a symbolic bound the evaluator cannot compute stays silent:

```sysml
package Demo {
    part def Wheel;
    part def Cyclic :> Cyclic;
    part def A :> B;
    part def B :> A;
    part def Cart :> Wheel, Wheel;
    attribute spares = 2 - 3;
    part wheels : Wheel [5..2];
    part spare : Wheel [spares];
}
```

```console
$ $sysmlv2 check sem.sysml --lib "$corpus/sysml.library"
error: `Cyclic` cannot specialize itself
  --> sem.sysml:3:24
   |
   |     part def Cyclic :> Cyclic;

error: circular specialization: this definition transitively specializes itself
  --> sem.sysml:4:19
   |
   |     part def A :> B;

error: circular specialization: this definition transitively specializes itself
  --> sem.sysml:5:19
   |
   |     part def B :> A;

warning: duplicate specialization of `Wheel`
  --> sem.sysml:6:29
   |
   |     part def Cart :> Wheel, Wheel;

error: multiplicity lower bound 5 exceeds upper bound 2
  --> sem.sysml:8:25
   |
   |     part wheels : Wheel [5..2];

error: multiplicity upper bound is negative
  --> sem.sysml:9:24
   |
   |     part spare : Wheel [spares];

1 warning(s)
5 error(s)
```

Note the last finding: `[spares]` is provably negative only because the evaluator computed `2 - 3`. The official semantic gate pins two dimensional findings in Turbojet Stage Analysis and VehicleGeometryAndCoordinateFrames (`tests/check.rs`, `examples/semstats`). Additional checks cover usage typing, redefinitions, metadata, valuation, invocation binding, dimensions, connector ends, and static action/state contracts. Unknown values stay conservative; behavioral execution is outside this checker.

With `--lib`, the CLI also reports unused private imports. The analysis combines resolution provenance with enclosing-owner and source-text evidence, so uncertain usage is retained conservatively. Public imports are not candidates because they can re-export names for other models. This is a warning, promoted to failure by `--strict`.

### `--format json` — one report document

`--format json` writes the findings as one JSON document on stdout instead of the text above on stderr; the exit code is unchanged and the count lines are not printed. Every item carries the same keys whichever verb produced it — `lint --format json` ([2a](#2a-lint--project-policy-rules)) emits the same shape: `stage` (`parse`, `context`, `referential` or `semantic`), `severity` in the lint config spelling (`error` / `warn` / `info` / `hint`), the `message`, the input's index and name (`unit`, `unitName`), byte offsets (`start`, `end`), 1-based positions (`line`, `col`, `endLine`, `endCol`), and the lint-only fields (`rule`, `element`, `suggest`, `fix`, `alternatives`) as null or empty:

```console
$ printf 'package Q { part x : ; }\n' > broken.sysml
$ $sysmlv2 check --format json broken.sysml
{
  "findings": [
    {
      "alternatives": [],
      "col": 22,
      "element": null,
      "end": 22,
      "endCol": 23,
      "endLine": 1,
      "fix": null,
      "line": 1,
      "message": "expected a name, found `;`",
      "rule": null,
      "severity": "error",
      "stage": "parse",
      "start": 21,
      "suggest": null,
      "unit": 0,
      "unitName": "broken.sysml"
    }
  ],
  "summary": {
    "errors": 1,
    "hints": 0,
    "infos": 0,
    "warnings": 0
  }
}
$ echo $?
1
```

A clean run is an empty `findings` array with a zeroed summary. Over several inputs `unit` indexes the files as given, so a consumer attributes each finding without parsing paths:

```console
$ $sysmlv2 check --format json clean.sysml
{
  "findings": [],
  "summary": {
    "errors": 0,
    "hints": 0,
    "infos": 0,
    "warnings": 0
  }
}
$ $sysmlv2 check --format json clean.sysml broken.sysml | jq -c '.findings[] | {stage, severity, unit, unitName, line, col}'
{"stage":"parse","severity":"error","unit":1,"unitName":"broken.sysml","line":1,"col":22}
```

Operational failures — an unreadable input, a library that fails to load — still go to stderr with exit 1 and no document.

---

## 2a. `lint` — project-policy rules

`lint` reports what `check` deliberately does not: style, hygiene and dead-model findings that are project policy rather than language law. It runs beside `check` and never changes its verdicts, sees only the user units (library elements are never linted, even with `--lib`), and sorts findings by unit, position and rule. Given `rig.sysml`:

```sysml
package Rig {
    part def Wheel;
    part def spare_wheel;
    part axle : Wheel;
    calc def Torque {
        in force : Real;
        in radius : Real;
        return t : Real = force * 2;
    }
}
```

Without configuration, only the rules with a non-off default speak — here the casing nudge:

```console
$ $sysmlv2 lint rig.sysml
warning: definition name `spare_wheel` should be PascalCase [naming-convention]
  --> rig.sysml:3:14
   |
   |     part def spare_wheel;

1 warning(s)
$ echo $?
0
```

Every finding names its rule in brackets. The text report has two severities — `info` and `hint` findings print as `warning:` and count as warnings — while the JSON report below keeps the exact severity. `--rule ID=LEVEL` switches a rule on for one run (repeatable; it wins over the config file):

```console
$ $sysmlv2 lint --rule unused-parameter=warn --rule unused-definition=warn rig.sysml
warning: definition name `spare_wheel` should be PascalCase [naming-convention]
  --> rig.sysml:3:14
   |
   |     part def spare_wheel;

warning: `spare_wheel` is never referenced in these units (closed world: outside consumers are not visible to lint) [unused-definition]
  --> rig.sysml:3:14
   |
   |     part def spare_wheel;

warning: `Torque` is never referenced in these units (closed world: outside consumers are not visible to lint) [unused-definition]
  --> rig.sysml:5:14
   |
   |     calc def Torque {

warning: input parameter `radius` of `Torque` is never used [unused-parameter]
  --> rig.sysml:7:12
   |
   |         in radius : Real;

4 warning(s)
```

### Configuration — `sysmlint.json`

Project policy lives in a JSON file: `{"rules": {"<id>": <level> | {"severity": <level>, "scopes": {"<Metaclass>": …}, …options}}}` where a level is `off`, `hint`, `info`, `warn` or `error`. Every rule accepts `scopes`, the same knob at stereotype granularity — a metaclass name maps to a level or to an object with rule-specific keys (naming's `style` / `regex`, undocumented's `depth`); an element's effective severity is its scope's, else the rule's base. `--config` names the file; without it, a `sysmlint.json` beside the first input is picked up automatically:

```console
$ cat > sysmlint.json <<'EOF'
{
    "rules": {
        "naming-convention": "off",
        "unused-parameter": "warn",
        "unused-definition": { "severity": "warn", "scopes": { "CalculationDefinition": "off" } }
    }
}
EOF
$ $sysmlv2 lint rig.sysml
warning: `spare_wheel` is never referenced in these units (closed world: outside consumers are not visible to lint) [unused-definition]
  --> rig.sysml:3:14
   |
   |     part def spare_wheel;

warning: input parameter `radius` of `Torque` is never used [unused-parameter]
  --> rig.sysml:7:12
   |
   |         in radius : Real;

2 warning(s)
```

The scope silenced the unused `calc def` while the `part def` still reports. A typo'd rule id or option is a finding (`lint-config`, without a location), never a silent ignore:

```console
$ $sysmlv2 lint --rule no-such=warn rig.sysml
warning: unknown lint rule `no-such` [lint-config]
warning: `spare_wheel` is never referenced in these units (closed world: outside consumers are not visible to lint) [unused-definition]
  --> rig.sysml:3:14
   |
   |     part def spare_wheel;

2 warning(s)
```

Warnings exit 0; `error`-level findings exit 1, and `--strict` fails on any finding at all (infos and hints included):

```console
$ $sysmlv2 lint --strict rig.sysml
warning: `spare_wheel` is never referenced in these units (closed world: outside consumers are not visible to lint) [unused-definition]
  --> rig.sysml:3:14
   |
   |     part def spare_wheel;

warning: input parameter `radius` of `Torque` is never used [unused-parameter]
  --> rig.sysml:7:12
   |
   |         in radius : Real;

2 warning(s)
--strict: warnings are failures
$ echo $?
1
```

### `--fix` — applying the fixes

Findings that carry a fix are applied in place by `--fix`, except the two guarded kinds: fixes that *delete* model text (an unused parameter's fix removes its declaration) additionally need `--fix-deletes`, and fixes that change what a declaration *means* (a usage keyword, a member's visibility) need `--fix-semantic`. Refused fixes are counted on stderr; every rewritten file must reparse cleanly before it is written back:

```console
$ $sysmlv2 lint --fix rig.sysml
warning: `spare_wheel` is never referenced in these units (closed world: outside consumers are not visible to lint) [unused-definition]
  --> rig.sysml:3:14
   |
   |     part def spare_wheel;

warning: input parameter `radius` of `Torque` is never used [unused-parameter]
  --> rig.sysml:7:12
   |
   |         in radius : Real;

1 deletion fix(es) available but not applied — deleting model text needs --fix --fix-deletes
2 warning(s)
$ $sysmlv2 lint --fix --fix-deletes rig.sysml
warning: `spare_wheel` is never referenced in these units (closed world: outside consumers are not visible to lint) [unused-definition]
  --> rig.sysml:3:14
   |
   |     part def spare_wheel;

warning: input parameter `radius` of `Torque` is never used [unused-parameter]
  --> rig.sysml:7:12
   |
   |         in radius : Real;

fixed: rig.sysml
2 warning(s)
$ cat rig.sysml
package Rig {
    part def Wheel;
    part def spare_wheel;
    part axle : Wheel;
    calc def Torque {
        in force : Real;
        return t : Real = force * 2;
    }
}
```

The report still lists the findings the fixes addressed — it describes the input as read; the deleted line is gone from the file. Stdin (`-`) and archive members are linted but never written.

### `--format json` — one report document

`--format json` writes one JSON document on stdout — the same shape as `check --format json` above — and prints nothing else: each finding carries its `rule`, the exact `severity`, `element` (the engine's edit-target spelling, a `::`-qualified name or `@<id>` for anonymous elements), `suggest` (a naming finding's re-spelled name) and `fix` / `alternatives` with byte-offset `edits` over the unit's text, so a host can apply or offer them itself. The exit status stays the text mode's (`--strict`, refused fixes), which the summary's per-severity counts do not encode. Before the fix above:

```console
$ $sysmlv2 lint --format json rig.sysml
{
  "findings": [
    {
      "alternatives": [],
      "col": 14,
      "element": "Rig::spare_wheel",
      "end": 58,
      "endCol": 25,
      "endLine": 3,
      "fix": null,
      "line": 3,
      "message": "`spare_wheel` is never referenced in these units (closed world: outside consumers are not visible to lint)",
      "rule": "unused-definition",
      "severity": "warn",
      "stage": "lint",
      "start": 47,
      "suggest": null,
      "unit": 0,
      "unitName": "rig.sysml"
    },
    {
      "alternatives": [],
      "col": 12,
      "element": "Rig::Torque::radius",
      "end": 147,
      "endCol": 18,
      "endLine": 7,
      "fix": {
        "deletes": true,
        "edits": [
          {
            "end": 155,
            "replacement": "",
            "start": 138,
            "unit": 0,
            "unitName": "rig.sysml"
          }
        ],
        "label": "delete unused parameter `radius`",
        "semantic": false
      },
      "line": 7,
      "message": "input parameter `radius` of `Torque` is never used",
      "rule": "unused-parameter",
      "severity": "warn",
      "stage": "lint",
      "start": 141,
      "suggest": null,
      "unit": 0,
      "unitName": "rig.sysml"
    }
  ],
  "summary": {
    "errors": 0,
    "hints": 0,
    "infos": 0,
    "warnings": 2
  }
}
$ $sysmlv2 lint --format json rig.sysml | jq -r '.findings[] | "\(.unitName):\(.line):\(.col) \(.severity) \(.rule)"'
rig.sysml:3:14 warn unused-definition
rig.sysml:7:12 warn unused-parameter
```

### The rules

| Rule | Default | Flags | Fix |
|---|---|---|---|
| `naming-convention` | info | a declared name off the project's casing — definitions PascalCase, usages and features camelCase; per-family and per-scope presets (`camelCase`, `PascalCase`, `snake_case`, `UPPER_SNAKE_CASE`, `kebab-case`) or a `regex` | `suggest` carries the re-spelled name |
| `undocumented-element` | off | a definition without its own `doc` body or a comment `about` it; `depth` reaches below the top level | — |
| `untyped-usage` | off | a named usage with no typing, subsetting or redefinition clause (enumeration literals and transitions off by default) | — |
| `unused-definition` | off | a user definition nothing in the user model references (closed world) | — |
| `unused-parameter` | off | an input parameter of a calc / constraint / action definition never used in its body | deletes the parameter (`--fix-deletes`) |
| `import-visibility` | info | an import without a visibility keyword — the syntax check reports the error, this finding carries the fix | declares the visibility its dependents need; the other keywords as alternatives |
| `visibility-blocked-reference` | warn | an unresolved reference that names a member reachable only by ignoring visibility | widens the member to `public` (`--fix-semantic`) |
| `usage-kind-mismatch` | info | a usage typed by a definition of another kind — the semantic check reports the error, this finding carries the fix | rewrites the usage keyword (`--fix-semantic`) |
| `port-member-referential` | info | a composite non-port usage inside a port body | inserts `ref` |
| `unqualified-enum-literal` | warn | an unresolved simple name matching exactly one enumeration literal | qualifies it |
| `unit-spelling` | off | one unit spelled two ways across the model; the `style` option (`quoted-product` / `expression`) enforces a form | re-spells |
| `dimensional-consistency` | warn | a quantity attribute whose declared type and value unit disagree; the `untyped` scope covers an untyped attribute whose value determines its type (needs the standard library) | re-types, or writes the inferred type |
| `qualified-names` | off | one target spelled differently across reference sites; the `style` option (`qualified` / `minimal` / `imported`) enforces a policy | re-spells (adding an import under `imported`) |
| `multiline-conditions` | off | a condition chain of `min` or more operands on one line (the formatter's threshold) | — |
| `indentation` | off | leading whitespace off the project's `style` (tabs or spaces) and `size`; verbatim bodies keep their layout | re-indents |
| `generated-provenance-invalid` | error | corrupted transformer ownership: markers without records, wrong or duplicate claims, malformed baselines | — |
| `generated-provenance-baseline-outdated` | info | a provenance record predating the baseline fields (legacy, not tamper) | — |
| `generated-element-modified` | warn | a generated member drifting from its provenance baseline (format-only drift, baseline drift, or a semantic edit) | — |

`--lib` supplies resolution context only (`dimensional-consistency` stays silent without the standard library's quantity types); library elements are never linted.

---

## 3. `fmt` — canonical formatting

Given a messy source:

```sysml
package  VehicleConfig   {   private   import   ScalarValues :: * ;
  // engine sizing options
  variation  part  def  EngineChoices { variant part '4cyl' ; variant part '6cyl';}
    part def Vehicle{attribute mass:Real; part engine : EngineChoices [ 1 ] ;}}
```

`--stdout` prints instead of rewriting (also the way to format stdin):

```console
$ $sysmlv2 fmt --stdout messy.sysml
package VehicleConfig {
    private import ScalarValues::*;
    // engine sizing options
    variation part def EngineChoices {
        variant part '4cyl';
        variant part '6cyl';
    }
    part def Vehicle {
        attribute mass : Real;
        part engine : EngineChoices[1];
    }
}
```

Notes (`// …`) and blank lines are preserved; the formatter is idempotent and AST-preserving (gated over the whole corpus). `--check` is the CI mode:

```console
$ $sysmlv2 fmt --check messy.sysml
would reformat: messy.sysml
$ echo $?
1

$ $sysmlv2 fmt messy.sysml        # rewrite in place
$ $sysmlv2 fmt --check messy.sysml
$ echo $?
0
```

Files with parse errors are reported and left untouched.

---

## 4. `convert` — text → compact interchange JSON

The compact form (KerML 10.4) is the abstract-syntax element graph as a flat array — memberships, relationships, deterministic UUIDv5 `@id`s — without derived properties or implied relationships:

```console
$ printf 'part def Vehicle { attribute mass : Real; }\n' | $sysmlv2 convert - --to compact-json
[
  {
    "@id": "285a9918-092d-5a42-a72b-91ee2bd95de0",
    "@type": "Namespace",
    ...
  },
  {
    "@id": "9893c716-bf98-5972-a9b2-b6fd34afe8ca",
    "@type": "OwningMembership",
    "ownedRelatedElement": [ { "@id": "77309b84-f72f-5845-a3e5-d958ebf1b702" } ],
    "visibility": "public",
    ...
  },
  {
    "@id": "77309b84-f72f-5845-a3e5-d958ebf1b702",
    "@type": "PartDefinition",
    "declaredName": "Vehicle",
    ...
  },
  ...
]
```

(6 elements for this snippet: namespace, membership, part definition, feature membership, attribute usage, feature typing.)

The same source always produces the same JSON — IDs are graph-derived (chained UUIDv5 through ownership and names, `IDS.md`), so conversion is reproducible. On the full vehicle model:

```console
$ $sysmlv2 convert "$vehicle" --to compact-json -o vehicle.json
$ python3 -c "
import json, collections
doc = json.load(open('vehicle.json'))
print(len(doc), 'elements')
for t, n in collections.Counter(e['@type'] for e in doc).most_common(5):
    print(f'{n:>6}  {t}')"
5452 elements
   684  FeatureMembership
   470  OwningMembership
   393  ParameterMembership
   315  FeatureChaining
   311  Membership
```

---

## 5. `--lib` — resolve against the standard library

With `--lib`, references into the OMG standard library resolve to their **normative element IDs** (KerML 9.1 UUIDv5, verified against the published XMI). `ScalarValues::Real` is `14c0aa22-5489-59b5-b438-ded26e83ba31` in every conforming tool:

```console
$ lib="$corpus/sysml.library"
$ printf 'package M { private import ScalarValues::*; attribute mass : Real; }\n' > m.sysml
$ $sysmlv2 convert m.sysml --to compact-json --lib "$lib" | grep -A1 '"type"'
    "type": {
      "@id": "14c0aa22-5489-59b5-b438-ded26e83ba31"
    },
```

Library elements participate in resolution but are not serialized — the output stays scoped to your model.

Native directory loading saves a build- and content-identified `.prepared` snapshot and shares a live prepared library across SDK sessions. Warm loads reuse the resolved graph and static facts; source trees reconstruct on demand. Set `SYSMLV2_CACHE_DIR` to choose the cache directory or `SYSMLV2_LIB_CACHE=off` to disable library caching. A fresh process with a populated disk cache is warm; a retained SDK session also avoids disk decoding. Neither means the operating-system file cache is cold. In-memory/WASM bundles use the separate resolution-only snapshot API.

### Ambient libraries

Whenever a library loads, the toolkit's generated libraries load with it: `Web` (`Web::DOM`, `Web::HTML`, `Web::HTML::Elements` — the Web platform from the standards' WebIDL), `Template` and `Svelte` (the template metamodel and its engine overlay), `WebApp` and `SvelteKit` (the application and route/SSR layers) and `TransformMeta`. A model can reference them without naming their files:

```console
$ printf 'package V { private import Web::HTML::Elements::*; part shell : Div { :>> id = "app"; } }\n' > v.sysml
$ $sysmlv2 check --strict --lib "$lib" v.sysml
$ $sysmlv2 query --lib "$lib" v.sysml 'V::shell.localName'
"div"
```

Their sources are `local-packages/*.sysml` in the repository; see `local-packages/README.md` for their contents, provenance, and local validation commands.

---

## 6. `convert --to full-json` — the schema-valid full form

The full form adds every derived property and the implied relationships the published `SysML.json` schema requires (52,048/52,048 corpus elements validate; `tests/full_json.rs`):

```console
$ printf 'part def Vehicle { attribute mass : Real; }\n' | $sysmlv2 convert - --to full-json > full.json
$ python3 -c "
import json
pd = [e for e in json.load(open('full.json')) if e['@type'] == 'PartDefinition'][0]
print(len(pd), 'properties on PartDefinition')
print('name:', pd['name'], '| qualifiedName:', pd['qualifiedName'])"
84 properties on PartDefinition
name: Vehicle | qualifiedName: Vehicle
```

A JSON input (a stored compact or full payload) is converted by loading it into a session and emitting from the model — every element keeps the id it carried, foreign ids included, and lift problems print as warnings — so `convert` and the session API cannot disagree; text inputs emit from the parsed model as before. Without `--lib`, references into the standard library stay the library ids the payload carried.

Compare: the compact form carries ~12 properties per element; the full form carries the complete metaclass property set (`name`, `qualifiedName`, `ownedFeature`, `documentation`, `isLibraryElement`, …).

If a work-in-progress model contains unresolved textual references, full JSON and full CBOR preserve their exact spelling by default using schema-valid `TextualRepresentation` annotations. This behavior does not depend on `--flexo`; Flexo changes only the outer payload envelope.

---

## 7. JSON → text

`convert` goes the other way too — input format is auto-detected (extension, else content sniffing). With `--lib`, normative library IDs are turned back into qualified names:

```console
$ $sysmlv2 convert m.sysml --to compact-json --lib "$lib" -o m.json
$ $sysmlv2 convert m.json --to text --lib "$lib"
package M {
    private import $::ScalarValues::*;
    attribute mass : $::ScalarValues::Real;
}
```

Lifted references print as `$::`-rooted qualified names (`$::` roots resolution at the global namespace), so the regenerated text is unambiguous regardless of import context — and it re-parses and re-checks cleanly:

```console
$ $sysmlv2 convert vehicle.json --to text -o vehicle-regen.sysml
$ $sysmlv2 check vehicle-regen.sysml && echo clean
clean
```

### `--min-qual` — shortest reference spellings

The `$::`-rooted printing is the always-correct default; `--min-qual` respells every reference with the *shortest* spelling that still resolves to the same element — bare name where unambiguous, a qualified suffix where needed — and verifies the whole result by reparse before printing (a respell that would change any resolution is dropped, keeping the site's printed form):

```console
$ $sysmlv2 convert m.json --to text --lib "$lib" --min-qual
package M {
    private import $::ScalarValues::*;
    attribute mass : Real;
}
```

The emitted interchange JSON of the minimized text is byte-identical to the `$::`-rooted form's — respelling references moves no declarations, so every element keeps its id. Import targets keep their printed form (their resolution rules differ), and a shadowed name keeps exactly the qualification it needs.

### Full-form input is normalized automatically

Feeding full-form JSON anywhere accepts JSON works — implied relationships are dropped and derived properties ignored on the way in:

```console
$ $sysmlv2 convert full.json --to compact-json | python3 -c "import json,sys; print(len(json.load(sys.stdin)), 'compact elements')"
5 compact elements
```

(The one warning this can print — `cannot name reference target …` — flags an implied-relationship target outside the document; the implied relationship is dropped by normalization anyway.)

---

## 8. Multi-file models — many files ⇄ one JSON

Several textual inputs form **one model** — one root namespace per file, cross-file references resolved:

```console
$ cat definitions.sysml
package Definitions {
    part def Wheel;
    part def Chassis;
}
$ cat vehicle.sysml
package Vehicle {
    private import Definitions::*;
    part chassis : Chassis;
    part wheels : Wheel [4];
}

$ $sysmlv2 convert definitions.sysml vehicle.sysml --to compact-json -o model.json
```

(`model.json` holds 21 elements under two root namespaces, one per file.) The cross-file resolution is easiest to see by asking the model directly — `query` (section 11) takes the same multi-file input:

```console
$ $sysmlv2 query definitions.sysml vehicle.sysml 'Vehicle::wheels istype Definitions::Wheel'
true
$ $sysmlv2 query definitions.sysml vehicle.sysml 'ownedMember(Vehicle)'
Vehicle::chassis (PartUsage)
Vehicle::wheels (PartUsage)
```

Going the other way, `--to text` with `-o <existing dir>` splits a multi-document JSON back into one file per root namespace (without a directory the documents are concatenated to stdout, with a note saying so):

```console
$ mkdir regen
$ $sysmlv2 convert model.json --to text -o regen
regen/document-1.sysml
regen/document-2.sysml
$ cat regen/document-2.sysml
package Vehicle {
    private import $::Definitions::*;
    part chassis : $::Definitions::Chassis;
    part wheels : $::Definitions::Wheel[4];
}
```

Cross-document references print as `$::`-rooted qualified names, so the regenerated files re-check cleanly as a set regardless of import context.

Plain compact JSON leaves the root namespaces anonymous, so the split synthesizes `document-N.sysml` names. `--flexo` (Flexo MMS conventions) stamps each root's `qualifiedName` with its source file name and wraps every element as a `{payload, identity}` change record; pass `--flexo` on the way back to unwrap, and the **original file names are restored**:

```console
$ $sysmlv2 convert definitions.sysml vehicle.sysml --to compact-json --flexo -o flexo.json
$ mkdir regen2
$ $sysmlv2 convert flexo.json --to text --flexo -o regen2
regen2/definitions.sysml
regen2/vehicle.sysml
$ $sysmlv2 check regen2/*.sysml && echo clean
clean
```

The full circle — N files → one Flexo JSON → split → the original file names, re-checked at 0 findings — is gated in `tests/cli.rs`. In library terms the split is `lift::split_documents` (forward ownership closure from each root) and `lift::document_name_map` (cross-document reference naming).

---

## 9. Round-trip fidelity

The conversion matrix is loss-free and byte-stable: text → JSON → text → JSON reproduces the first JSON **byte-identically**, IDs included. On the 1,581-line vehicle model:

```console
$ $sysmlv2 convert "$vehicle" --to compact-json -o v1.json
$ $sysmlv2 convert v1.json --to text -o v-regen.sysml
$ $sysmlv2 convert v-regen.sysml --to compact-json -o v2.json
$ cmp v1.json v2.json && echo byte-identical
byte-identical
```

This invariant is gated over all 345 corpus files (`tests/roundtrip.rs`).

---

## 10. `eval` — compute feature values

The expression evaluator computes bound feature values against the resolved model: operators, sequences, feature references (following values, redefinition-aware), and Kernel Function Library intrinsics including lambda-bodied control functions. Numbers are exact: decimal literals are rationals, arithmetic never rounds (`0.1 + 0.2` is `0.3`, `100 * 1.1` is `110`), integers grow past the machine word instead of wrapping, and unit conversion factors are exact. A result whose decimal expansion terminates prints as that decimal; any other rational prints as a reduced fraction (`1/3`), which is itself a valid expression. Only transcendental functions (`sqrt` of a non-square, `ln`, `exp`, trigonometry) and non-exact powers produce approximate doubles, and any operation over such a value stays approximate.

```sysml
package Demo {
    part def Vehicle {
        attribute baseMass = 1000.5;
        attribute wheelCount = 4;
        attribute wheelMasses = (23, 23, 24, 24);
        attribute totalMass = baseMass + sum(wheelMasses);
        attribute heavy = totalMass > 1000;
        attribute label = "car-" + ToString(wheelCount);
        attribute evens = (1..10)->select { in x; x % 2 == 0 };
        attribute doubled = wheelMasses->collect { in m; m * 2 };
        attribute biggest = max(wheelMasses);
    }
    part car : Vehicle { attribute :>> baseMass = 1200.0; }
    attribute carTotal = car.totalMass;

    attribute mm;
    attribute wheelbase = 2700 [mm];
    attribute overhangs = 2 * (450 [mm]);
    attribute length = wheelbase + overhangs;
    attribute isLong = length > 3500 [mm];

    calc def Power { in torque; in rpm; torque * rpm / 9549.0 }
    attribute peakPower = Power(rpm = 6000, torque = 250);
}
```

```console
$ $sysmlv2 eval demo.sysml --all
baseMass = 1000.5
wheelCount = 4
wheelMasses = (23, 23, 24, 24)
totalMass = 1094.5
heavy = true
label = "car-4"
evens = (2, 4, 6, 8, 10)
doubled = (46, 46, 48, 48)
biggest = 24
<anonymous> = 1200
carTotal = 1294
wheelbase = 2700 [mm]
overhangs = 900 [mm]
length = 3600 [mm]
isLong = true
peakPower = 500000/3183
```

Quantities (`2700 [mm]`) carry their units: same-unit values add and compare on the numbers, scalars scale them, and *different* units never mix silently — `1 [kg] + 1 [mm]` is a type error, not a wrong number. User-defined calculations invoke with positional or named arguments (`Power(rpm = 6000, torque = 250)`), and may recurse (bounded).

Note `carTotal`: the chain step `car.totalMass` evaluates the inherited expression in `car`'s **featuring context**, so the redefined `baseMass = 1200.0` shadows the definition's `1000.5`. Individual features evaluate by qualified name:

```console
$ $sysmlv2 eval demo.sysml Demo::carTotal Demo::Vehicle::totalMass
Demo::carTotal = 1294
Demo::Vehicle::totalMass = 1094.5
```

The `examples/evalstats` run computes 3,306/3,993 feature values (82.8%); 614 are indeterminate over unbound inputs and 73 return errors. Seventeen errors explicitly reject calculations requiring statement execution. These categories distinguish a computed value from a successful indeterminate result; `tests/eval.rs` gates evaluation without panics.

## 11. `query` — ask the model questions

`query` evaluates an ad-hoc KerML expression against the root namespace — the same expression language and evaluator as `eval`, pointed at the model from the outside. Two extensions apply only here (never to feature values in model files): `istype`/`as` classify a model element **closed-world** (a miss against a user-defined type answers `false` instead of undecided — the operand is the declaration itself, not a possibly-more-specific instance), and the reflection functions `ownedMember(x)` / `ownedFeature(x)` — the KerML derived properties, as functions — enumerate an element's owned members. Elements print as qualified name plus metaclass, sequences one item per line.

A structural tour of the Annex A vehicle model:

```console
$ $sysmlv2 query "$vehicle" 'ownedMember(SimpleVehicleModel)'
SimpleVehicleModel::Definitions (Package)
SimpleVehicleModel::VehicleLogicalConfiguration (Package)
SimpleVehicleModel::VehicleLogicalToPhysicalAllocation (Package)
SimpleVehicleModel::VehicleConfigurations (Package)
SimpleVehicleModel::VehicleAnalysis (Package)
SimpleVehicleModel::VehicleVerification (Package)
SimpleVehicleModel::VehicleIndividuals (Package)
SimpleVehicleModel::MissionContext (Package)
SimpleVehicleModel::VehicleSuperSetModel (Package)
SimpleVehicleModel::SafetyandSecurityGroups (Package)
SimpleVehicleModel::Views_Viewpoints (Package)
```

Find parts by usage type — the axle assemblies of the `vehicle_b` configuration:

```console
$ vb=SimpleVehicleModel::VehicleConfigurations::VehicleConfiguration_b::PartsTree::vehicle_b
$ ax=SimpleVehicleModel::Definitions::PartDefinitions::AxleAssembly
$ $sysmlv2 query "$vehicle" "ownedFeature($vb)->select { in p; p istype $ax }"
SimpleVehicleModel::VehicleConfigurations::VehicleConfiguration_b::PartsTree::vehicle_b::frontAxleAssembly (PartUsage)
SimpleVehicleModel::VehicleConfigurations::VehicleConfiguration_b::PartsTree::vehicle_b::rearAxleAssembly (PartUsage)
```

References in a query resolve from the *root* namespace, so type names are spelled fully qualified. `ownedFeature` follows the KerML derived property exactly: a usage owned by a *package* is an owned member but not an owned feature. The argument can itself be a chain — `vehicle_b`'s rear wheels:

```console
$ $sysmlv2 query "$vehicle" "ownedFeature($vb.rearAxleAssembly)->select { in p; p istype SimpleVehicleModel::Definitions::PartDefinitions::Wheel }"
SimpleVehicleModel::VehicleConfigurations::VehicleConfiguration_b::PartsTree::vehicle_b::rearAxleAssembly::rearWheel1 (PartUsage)
SimpleVehicleModel::VehicleConfigurations::VehicleConfiguration_b::PartsTree::vehicle_b::rearAxleAssembly::rearWheel2 (PartUsage)
```

Reflection composes with evaluation: chain into the enumerated parts and collect their quantity-valued masses (the `[kg]` brackets need the standard library):

```console
$ $sysmlv2 query "$vehicle" --lib "$lib" "ownedFeature($vb)->select { in p; p istype $ax }->collect { in p; p.mass }"
800 [kg]
875 [kg]
```

And the whole Kernel Function Library is available, so counting, folding, and plain value computation work anywhere `eval` does:

```console
$ $sysmlv2 query "$vehicle" "size(ownedFeature($vb))"
40
```

## 11a. `render` — evaluate a view's component template

A component template represented as a `rendering def` plus a `view def` can be evaluated over a model. A `view` usage of that definition exposes a model slice, and `render` evaluates the template over it — each blocks iterate the exposed elements, expression tags evaluate their translated KerML — printing the rendered node tree as JSON, or HTML with `--html`. The model is not modified.

```console
$ $sysmlv2 render --lib "$lib" --html PackagesView.sysml fleet.sysml Site::packagesView
<h3 id="packages-heading">Vehicles</h3><filterable-list>…</filterable-list>
```

Expressions the importer could not translate render as their opaque source (`{expr}`) or as an `<!-- error: … -->` marker, so a view always renders.

---

## 12. `verify` — constraint verdicts, witnesses, proofs

`verify` evaluates every constraint, requirement, and invariant body that carries its own result expression to a verdict — satisfied, VIOLATED (exit 1), or undecided with the reason:

```sysml
package FlightCheck {
    attribute wingArea = 52.5;
    attribute maxLoad = 4200;
    attribute loading = maxLoad / wingArea;

    assert constraint capacity { maxLoad > 0 & loading < 90 }
    assert constraint strict { loading < 50 }
    assert constraint unknownSpan { wingSpan > 10 }
}
```

```console
$ $sysmlv2 verify wing.sysml
wing.sysml:6:34  capacity (AssertConstraintUsage): satisfied
wing.sysml:7:32  strict (AssertConstraintUsage): VIOLATED
wing.sysml:8:37  unknownSpan (AssertConstraintUsage): undecided (unresolved reference `wingSpan`)
1 satisfied, 1 violated, 1 undecided
$ echo $?
1
```

Verdicts are deliberately cautious: a comparison involving an *unbound* feature is undecided, never a false `false` — which keeps the corpus at **0 violated** (ratcheted by `tests/check.rs`). A type default read through an unbound parameter or featured reference — a requirement's `subject` or `ref part`, an actor, a calculation input — is undecided because the instance bound later may override it. A fixed literal still decides; a fixed formula decides only when its inputs are known. This uncertainty survives aliases, conditionals, nested members and calculation calls, while concrete receivers still read their defaults. The same discipline covers cardinality: `size(xs)` over an unbound feature answers only what the declared multiplicity proves (an exact `[3]` answers 3, `[1..*]` settles `notEmpty`, anything else stays undecided). Propagation keeps unknown receiver members free; nested unknown receiver paths stay outside the supported fragment rather than conflating distinct instances.

### Satisfaction claims — subject-bound verdicts

A `satisfy R by x;` member claims that `x` satisfies requirement `R` — so `verify` binds `R`'s subject to `x` and evaluates every constraint reachable through the requirement's composition: nested `require` references with their parameter bindings, bodies inherited from requirement definitions, and assumption constraints. The bound verdicts carry a `satisfies …` context; the unbound originals keep their honest undecideds:

```sysml
package Freight {
    private import ISQ::*;
    private import SI::*;
    part def Wagon {
        attribute tare : MassValue;
        attribute cargo : MassValue;
    }
    part wagon1 : Wagon {
        attribute :>> tare = 800 [kg];
        attribute :>> cargo = 150 [kg];
        satisfy wagonSpec by wagon1;
    }
    requirement wagonSpec {
        subject unit : Wagon;
        require ladenLimit { in w = unit; }
        require emptyLimit { in w = unit; }
    }
    requirement def MassCap {
        attribute actual : MassValue;
        attribute cap : MassValue;
        require constraint { actual <= cap }
    }
    requirement def WagonMassCap :> MassCap {
        subject w : Wagon;
        attribute :>> actual = w.tare + w.cargo;
        assume constraint { w.cargo > 0 [kg] }
    }
    requirement ladenLimit : WagonMassCap {
        attribute :>> cap = 1000 [kg];
    }
    requirement emptyLimit : WagonMassCap {
        attribute :>> cap = 900 [kg];
    }
}
```

```console
$ $sysmlv2 verify freight.sysml --lib sysml.library
freight.sysml:21:30  <anonymous> (ConstraintUsage): undecided (result is indeterminate over unbound features)
freight.sysml:26:29  <anonymous> (ConstraintUsage): undecided (result is indeterminate over unbound features)
freight.sysml:21:30  <anonymous> (ConstraintUsage, satisfies Freight::wagonSpec): satisfied
freight.sysml:21:30  <anonymous> (ConstraintUsage, satisfies Freight::wagonSpec): VIOLATED
freight.sysml:26:29  <anonymous> (ConstraintUsage, satisfies Freight::wagonSpec): satisfied
freight.sysml:26:29  <anonymous> (ConstraintUsage, satisfies Freight::wagonSpec): satisfied
3 satisfied, 1 violated, 2 undecided
$ echo $?
1
```

The wagon's 950 kg is inside the 1000 kg laden cap (satisfied) but over the 900 kg empty cap — the claim is genuinely false, and `verify` says so with exit 1. The `massActual <= massReqd` body evaluates once per requirement branch, each under its own redefinitions.

### `--ranges` — interval propagation (no solver)

With `--ranges`, every unbound feature gets an interval domain that the asserted constraints contract by bidirectional propagation. There is no external solver — it is ~300 lines of interval arithmetic in `sysmlv2-solve`. The result is a **finite range per feature** plus verdict upgrades that are definitive (a range holds for *every* consistent assignment): a body that is true over the whole narrowed domain is satisfied, one that is false everywhere is VIOLATED, and a domain that contracts to empty (`∅`) proves the constraint unsatisfiable.

```sysml
package Demo {
    attribute def Real;
    attribute def Integer;
    attribute wingSpan : Real;
    attribute count : Integer;

    assert constraint span_lo { wingSpan >= 10 }
    assert constraint span_hi { wingSpan <= 200 }
    assert constraint bad { count > 5 & count < 4 }
}
```

```console
$ $sysmlv2 verify demo.sysml --ranges
demo.sysml:6:33  span_lo (AssertConstraintUsage): satisfied (propagation: holds for all values in the narrowed ranges)
demo.sysml:7:33  span_hi (AssertConstraintUsage): satisfied (propagation: holds for all values in the narrowed ranges)
demo.sysml:8:29  bad (AssertConstraintUsage): VIOLATED (propagation: domains contract to empty — unsatisfiable)
2 satisfied, 1 violated, 0 undecided

narrowed ranges:
  wingSpan ∈ [10, 200]
  count ∈ ∅
```

Constraints sharing a feature narrow it *jointly* (`span_lo` and `span_hi` bracket `wingSpan` from both sides), and an empty domain implicates only the constraints that reference the emptied feature — the feasible siblings stay satisfied.

### `--solve` — send the residue to Z3

With `--solve` (and a `z3` binary on `PATH`, or `--z3 <path>`), propagation runs **first**, and only the constraints it cannot settle become SMT queries — Z3 sees a smaller problem. Linear bounds, enumeration disequalities, and empty-domain contradictions never reach Z3 at all (propagation decides them, as in the `--ranges` example above); what remains for Z3 is the genuinely contingent and the nonlinear, where it either proves the constraint or exhibits a witness. Each residual query is also *bounded*: the feature's propagated range is asserted alongside the constraint (on the satisfiability query only), so Z3 searches a box instead of the whole real line — which turns some otherwise-`unknown` nonlinear queries into decisions.

Bound features *inline their defining expressions*, so a constraint over derived values solves in terms of the underlying unknowns — here Z3 handles the nonlinear volume of a tank whose height is tied to its radius, and the witness names only the free variable:

```sysml
package Tank {
    attribute def Real;
    attribute radius : Real;
    attribute height : Real = radius * 2.0;
    attribute volume : Real = 3.14159 * radius * radius * height;

    assert constraint fits { volume <= 50.0 & radius >= 1.0 }
}
```

```console
$ $sysmlv2 verify tank.sysml --solve
tank.sysml:7:30  fits (AssertConstraintUsage): undecided (result is indeterminate over unbound features) — z3: satisfiable, e.g. radius = 1.5
0 satisfied, 0 violated, 1 undecided
```

What stays undecided is honestly undecided — a contingent constraint reports a witness instead of a guess, constructs outside the decidable fragment (sequences, strings, quantity brackets…) say so, and a feature whose definition can't be encoded is over-approximated in a way that keeps `VIOLATED`/`satisfied` upgrades definitive. Across the corpus, 43 of the 80 evaluator-undecided constraints get witnesses this way, and none are unsatisfiable (`crates/sysmlv2-solve/tests/corpus.rs` gates exactly that). The solving layer lives in the dependency-free `sysmlv2-solve` crate — Z3 runs as a subprocess, nothing links libz3.

## 13. `viz` — PlantUML diagrams

`viz` renders one view of a model as PlantUML text (`--view tree|interconnection|state|action|sequence|case|mixed`, default `tree`; `ic` and `seq` are accepted short spellings). Feed the output to any PlantUML build for SVG/PNG; the toolkit itself has no rendering stage.

The **tree** view is the structure diagram: packages, definitions, and usages with attribute compartments, plus composition (`*--`), typing (`..>`), and specialization (`--|>`) edges.

```console
$ printf 'package Vehicles {
    part def Vehicle { attribute mass : Real = 1200; part wheels : Wheel[4]; }
    part def Wheel;
    part myCar : Vehicle;
}' | $sysmlv2 viz -
@startuml
hide empty members
package "Vehicles" as n1 {
  class "Vehicle" as n2 <<part def>> {
    mass = 1200
  }
  class "wheels : Wheel [4]" as n3 <<part>>
  class "Wheel" as n4 <<part def>>
  class "myCar : Vehicle" as n5 <<part>>
}
n2 *-- n3
n3 ..> n4
n5 ..> n2
@enduml
```

The **interconnection** view renders parts as nested `rectangle` blocks with ports on their boundaries — ports declared on a part's *definition* render on each usage box — and connector-family usages as edges between their resolved ends: connections (`--`), interfaces (`-- : «interface»`), bindings (`.. : =`), allocations (`..> : «allocate»`), and flows (`-->`, labelled with their payload).

```console
$ printf 'package Rig {
    part def Tank { port fuelOut; }
    part rig {
        part tank : Tank;
        part eng { port fuelIn; }
        connection c1 connect tank.fuelOut to eng.fuelIn;
    }
}' | $sysmlv2 viz - --view interconnection
@startuml
package "Rig" as n1 {
  rectangle "Tank" as n2 <<part def>> {
    port "fuelOut" as n3
  }
  rectangle "rig" as n4 <<part>> {
    rectangle "tank : Tank" as n5 <<part>> {
      port "fuelOut" as n6
    }
    rectangle "eng" as n7 <<part>> {
      port "fuelIn" as n8
    }
  }
}
n6 -- n8 : c1
@enduml
```

The **state** and **action** views render behavior in the PlantUML state-diagram dialect. States and actions become (composite) `state` nodes; transitions become edges labelled `trigger [guard] / effect`; a succession from an unspelled or `start`/`done` end becomes the `[*]` initial/final pseudostate; entry/do/exit subactions become description lines; fork/join nodes map to the built-in bar shapes and decision/merge to `<<choice>>`; flows inside actions draw dashed. Packages and parts are transparent containers here — a `state def` in a package or an `exhibit state` inside a part is found wherever it lives.

```console
$ $sysmlv2 viz doors.sysml --view state
@startuml
state "DoorStates" as n1 <<state def>> {
  state "Closed" as n2 <<state>>
  state "Open" as n3 <<state>>
  [*] --> n2
  n2 --> n3 : OpenCmd [ready]
  n3 --> n2 : CloseCmd / notifier : Notify
}
@enduml
```

The **sequence** view mirrors the Pilot's SEQUENCE mode: lifelines for the parts that exchange messages, `->>` arrows for flow-family usages (the `message` spelling included). Message ends spelled through events (`message m from producer.pub_evt to server.rcv_evt`) attach to the event's owning part; plain part ends still render. Messages sort by the events' succession partial order — `event occurrence a; then event occurrence b;` orders a lifeline, and that order wins over message declaration order. Participants group `box "Owner" … end box` per owning definition. (`--horizontal` is ignored — the sequence dialect has no direction line.)

```console
$ $sysmlv2 viz pubsub.sysml --view sequence
@startuml
box "PubSubSequence"
participant "producer" as n1
participant "server" as n2
participant "consumer" as n3
end box
n3 ->> n2 : subscribe_message
n1 ->> n2 : publish_message
n2 ->> n3 : deliver_message
@enduml
```

The **case** view is a use-case diagram: case-family definitions and usages as `usecase` nodes, `actor` members with association edges, subjects as `<<subject>>` rectangles, objectives as attached notes carrying their doc bodies, and `include` references as `«include»` edges.

The **mixed** view puts everything on one canvas — the Pilot's MIXED mode: nested part rectangles with ports and connector edges, states/actions as stereotyped rectangles with succession/transition edges (`trigger [guard] / effect`), cases and actors, plus typing (`..>`) and specialization (`--|>`) edges. Attribute compartments stay in the tree view (the component dialect has none).

Cross-view options:

- Comment and `doc` bodies attach as `note` blocks wherever their annotated element is on the diagram (`--no-notes` omits them).
- Prefix metadata (`#Safety part def Pump;`) joins the node's stereotype list (`<<part def>> <<Safety>>`); `--hide-metadata` drops metadata entirely.
- `--show-inherited` adds `^`-marked compartment lines one explicit typing/specialization hop up (tree view; own members shadow).
- `--show-lib` gives referenced standard-library types their own `<<library>>`-marked nodes instead of label-only names.
- `--show-imported` draws `«import»` edges between rendered nodes.
- `--line-style polyline|ortho` picks edge routing; `--color` keys node backgrounds on the metaclass family.
- `--link-template "vscode://file/{file}:{line}"` embeds `[[url]]` hyperlinks on every node (placeholders `{file}`, `{line}`, `{col}`, `{qname}`, `{id}`) — PlantUML carries them into rendered SVG, so diagram nodes click through to their source declarations.

`--element <qualified::name>` roots the diagram at one element, `--horizontal` lays it out left-to-right, `--no-values` drops the `= value` suffixes (tree view), and `--lib` names standard-library references in labels (library elements never render as nodes by default; their ports still render on the usages they type). In the tree view, attribute-family usages become compartment lines on their owner; everything else usage-shaped becomes a node with a composition edge.

```console
$ $sysmlv2 viz model.sysml --lib "$lib" --element Vehicles::Vehicle -o vehicle.puml
$ java -jar plantuml.jar -tsvg vehicle.puml
```

Every non-library corpus file emits a balanced diagram for every view (`sysmlv2-viz/tests/viz.rs`), and the full sweep validates against a real PlantUML build (`cargo run -p sysmlv2-viz --example vizsweep`).

### View-directed diagrams

A *view usage* carries its own diagram definition: `expose` picks the elements (with the model's `filter` conditions applied through the same machinery that governs import visibility), and `render` picks the style. Pointing `--element` at a view renders exactly that slice — `--view` is only needed to override the view's own choice:

```sysml
package Stage {
    metadata def LOUD;
    port def Jack;
    interface def Cable { end a : Jack; end b : Jack; }
    part def Amp { port line : Jack; port aux : Jack; }
    part def Speaker { port feed : Jack; }
    part rig {
        part amp : Amp;
        part main : Speaker;
        part monitor : Speaker;
        interface connect amp.line to main.feed;
        #LOUD interface connect amp.aux to monitor.feed;
    }
    view quiet {
        expose rig::**;
        filter not (@LOUD);
        render Views::asInterconnectionDiagram;
    }
}
```

```console
$ $sysmlv2 viz slice.sysml --element Stage::quiet --lib sysml.library
@startuml
rectangle "amp : Amp" as n1 <<part>> {
  port "line : Jack" as n2
  port "aux : Jack" as n3
}
rectangle "main : Speaker" as n4 <<part>> {
  port "feed : Jack" as n5
}
rectangle "monitor : Speaker" as n6 <<part>> {
  port "feed : Jack" as n7
}
n2 -- n5 : «interface»
@enduml
```

The `LOUD`-tagged connector is filtered off the canvas; the untagged parts and the remaining cable render, and the interconnection style came from the view's `render` member, not the command line.

## 14. Pipelines

`-` reads stdin everywhere (sniffed as JSON if it starts with `[` / `{`, otherwise parsed as SysML), so the subcommands compose:

```console
$ cat m.sysml | $sysmlv2 convert - --to compact-json | $sysmlv2 convert - --to text
package M {
    private import ScalarValues::*;
    attribute mass : Real;
}

$ git show HEAD:model.sysml | $sysmlv2 check -            # check a past revision
$ curl -s https://example.org/model.json | $sysmlv2 convert - --to text
$ $sysmlv2 lint --format json src/*.sysml | jq '.summary'  # machine-readable findings (check too)
```

A reader that stops early — `$sysmlv2 convert model.json --to text | head` — ends the run quietly: the closed pipe means no more output is wanted, so nothing is printed and the exit status is 0.

---

## 15. `convert --to compact-cbor` — the binary `.s2c` form

The compact element array also serializes as **s2c**, a deterministic CBOR encoding (`CBOR.md` — RFC 9277 file magic, presence-bitmask elements, interned UUID tables). Same information, an order of magnitude fewer bytes:

```console
$ $sysmlv2 convert "$vehicle" --to compact-cbor -o vehicle.s2c
$ xxd -l 16 vehicle.s2c
00000000: d9d9 f7da 2453 3243 841b 0000 0001 0001  ....$S2C........
```

The first eight bytes are the file magic (self-described-CBOR tag 55799 wrapping application tag `0x24533243`, "`$S2C`"); the payload is one valid CBOR item, so generic CBOR tooling reads it too. On the vehicle model (6,405 elements):

| form | bytes |
|---|---:|
| pretty JSON | 3,202,468 |
| minified JSON | 2,487,208 |
| `.s2c` | 238,802 |
| `.s2c --elide-ids` | 129,951 |

`--elide-ids` drops every id the receiver can re-derive from the graph (`IDS.md`), leaving a per-element exception map and an integrity digest the decoder verifies. (The codec round trip is byte-exact — `from_compact_cbor(to_compact_cbor(v)) == v`, gated in `crates/sysmlv2-cbor` — while `convert` treats an `.s2c` *input* like a `.json` input: it lifts and re-emits.) Binary back to text:

```console
$ $sysmlv2 convert vehicle.s2c --to text | head -8
package SimpleVehicleModel {
    public import $::SimpleVehicleModel::Definitions::*;
    public import ISQ::*;
    package Definitions {
        public import $::SimpleVehicleModel::Definitions::PartDefinitions::*;
        public import $::SimpleVehicleModel::Definitions::PortDefinitions::*;
        public import $::SimpleVehicleModel::Definitions::ItemDefinitions::*;
        public import $::SimpleVehicleModel::Definitions::SignalDefinitions::*;
```

`--to full-cbor` emits the full form the same way, and `--delta-base` turns the output into a **delta payload** — element-granular change records against a base snapshot, the commit-sized shape:

```console
$ printf 'package Drive { part def Motor; part m : Motor; }\n' > v1.sysml
$ printf 'package Drive { part def Motor; part m : Motor; part def Battery { attribute charge; } }\n' > v2.sysml
$ $sysmlv2 convert v1.sysml --to compact-cbor -o base.s2c
$ $sysmlv2 convert v2.sysml --to compact-cbor --delta-base base.s2c -o commit.s2c
$ ls -l base.s2c commit.s2c | awk '{print $5, $9}'
278 base.s2c
208 commit.s2c
```

The delta names its base by content digest and refuses a wrong base hard; applying it reproduces the target exactly:

```console
$ $sysmlv2 convert commit.s2c --delta-base base.s2c --to text
package Drive {
    part def Motor;
    part m : $::Drive::Motor;
    part def Battery {
        attribute charge;
    }
}
```

(`--delta-portable` switches to id-keyed change records that apply best-effort to divergent bases — cherry-pick semantics; see `CBOR.md`.)

The base may come from any producer or invocation shape. Ids re-derive on every parse from a root seeded by the unit name and build layout (a `--lib` or multi-file run seeds differently than a bare single-file one, an IDE export differently again), so before diffing the encoder **rebases** the fresh parse onto the base: elements at the same ownership path adopt the base element's id, and unchanged elements keep their identity in the delta no matter where the base snapshot came from.

### 15.1 `payload` — inspect files, match deltas to bases

`payload` says what a payload file *is* without loading it as a model: form, header versions, element and change counts, and the content digests the delta machinery keys on. A snapshot (`.s2c` or compact `.json`) reports its **state digest**; a delta reports the **base digest** it demands and the **result digest** it produces — readable without the base present:

```console
$ $sysmlv2 payload commit.s2c | jq '.delta | {baseDigest, resultDigest}'
{
  "baseDigest": "76ee91ca-4c74-5e9d-b657-3a761d2af71f",
  "resultDigest": "aed59321-92b3-545a-ae23-7cb1122a28d5"
}
$ $sysmlv2 payload base.s2c | jq .stateDigest
"76ee91ca-4c74-5e9d-b657-3a761d2af71f"
```

A snapshot is a valid base for a delta exactly when its state digest equals the delta's base digest. `--find-base` runs that comparison over a directory — every snapshot file under it is digested once, and each delta input reports which ones it applies to cleanly (`baseMatches`) and which already hold its outcome (`resultMatches`):

```console
$ $sysmlv2 payload commit.s2c --find-base . | jq .delta.baseMatches
[
  "./base.s2c"
]
```

A delta with no base match prints a note and exits nonzero, so the verb scripts as a check. Digests are content-derived (`uuid5` over the canonical compact encoding), so a match is a match regardless of which tool produced the snapshot or how it traveled. Id-elided snapshots decode before digesting; pass `--lib` when their elements are library-typed.

### 15.2 Payload-identity operations — `--delta-from`, `--apply-to`, `--ids`

Every mode of the `payload` verb works **at payload identity**: files are read exactly as their producer wrote them — no model lift, no id re-derivation, no rebase. That is the mode a store wants when the ids in its payloads are authoritative (it assigned them, or it committed to the ones it ingested) and its two states must diff losslessly. Contrast `convert --delta-base` (section 15), which parses its input as a model and therefore re-derives and rebases ids — right for fresh parses of textual sources, wrong for a store diffing its own states: there a rename with stable ids would split into delete+create at the rebase's pairing gate instead of staying one update.

`--delta-from BASE` diffs the single snapshot input against `BASE`, pairing elements by `@id`. `--claim-project`, `--claim-commit`, and `--claim-service` attach the documented routing claims (keys 0/1/2 — hints only; the base digest remains the proof), and `--portable` switches to id-keyed change records:

```console
$ $sysmlv2 convert v1.sysml --to compact-json -o state1.json
$ # …rename Motor to TractionMotor in place, every @id untouched…
$ $sysmlv2 payload state2.json --delta-from state1.json \
    --claim-commit 8c56a141-4dbd-4c4a-b3dc-6a05e2eb4bd0 -o commit.s2c
$ $sysmlv2 payload commit.s2c | jq '.delta | {changes, claims}'
{
  "changes": { "creates": 0, "deletes": 0, "updates": 1 },
  "claims": [ { "id": "8c56a141-4dbd-4c4a-b3dc-6a05e2eb4bd0", "key": 1 } ]
}
```

The rename travels as one 97-byte field-patched update. `--apply-to BASE` applies a delta the same way — the applied compact JSON goes to `--output`, and the apply report (with the digest-verified result digest) to stdout; `--lenient` lets a portable delta proceed best-effort on a divergent base, with the report counting what happened:

```console
$ $sysmlv2 payload commit.s2c --apply-to state1.json -o applied.json
{
  "baseMatched": true,
  "file": "commit.s2c",
  "noopDeletes": 0,
  "output": "applied.json",
  "replacedCreates": 0,
  "resultDigest": "e2161595-ea55-521a-96c7-c6c04a6a18b9",
  "resultElements": 8,
  "units": [],
  "upsertedUpdates": 0
}
```

`--encode` completes the payload-identity family: it encodes a compact-JSON snapshot to `.s2c` exactly as written — the store-side inverse of a snapshot decode, digest-preserving even for ids no session derivation would mint (`convert` would lift and re-derive them):

```console
$ $sysmlv2 payload state1.json --encode -o state1.s2c
$ $sysmlv2 payload state1.s2c | jq .stateDigest
"76ee91ca-4c74-5e9d-b657-3a761d2af71f"
```

`--ids` prints a snapshot's **delta-canonical element id sequence** — the index space strict deltas address their base through (`CBOR.md` documents the ordering rule). A store that records this sequence per state can resolve a strict delta's `updateTargets`/`deleteTargets` indices to element ids without holding the base payload itself:

```console
$ $sysmlv2 payload state1.json --ids | jq '{elements, stateDigest}'
{
  "elements": 8,
  "stateDigest": "76ee91ca-4c74-5e9d-b657-3a761d2af71f"
}
```

### 15.3 The codec tables artifact — `--tables`

The meaning of every small integer on the s2c wire — metaclass type codes, field ordinals, enum values, presence defaults — is *generated data*, versioned by the header's `tables` axis. `payload --tables` exports it as one self-contained JSON document, so a consumer in any language can label payload structure by vendoring the artifact instead of porting tables by hand:

```console
$ $sysmlv2 payload --tables -o s2c-tables.json
$ jq '{magic, versions, flags}' s2c-tables.json
{
  "magic": "d9d9f7da24533243",
  "versions": { "layout": 1, "scheme": 1, "tables": 1 },
  "flags": { "delta": 4, "deltaPortable": 8, "elideIds": 1, "explicitIds": 64, "fullForm": 2, "impliedOwners": 32, "unitPaths": 16 }
}
$ jq '.metaclasses[] | select(.name == "AcceptActionUsage") | .fields[15]' s2c-tables.json
{
  "default": true,
  "kind": 0,
  "ordinal": 15,
  "prop": "isUnique"
}
```

The document carries both ordinal spaces (`metaclasses` for compact payloads, `fullMetaclasses` for the emit-only full form), the enum vocabularies, the field-kind legend, and each field's presence default where its kind has one (booleans and enums — what a presence bit materializes as). Wire codes and ordinals are array positions, also spelled explicitly. A consumer should refuse payloads whose header `tables` version differs from the vendored artifact's — regenerating the artifact against a newer toolkit is the upgrade path, not editing it.

### 15.4 Exporting the standard library — `convert --library`

A normal conversion emits just the user units' elements; its references into the standard library are bare `@id`s that dangle by design (section 5's note). `convert --library` emits the other half — the resolved library itself, every element of the `--lib` units under its normative KerML 9.1 id — so a store can materialize the library once and have every user payload's library references land exactly on its element ids:

```console
$ export SYSMLV2_AMBIENT=off  # measure the 94-unit official library alone
$ $sysmlv2 convert --library --lib "$lib" --to compact-json -o stdlib.json
$ $sysmlv2 convert --library --lib "$lib" --to compact-cbor -o stdlib.s2c
$ jq length stdlib.json
91405
$ ls -l stdlib.json stdlib.s2c | awk '{print $5, $9}'
45432383 stdlib.json
3586617 stdlib.s2c
```

(The binary form also benefits from implied ownership backpointers — `CBOR.md`, flag 0x20: backpointers that match their derivation from the forward ownership lists never reach the wire, ~10% of this payload.)

The export is deterministic, internally complete (no dangling references; its only unowned roots are the per-unit namespaces), and digests identically however it travels:

```console
$ $sysmlv2 payload stdlib.json | jq .stateDigest
"c64e4daa-4a49-5052-8adb-d038c3ac6202"
$ $sysmlv2 payload stdlib.s2c | jq .stateDigest
"c64e4daa-4a49-5052-8adb-d038c3ac6202"
```

Named library elements carry ids derived from their qualified names (KerML 9.1 — identical across conforming implementations, stable across releases while the name is stable). Truly unnamed elements keep this toolkit's deterministic path-based ids: the norm's positional ids count an implementation's implied-relationship closure, so no portable spelling exists for them — and being unnamed, they are never the target of a cross-model reference. Unset `SYSMLV2_AMBIENT` after reproducing these official-library-only numbers to restore ambient libraries. Byte counts and digests above use the pinned library. `--library` takes no inputs (the `--lib` directory is the input) and targets `compact-json` and `compact-cbor`.

## 16. Ambient model and library directories

Every section above named its input files explicitly. When `SYSMLV2_MODEL_DIR` names a directory, its `.sysml`/`.kerml` files (collected depth-first with siblings in name order; hidden entries skipped) stand in for omitted inputs. Explicit files always win — the variable only fills an absence — and a stderr note records when it did, so output never silently depends on ambient state:

```console
$ ls rover/
chassis.sysml   power.sysml
$ cat rover/chassis.sysml
package Chassis {
    part def Frame {
        attribute mass = 42.0;
    }
}
$ cat rover/power.sysml
package Rover {
    private import Chassis::*;
    part base : Frame;
    attribute payload = 8.5;
    attribute totalMass = base.mass + payload;
}

$ export SYSMLV2_MODEL_DIR=rover
$ $sysmlv2 check
sysmlv2: model = 2 files from rover (SYSMLV2_MODEL_DIR)

$ $sysmlv2 query 'size(ownedMember(Rover))'
sysmlv2: model = 2 files from rover (SYSMLV2_MODEL_DIR)
3
```

`eval` and `query` reclassify their leading positional, so with the variable set a bare qualified name or expression is not mistaken for a file. The note goes to stderr — pipelines still see clean stdout — and `-q`/`--quiet` silences it:

```console
$ $sysmlv2 -q eval Rover::totalMass
Rover::totalMass = 50.5
```

Destructive verbs do not inherit ambience: in-place `fmt` refuses, while `fmt --check` (the read-only mode) runs:

```console
$ $sysmlv2 fmt
error: no input files — fmt rewrites in place, so ambient SYSMLV2_MODEL_DIR inputs apply to --check only; pass explicit paths

$ $sysmlv2 fmt --check
sysmlv2: model = 2 files from rover (SYSMLV2_MODEL_DIR)
```

With the variable set, `--help` (top-level and per-verb) ends by confirming the active context:

```console
$ $sysmlv2 check --help | tail -1
model context: rover (SYSMLV2_MODEL_DIR — 2 model files); file inputs may be omitted
```

Without it, omitting inputs is still an error, and it names both remedies:

```console
$ unset SYSMLV2_MODEL_DIR
$ $sysmlv2 check
error: no input files — provide input files, or set SYSMLV2_MODEL_DIR to a model directory
```

`SYSMLV2_LIB_DIR` works the same way for `--lib`: wherever the flag is accepted (including `lsp`) the variable fills it when omitted, and the flag's `--help` entry carries an `[env: SYSMLV2_LIB_DIR=]` tag.

---

## 17. `describe` / `members` — element inspection

Two small verbs answer "what is this element" and "what does it own" without exporting anything — the terminal-friendly companions to `query`. Both take the usual file arguments (or the `SYSMLV2_MODEL_DIR` ambient context; a leading qualified name is then a name, not a file):

```console
$ export SYSMLV2_MODEL_DIR=rover
$ $sysmlv2 -q describe Rover::base
Rover::base
  metaclass  PartUsage
  owner      Rover
  type       Chassis::Frame
  position   1 of 3
  location   rover/power.sysml:3:10

$ $sysmlv2 -q members Rover
base                         PartUsage
payload                      AttributeUsage
totalMass                    AttributeUsage

$ $sysmlv2 -q members Chassis::Frame
mass                         AttributeUsage
```

`position` counts owned members only (import memberships are not members of the importing namespace); an unresolved name exits 1 with `error: cannot resolve \`…\``.

## 18. `refactor` — extract / split / inline

`extract` and `inline` move a model between the usage-oriented and definition-oriented styles. Both directions run the transformation engine's verified commit: every carried reference is checked at its new home, and a refusal names its reason and leaves every file untouched. Given `model.sysml`:

```sysml
package Rig {
    part def A;
    part engine : A {
        attribute mass = 100;
    }
}
```

`--dry-run` prints the would-be changes as one trimmed hunk per file and writes nothing:

```console
$ sysmlv2 refactor extract model.sysml Rig::engine --dry-run
--- model.sysml
@@ -3,3 +3,4 @@
-    part engine : A {
-        attribute mass = 100;
-    }
+    part def Engine :> A {
+        attribute mass = 100;
+    }
+    part engine : Engine;
```

Without it, changed files are rewritten in place (the summary goes to stderr; `--name` overrides the UpperCamel default). A multi-file edit preflights every target, stages same-directory replacement and rollback copies, and restores already-replaced files if a later replacement fails. Before rollback it rechecks each source; if one changed after replacement, the external edit is preserved and the error names the retained recovery copy instead. Native Unix writes retain the source's owner, group, mode, and extended attributes, and refuse files with multiple hard links rather than silently splitting their contents. Success summaries appear only after the whole write completes:

```console
$ sysmlv2 refactor extract model.sysml Rig::engine
extracted 'Engine' from `Rig::engine` — rewrote model.sysml
$ cat model.sysml
package Rig {
    part def A;
    part def Engine :> A {
        attribute mass = 100;
    }
    part engine : Engine;
}
```

Inlining the definition just produced restores the original file byte-for-byte (the one-sided inverse the engine gates promise):

```console
$ sysmlv2 refactor inline model.sysml Rig::Engine
inlined `Rig::Engine` — rewrote model.sysml
```

Refusals are named, not stack traces — an ineligible target, a taken name, outside references through a definition:

```console
$ sysmlv2 refactor extract model.sysml Rig::A
error: extract refused: not an extractable usage (metaclass PartDefinition)
```

Inline reports imports its deletion leaves unused as `note:` lines on stderr and never removes them itself (that is the LSP quick fix's job). With `SYSMLV2_MODEL_DIR` set, bare invocations read the ambient model for `--dry-run` only — in-place rewriting always requires explicit file paths, the same discipline as `fmt`.

### `split` — one file per nested package

`refactor split` takes a package apart: every nested package moves to its own file under a directory named after the root file (`--dir` overrides it; `--slug` restricts file names to letters, digits, `.`, `_` and `-`), dedented, with every reference to something outside it spelled in full, and the root package re-exports each one with a `public import` (or a public alias when a package had to be renamed to avoid a root-level collision), so every qualified reference through the root keeps resolving. Given `model.sysml`:

```sysml
package Root {
    part def Frame;
    package Chassis {
        part def Axle;
        part body : Frame;
    }
    package Drive {
        part axle : Chassis::Axle;
    }
}
```

`--dry-run` prints the plan, the new files and the root's hunk, and writes nothing:

```console
$ $sysmlv2 refactor split model.sysml Root --dry-run
model/Chassis.sysml: `Root::Chassis` (73 bytes)
model/Drive.sysml: `Root::Drive` (56 bytes)
--- model/Chassis.sysml (new)
package Chassis {
    part def Axle;
    part body : Root::Frame;
}

--- model/Drive.sysml (new)
package Drive {
    part axle : Root::Chassis::Axle;
}

--- model.sysml
@@ -3,7 +3,2 @@
-    package Chassis {
-        part def Axle;
-        part body : Frame;
-    }
-    package Drive {
-        part axle : Chassis::Axle;
-    }
+    public import Chassis;
+    public import Drive;
```

Without it the files are written and the root is rewritten in place; the pieces check clean together, and running `split` again on a moved file splits deeper:

```console
$ $sysmlv2 refactor split model.sysml Root
model/Chassis.sysml: `Root::Chassis` (73 bytes)
model/Drive.sysml: `Root::Drive` (56 bytes)
created model/Chassis.sysml
created model/Drive.sysml
split `Root` — rewrote model.sysml
$ cat model.sysml
package Root {
    part def Frame;
    public import Chassis;
    public import Drive;
}
$ $sysmlv2 check model.sysml model/*.sysml && echo clean
clean
```

---

## 19. `lsp` — the language server

`sysmlv2 lsp` speaks the Language Server Protocol over stdio until the client ends the session — an editor runs it, not a terminal. It serves parse and body-context diagnostics on every change, whole-document formatting, outline, semantic tokens, navigation, completion, hover, inlay hints, code lenses and refactorings; `--lib` (or `SYSMLV2_LIB_DIR`) adds the standard library so hover, definition, references and rename resolve library names too, and lint findings surface as diagnostics with their fixes as quick fixes. The dialect follows the file extension (`.kerml` is KerML, everything else SysML). Client configuration for VS Code, Neovim and Helix is in [editors/vscode/README.md](editors/vscode/README.md).

```console
$ $sysmlv2 lsp --help | head -1
Run the Language Server Protocol server over stdio
```

---

## Exit codes

| Command | 0 | 1 |
|---|---|---|
| `parse` | no diagnostics | any diagnostic |
| `check` | all files parse and validate | any parse or context error (`--strict`: any finding) |
| `lint` | no error-severity finding | an error finding, a parse error, or a `--fix` that would break a file or cannot be written (`--strict`: any finding) |
| `fmt` | formatted / already canonical | I/O or parse failure |
| `fmt --check` | all files canonical | some file would be reformatted |
| `convert` | conversion written | read/parse/convert failure |
| `eval` | all named features evaluate | parse failure, unresolved name, or evaluation error |
| `query` | the expression evaluates | expression/parse failure, unresolved reference, or evaluation error |
| `verify` | no violated constraint | any violation (incl. Z3-proved unsatisfiable) |
| `viz` | diagram written | read/parse failure or unknown --element |
| `describe` | element described | read/parse failure or unresolved name |
| `members` | members listed | read/parse failure or unresolved name |
| `refactor extract` | extracted (or `--dry-run` diff printed) | refusal (named reason), unresolved name, read/parse/write failure |
| `refactor inline` | inlined (or `--dry-run` diff printed) | refusal (named reason), unresolved name, read/parse/write failure |
| `refactor split` | new files written (or `--dry-run` plan printed) | refusal (named reason), unresolved name, read/parse/write failure |

A value an enumerated option does not accept — `--to`, `--format`, `--view`, `--line-style` — is a usage error: the message lists the possible values and the status is 2, the same as a missing argument or an unknown flag.

Every subcommand's `--help` carries worked examples (enforced by `tests/cli.rs`).
