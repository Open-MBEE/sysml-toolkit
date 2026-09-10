# `sysmlv2` Python SDK tour

A tour of the `sysmlv2` Python module — the transformation SDK (reference-site table, span-splice edit engine, interchange-JSON sessions) driven from Python. Every output shown here is the actual output of the statement above it (the whole tour runs as a doctest — see the end of this file).

Setup — build the extension into the active virtualenv with [maturin](https://maturin.rs) (any CPython ≥ 3.9; the wheel is abi3):

```console
$ pip install maturin
$ cd crates/sysmlv2-py && maturin develop --release
```

The running example is a small two-package model:

```pycon
>>> import sysmlv2
>>> MODEL = """package Defs {
...     // the wheel family
...     part def Wheel {
...         attribute diameter = 660;
...     }
...     part def SpareWheel :> Wheel;
... }
... package Rig {
...     private import Defs::Wheel;
...     part def Vehicle {
...         part front : Wheel;
...         part spare : Defs::SpareWheel;
...         attribute wheelCount = 2;
...     }
...     part v : Vehicle;
... }
... """
```

---

## 1. Sessions

A `Session` owns the parsed, resolved model and every handle into it. Open one from files on disk, from in-memory sources, or from interchange JSON (section 6):

```pycon
>>> s = sysmlv2.Session.from_sources([("demo.sysml", MODEL)])
>>> s.unresolved_count()
0
```

`from_files([...])` does the same for paths (dialect by extension, `.kerml` → KerML). To resolve names from the OMG standard library, call `load_library(dir)` with a checkout of its `sysml.library/` directory — resolution outcomes come from the same warm cache the CLI uses, and quantity values (`10 [mm]`) then evaluate to `(magnitude, unit)` tuples.

`units()` lists the model's units as `(index, name, source)`; `source(i)` returns one unit's current text:

```pycon
>>> [(i, name) for i, name, _text in s.units()]
[(0, 'demo.sysml')]
```

## 2. Navigation

`resolve` takes a qualified name and returns an element handle (or `None`). Handles are opaque; the session answers questions about them:

```pycon
>>> wheel = s.resolve("Defs::Wheel")
>>> vehicle = s.resolve("Rig::Vehicle")
>>> s.metaclass(wheel)
'PartDefinition'
>>> s.qualified_name(vehicle)
'Rig::Vehicle'
>>> [s.name(f) for f in s.features(vehicle)]
['front', 'spare', 'wheelCount']
>>> s.qualified_name(s.owner(vehicle))
'Rig'
```

Typing and conformance walk the explicit specialization closure:

```pycon
>>> front = s.resolve("Rig::Vehicle::front")
>>> s.typings(front) == [wheel]
True
>>> s.conforms(s.resolve("Defs::SpareWheel"), wheel)
True
>>> s.conforms(wheel, s.resolve("Defs::SpareWheel"))
False
>>> len(s.elements_of_metaclass("PartDefinition"))
3
>>> s.is_library_element(wheel)
False
```

`element_id(e)` returns the element's interchange id — the same UUID the JSON emitters use.

## 3. Find usages

`references(e)` returns every place in the sources whose resolution denotes `e` — the reference-site table that powers rename and retarget. Each site carries the serialized property it feeds (`kind`), its unit, and exact byte spans:

```pycon
>>> for r in s.references(wheel):
...     print(r.kind, r.span)
superclassifier (127, 132)
importedMembership (169, 180)
type (226, 231)
```

(`SpareWheel :> Wheel` is the `superclassifier` site; `private import Defs::Wheel` the `importedMembership`; `front : Wheel` the `type`. A qualified spelling like `Defs::SpareWheel` also records a `qualifier` site against `Defs` — renames must respell prefixes too.)

## 4. Queries and evaluation

`query(expr)` evaluates a KerML expression at the root namespace with the CLI's query-mode semantics — closed-world `istype` on model elements plus the reflection functions `ownedMember(x)` / `ownedFeature(x)`. Elements come back as handles, scalars as native Python values:

```pycon
>>> hits = s.query("ownedFeature(Rig::Vehicle)->select { in p; p istype Defs::Wheel }")
>>> [s.name(e) for e in hits]
['front', 'spare']
>>> s.query("Rig::Vehicle::wheelCount + 1")
3
```

`evaluate(e)` evaluates one feature's declared value in place:

```pycon
>>> s.evaluate(s.resolve("Defs::Wheel::diameter"))
660
```

Malformed expressions raise `ValueError` with the parser's diagnostics.

## 5. Batch edits with verified commits

Edits are staged on a batch, then committed atomically. The engine splices the source text span-by-span — everything outside the edit, comments included, is preserved byte-for-byte — and the commit reparses, re-resolves, and verifies **semantic identity**: every untouched reference site must still denote the same element, else the whole batch rolls back.

```pycon
>>> edit = s.edit()
>>> edit.rename(wheel, "RoadWheel")
>>> edit.set_feature_value(s.resolve("Rig::Vehicle::wheelCount"), "4")
>>> edit.insert_member(vehicle, "part rear : RoadWheel;")
>>> len(edit)
3
>>> report = s.commit(edit)
>>> report
<CommitReport 2 id move(s), 0 finding(s)>
>>> print(s.source(0))
package Defs {
    // the wheel family
    part def RoadWheel {
        attribute diameter = 660;
    }
    part def SpareWheel :> RoadWheel;
}
package Rig {
    private import Defs::RoadWheel;
    part def Vehicle {
        part front : RoadWheel;
        part spare : Defs::SpareWheel;
        attribute wheelCount = 4;
        part rear : RoadWheel;
    }
    part v : Vehicle;
}
<BLANKLINE>
```

The report's `id_map` lists `(old id, new id)` for every element whose interchange id moved — ids derive from qualified names, so the rename moved exactly the renamed definition and its owned `diameter`:

```pycon
>>> len(report.id_map)
2
```

Renames only respell sites written with the element's own name — alias and effective-name spellings stay untouched. New text is validated at plan time: unparsable member text, renames to reserved words, and overlapping splices raise `ValueError` before anything is applied.

A successful commit is a new model state: handles minted before it — including the consumed batch itself — are **stale** and raise rather than silently denoting the wrong element:

```pycon
>>> s.name(wheel)
Traceback (most recent call last):
  ...
ValueError: stale handle: the session was edited since it was minted (re-resolve after commit)
>>> s.commit(edit)
Traceback (most recent call last):
  ...
ValueError: stale handle: the session was edited since it was minted (re-resolve after commit)
```

`remove(e)` deletes a member's whole extent, but the commit pre-fails (nothing applied) if other sites still reference the removed element:

```pycon
>>> roadwheel = s.resolve("Defs::RoadWheel")
>>> bad = s.edit()
>>> bad.remove(roadwheel)
>>> s.commit(bad)
Traceback (most recent call last):
  ...
RuntimeError: removing `Defs::RoadWheel` breaks 4 reference(s)
```

And commit-time semantic breakage — here a rename that would let an inner declaration shadow-capture an outer reference — rolls back bit-exact and raises `RuntimeError`:

```pycon
>>> t = sysmlv2.Session.from_sources(
...     [("u.sysml", "package P { part def T; package Q { part def U; part x : T; } }")])
>>> shadow = t.edit()
>>> shadow.rename(t.resolve("P::Q::U"), "T")
>>> t.commit(shadow)
Traceback (most recent call last):
  ...
RuntimeError: edit refused: 1 reference would break: `T` at u.sysml:1:58 (bytes 57..58) would resolve to `P::Q::T` instead of `P::T`
>>> t.resolve("P::Q::U") is not None
True
```

`retarget(site, to)` rewrites one reference site to denote a different element, spelling its qualified name:

```pycon
>>> s2 = sysmlv2.Session.from_sources([("demo.sysml", MODEL)])
>>> w2 = s2.resolve("Defs::Wheel")
>>> site = next(r for r in s2.references(w2) if r.kind == "type")
>>> e2 = s2.edit()
>>> e2.retarget(site, s2.resolve("Defs::SpareWheel"))
>>> _ = s2.commit(e2)
>>> "part front : Defs::SpareWheel;" in s2.source(0)
True
```

(`insert_top_level(unit_name, text)` appends a new top-level member to a named unit — the batch op for adding whole packages.)

### Extract / inline definitions

The refactoring pair moves between the usage-oriented and definition-oriented modeling styles. `extract_definition` lifts a usage's inline body into a fresh definition (UpperCamel of the usage's name unless `name=` says otherwise) and retypes the usage by it; `inline_definition` reverses that for a definition with exactly one typed usage. Both are verified commits — carried references are checked at their new homes, and the touched usage's effective members must be structurally unchanged — and inlining a definition just produced by extract restores the source byte-for-byte:

```pycon
>>> rf = sysmlv2.Session.from_sources([("rig.sysml",
...     "package Rig {\n"
...     "    part def A;\n"
...     "    part engine : A {\n"
...     "        attribute mass = 100;\n"
...     "    }\n"
...     "}\n")])
>>> b = rf.edit()
>>> b.extract_definition(rf.resolve("Rig::engine"))
>>> _ = rf.commit(b)
>>> print(rf.source(0))
package Rig {
    part def A;
    part def Engine :> A {
        attribute mass = 100;
    }
    part engine : Engine;
}
<BLANKLINE>
>>> b = rf.edit()
>>> b.inline_definition(rf.resolve("Rig::Engine"))
>>> _ = rf.commit(b)
>>> print(rf.source(0))
package Rig {
    part def A;
    part engine : A {
        attribute mass = 100;
    }
}
<BLANKLINE>
```

Refusals are named `ValueError`s — an ineligible kind or header, a taken definition name, outside references through the definition — and the session is left untouched.

## 6. Interchange JSON sessions

Sessions round-trip through KerML interchange JSON. `to_compact_json()` / `to_full_json()` emit the current state; `from_interchange_json` opens a session from a compact or full element list — including Flexo MMS `{payload, identity}` change records — by lifting it back to text:

```pycon
>>> import json
>>> elements = json.loads(s2.to_compact_json())
>>> for e in elements:
...     if e["@type"] == "Namespace" and not e.get("owningRelationship"):
...         e["qualifiedName"] = "demo.sysml"    # Flexo names roots by file
>>> j = sysmlv2.Session.from_interchange_json(json.dumps(elements))
>>> j.warnings()
[]
>>> j.resolve("Rig::Vehicle") is not None
True
```

Re-emission is **id-stable** — the unit name prefixes every ownership path, so a payload that came from Flexo goes back with the same ids:

```pycon
>>> json.loads(j.to_compact_json())[0]["@id"] == elements[0]["@id"]
True
```

For payloads produced by foreign tools (or unnamed roots), `id_map_from(input_json)` maps input ids to this session's ids by qualified name — empty when they already agree:

```pycon
>>> j.id_map_from(json.dumps(elements))
[]
```

Library-typed payloads generally need the standard library at lift time — `from_interchange_json(json, lib="<sysml.library dir>")` names library element ids during the lift and keeps the library loaded, like `load_library`. Non-fatal lift problems (unknown properties, unresolvable in-payload refs) land in `warnings()` instead of failing the load. The full form (`to_full_json()`) adds the derived properties and implied relationships the schema materializes and, by default, annotates dangling references with their source spelling. A partial model — one whose references don't all resolve — therefore survives emit → reload losslessly without requiring a Flexo envelope. Pass `recover_refs=False` only for compatibility with the historical lossy form:

```pycon
>>> partial = sysmlv2.Session.from_sources(
...     [("p.sysml", "package P { part x : Missing; }")])
>>> back = sysmlv2.Session.from_interchange_json(partial.to_full_json())
>>> "part x : Missing;" in back.source(0)
True
```

### Minimal reference spellings

The lift prints every reference as an always-correct `$::`-rooted path. `minimize_qualifications()` — the CLI's `convert --to text --min-qual` — respells each with the *shortest* spelling that still resolves to the same element (bare name where unambiguous, a qualified suffix where needed), verified by reparse; a respell that would change any resolution is dropped. It returns `(respelled, reverted)` counts, and because declarations never move, re-emission stays id-stable:

```pycon
>>> "part v : $::Rig::Vehicle;" in j.source(0)
True
>>> j.minimize_qualifications()
(4, 1)
>>> "part v : Vehicle;" in j.source(0)
True
>>> "part front : Defs::SpareWheel;" in j.source(0)
True
>>> json.loads(j.to_compact_json())[0]["@id"] == elements[0]["@id"]
True
```

`front` keeps exactly one qualifier — only `Wheel` is imported into `Rig`, so a bare `SpareWheel` would not resolve; import targets keep their printed form (their resolution rules differ).

---

## 7. Binary interchange (s2c)

The compact form also serializes as **s2c** — a deterministic CBOR encoding an order of magnitude smaller than the JSON (`CBOR.md`): `to_compact_cbor()` returns `bytes` opening with the RFC 9277 file magic, `from_compact_cbor(data, lib=None)` opens a session from them, and `to_full_cbor()` emits the lossless full form:

```pycon
>>> s2c = j.to_compact_cbor()
>>> s2c[:8].hex()                     # tag(55799) + tag(0x24533243)
'd9d9f7da24533243'
>>> len(s2c) < len(j.to_compact_json()) // 10
True
>>> k = sysmlv2.Session.from_compact_cbor(s2c)
>>> k.source(0) == sysmlv2.Session.from_interchange_json(j.to_compact_json()).source(0)
True
```

(The **codec** round trip is byte-exact — decoding reproduces the identical element array — so the binary and JSON ingest paths lift to the same text; opening a *session* is a lift like section 6, with the same root-naming rules.)

Id-elided payloads (`Session::to_compact_cbor_elided` in Rust, CLI `--elide-ids`) and digest-named delta payloads (`delta_cbor_from`, CLI `--delta-base`) are covered in `CBOR.md`.

## 8. Checking models

`sysmlv2.check(sources, lib=None)` runs the `sysmlv2 check` pipeline as a library call: per-unit parse and body-context validation always, plus referential and semantic checks against the standard library when `lib` is given (loaded through the same sealed-snapshot cache as sessions). It returns `Finding`s — severity, message, unit name, and a 1-based line/column — and never raises for model problems, so a broken parse is data, not an exception:

```pycon
>>> bad = sysmlv2.check([("bad.sysml", "package Bad {\n  part p : ;\n}")])
>>> (bad[0].severity, bad[0].unit, bad[0].line, bad[0].col)
('error', 'bad.sysml', 2, 12)
>>> sysmlv2.check([("ok.sysml", "package Ok { part def A; part a : A; }")])
[]
```

With `lib="<sysml.library dir>"`, unresolved references come back as warnings with positions; the CLI's `--strict` gating is caller-side policy — treat warnings as failures if that fits your pipeline:

```python
>>> sysmlv2.check([("d.sysml", "package D { part p : Missing; }")], lib=LIB)
[<Finding warning: unresolved reference `Missing` at d.sysml:1:22>]
```

---

## 9. PlantUML diagrams

`to_plantuml(element=None, view="tree", horizontal=False, show_values=True, show_notes=True, show_metadata=True, show_inherited=False, show_lib=False, show_imported=False, line_style=None, std_color=False, link_template=None)` emits one view of the model as PlantUML text (feed it to any PlantUML build for SVG/PNG; the CLI verb `sysmlv2 viz` is the same emitter). The default `tree` view is the structure diagram — packages, definitions, usages with attribute compartments, plus composition / typing / specialization edges:

```pycon
>>> v = sysmlv2.Session.from_sources(
...     [("v.sysml", "package V { part def A; part a : A; }")])
>>> print(v.to_plantuml(), end="")
@startuml
hide empty members
package "V" as n1 {
  class "A" as n2 <<part def>>
  class "a : A" as n3 <<part>>
}
n3 ..> n2
@enduml
```

`view="interconnection"` renders parts as nested blocks with ports (definition ports render on each usage box) and connector-family usages — connections, interfaces, bindings, allocations, flows — as edges between their resolved ends; `view="state"` and `view="action"` render behavior in the state-diagram dialect (transitions labelled `trigger [guard] / effect`, `[*]` for unspelled or `start`/`done` succession ends, fork/join/choice control nodes, dashed flows); `view="sequence"` renders lifelines and `->>` message arrows, ordered by the events' succession partial order and boxed per owning definition; `view="case"` is the use-case diagram (actors, subjects, objectives with their doc bodies, `«include»` edges); `view="mixed"` puts everything on one canvas:

```pycon
>>> w = sysmlv2.Session.from_sources([("w.sysml", """
... package W {
...     part a { port p; }
...     part b { port q; }
...     connection c1 connect a.p to b.q;
...     state def S { state On; state Off; transition first On then Off; }
... }""")])
>>> print(w.to_plantuml(view="interconnection"), end="")
@startuml
package "W" as n1 {
  rectangle "a" as n2 <<part>> {
    port "p" as n3
  }
  rectangle "b" as n4 <<part>> {
    port "q" as n5
  }
}
n3 -- n5 : c1
@enduml
>>> print(w.to_plantuml(view="state"), end="")
@startuml
state "S" as n1 <<state def>> {
  state "On" as n2 <<state>>
  state "Off" as n3 <<state>>
  n2 --> n3
}
@enduml
>>> s = sysmlv2.Session.from_sources([("s.sysml", """
... package S {
...     part def Chat {
...         part a { event occurrence ping_sent; }
...         part b { event occurrence ping_rcvd; }
...         message ping from a.ping_sent to b.ping_rcvd;
...     }
... }""")])
>>> print(s.to_plantuml(view="sequence"), end="")
@startuml
box "Chat"
participant "a" as n1
participant "b" as n2
end box
n1 ->> n2 : ping
@enduml
```

```pycon
>>> uc = sysmlv2.Session.from_sources([("uc.sysml", """
... package Ops {
...     part def Driver;
...     use case def Drive { actor driver : Driver; objective { doc /* arrive */ } }
... }""")])
>>> print(uc.to_plantuml(view="case"), end="")
@startuml
usecase "Drive" as n1 <<use case def>>
actor "driver : Driver" as n2
n2 -- n1
note as o1
«objective»
arrive 
end note
o1 .. n1
@enduml
```

Every view takes the same keyword options: comment/doc bodies attach as notes (`show_notes=False` omits), prefix metadata joins the stereotype list (`show_metadata=False` hides metadata), `show_inherited=True` adds `^`-marked inherited compartment lines, `show_lib=True` gives referenced library types marked nodes, `show_imported=True` draws `«import»` edges, `line_style="polyline"|"ortho"` picks edge routing, `std_color=True` colors nodes by metaclass family, and `link_template="vscode://file/{file}:{line}"` embeds `[[hyperlinks]]` (placeholders `{file}`/`{line}`/`{col}`/`{qname}`/`{id}`) that PlantUML carries into rendered SVG — diagram nodes click through to source.

`element="V::A"` roots the diagram at one element (unknown names raise `ValueError`, as do an unknown `view` or `line_style`); sessions lifted from interchange JSON diagram the same way — fetch a Flexo element list, `from_interchange_json`, `to_plantuml`.

---

## Running this tour

The code blocks above are doctests over one shared namespace:

```console
$ python tools/sdk_doctour.py        # extracts SDK.md's pycon blocks and runs them
```

`crates/sysmlv2-py/tests/smoke.py` remains the binding's assertion gate; this file is the narrated version.
