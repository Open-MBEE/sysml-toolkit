# sysmlv2 (Python)

Python binding for the [sysmlv2](https://github.com/Open-MBEE/sysml-toolkit) SysML v2 / KerML toolkit: open textual models or interchange JSON as a **session**, navigate and query them with KerML expressions, and apply **span-splice transformations** — rename, set value, insert, remove, retarget — whose commits reparse, re-resolve, and verify that untouched references kept their targets (or roll back).

```python
import sysmlv2

s = sysmlv2.Session.from_files(["model.sysml"])
vehicle = s.resolve("Demo::Vehicle")
wheels = s.query("ownedFeature(Demo::Vehicle)->select { in p; p istype Demo::Wheel }")

edit = s.edit()
edit.rename(s.resolve("Demo::Wheel"), "RoadWheel")
edit.set_feature_value(s.resolve("Demo::Vehicle::count"), "4")
report = s.commit(edit)          # raises (and rolls back) on semantic breakage
print(report.id_map)             # old -> new interchange ids for moved elements

payload = sysmlv2.Session.from_interchange_json(json_text)   # Flexo MMS path
json_out = payload.to_compact_json()
```

Element and reference handles belong to one committed state of the session; a successful commit invalidates them (methods raise on stale handles) — re-resolve after committing.

Everything the module raises derives from `sysmlv2.Error`, so `except sysmlv2.Error` catches the toolkit's failures and nothing else. A refusal — an argument the toolkit cannot use, a handle from a superseded session state, an edit naming a read-only library element, an edit whose commit would change what an untouched reference denotes — is `sysmlv2.RefusedError`, which derives from `sysmlv2.Error` and from `ValueError`, so `except ValueError` keeps catching every refusal it caught before.

`Session.to_plantuml(view=…)` renders any of seven PlantUML views (structure tree, interconnection, state, action, sequence, use case, mixed) with options for notes, metadata, inherited members, colors, and clickable source hyperlinks; `sysmlv2.check(sources, lib=None)` runs parse and structural checks in-process, adding referential and semantic checks when `lib` is supplied (a path string or a `pathlib.Path`); it releases the interpreter lock while it runs — a library-backed check takes seconds — so other threads keep going. It does not include the CLI’s unused-private-import analysis. See [the checking API](../../SDK.md#8-checking-models).

Every call parses on the thread that makes it, which this module neither creates nor resizes. The parser bounds how deeply a source may nest — 128 levels of braces — and that bound assumes a stack large enough to descend that far; a thread that has less overflows on input the parser accepts, and a stack overflow ends the interpreter rather than raising anything catchable. Sources written by hand never come close (the published example and library models nest ten levels), machine-generated ones can: for those, raise `threading.stack_size(16 * 1024 * 1024)` before the thread that will parse. [The tour](../../SDK.md#deeply-nested-sources) shows one way to run a call there and get its result — or its exception — back.

Build from source with [maturin](https://maturin.rs): `maturin develop` in `crates/sysmlv2-py/`. A worked tour with real outputs lives in `SDK.md` at the repository root.
