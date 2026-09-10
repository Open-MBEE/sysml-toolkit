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

`Session.to_plantuml(view=…)` renders any of seven PlantUML views (structure tree, interconnection, state, action, sequence, use case, mixed) with options for notes, metadata, inherited members, colors, and clickable source hyperlinks; `sysmlv2.check(sources)` runs the CLI's validation pipeline in-process.

Build from source with [maturin](https://maturin.rs): `maturin develop` in `crates/sysmlv2-py/`. A worked tour with real outputs lives in `SDK.md` at the repository root.
