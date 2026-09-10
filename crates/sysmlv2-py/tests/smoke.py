"""Smoke test of the sysmlv2 Python binding — the whole public surface."""
import json
import sysmlv2

DEMO = """package Defs {
    // the wheel family
    part def Wheel;
    part def SpareWheel :> Wheel;
}
package Rig {
    private import Defs::Wheel;
    part def Vehicle {
        part front : Wheel;
        part spare : Defs::SpareWheel;
        attribute count = 2;
    }
    part v : Vehicle;
}
"""

s = sysmlv2.Session.from_sources([("t.sysml", DEMO)])
assert s.unresolved_count() == 0

# --- navigation ---
wheel = s.resolve("Defs::Wheel")
vehicle = s.resolve("Rig::Vehicle")
assert wheel is not None and vehicle is not None
assert s.metaclass(wheel) == "PartDefinition"
assert s.qualified_name(vehicle) == "Rig::Vehicle"
assert s.name(wheel) == "Wheel"
assert [s.name(m) for m in s.features(vehicle)] == ["front", "spare", "count"]
assert s.qualified_name(s.owner(vehicle)) == "Rig"
spare_def = s.resolve("Defs::SpareWheel")
assert s.conforms(spare_def, wheel) and not s.conforms(wheel, spare_def)
front = s.resolve("Rig::Vehicle::front")
assert s.typings(front) == [wheel]
assert len(s.elements_of_metaclass("PartDefinition")) == 3
assert not s.is_library_element(wheel)

# --- find-usages ---
refs = s.references(wheel)
assert len(refs) == 3, refs
assert any(r.kind == "importedMembership" for r in refs)
assert all(r.target == wheel for r in refs)

# --- query (KerML expressions, query-mode semantics) ---
q = s.query("ownedFeature(Rig::Vehicle)->select { in p; p istype Defs::Wheel }")
assert [s.name(e) for e in q] == ["front", "spare"], q
assert s.query("Rig::Vehicle::count + 1") == 3
assert s.query("2 ** 10") == 1024
count = s.resolve("Rig::Vehicle::count")
assert s.evaluate(count) == 2

# --- edits ---
edit = s.edit()
edit.rename(wheel, "RoadWheel")
edit.set_feature_value(count, "4")
edit.insert_member(vehicle, "part rear : RoadWheel;")
assert len(edit) == 3
report = s.commit(edit)
assert isinstance(report.id_map, list) and len(report.id_map) > 0
text = s.units()[0][2]
assert "part front : RoadWheel;" in text
assert "// the wheel family" in text          # notes preserved
assert "attribute count = 4;" in text
assert s.unresolved_count() == 0

# stale handles raise after commit
try:
    s.name(wheel)
    raise AssertionError("stale handle must raise")
except ValueError:
    pass

# a consumed batch cannot commit twice
try:
    s.commit(edit)
    raise AssertionError("double commit must raise")
except ValueError:
    pass

# --- semantic-identity rollback ---
before = s.units()[0][2]
t = sysmlv2.Session.from_sources([
    ("u.sysml", "package P { part def T; package Q { part def U; part x : T; } }"),
])
u = t.resolve("P::Q::U")
bad = t.edit()
bad.rename(u, "T")
try:
    t.commit(bad)
    raise AssertionError("shadow capture must raise")
except RuntimeError as e:
    assert "would resolve to" in str(e), e
assert t.resolve("P::Q::U") is not None       # rolled back

# --- retarget ---
s2 = sysmlv2.Session.from_sources([("t.sysml", DEMO)])
w2 = s2.resolve("Defs::Wheel")
site = next(r for r in s2.references(w2) if r.kind == "type")
e2 = s2.edit()
e2.retarget(site, s2.resolve("Defs::SpareWheel"))
s2.commit(e2)
assert "part front : Defs::SpareWheel;" in s2.units()[0][2]

# --- JSON path ---
out = s2.to_compact_json()
elements = json.loads(out)
for e in elements:
    if e["@type"] == "Namespace" and not e.get("owningRelationship"):
        e["qualifiedName"] = "t.sysml"        # Flexo naming convention
j = sysmlv2.Session.from_interchange_json(json.dumps(elements))
assert j.warnings() == []
assert j.units()[0][1] == "t.sysml"
assert j.resolve("Rig::Vehicle") is not None
assert json.loads(j.to_compact_json())[0]["@id"] == elements[0]["@id"]  # id-stable
assert j.id_map_from(json.dumps(elements)) == []
full = json.loads(j.to_full_json())
assert len(full) >= len(elements)

# recover_refs: dangling references survive full-form emit -> reload
p = sysmlv2.Session.from_sources([("p.sysml", "package P { part x : Missing; }")])
r = sysmlv2.Session.from_interchange_json(p.to_full_json(recover_refs=True))
assert "part x : Missing;" in r.units()[0][2]
r2 = sysmlv2.Session.from_interchange_json(p.to_full_json(recover_refs=False))
assert "Missing" not in r2.units()[0][2]      # the opt-out stays lossy

# --- error surfaces ---
try:
    s2.query("1 +")
    raise AssertionError("bad expression must raise")
except ValueError:
    pass

# --- check: the CLI check pipeline as a library call ---
bad = sysmlv2.check([("bad.sysml", "package Bad {\n  part p : ;\n}")])
assert bad and bad[0].severity == "error"
assert (bad[0].unit, bad[0].line, bad[0].col) == ("bad.sysml", 2, 12)
assert sysmlv2.check([("ok.sysml", "package Ok { part def A; part a : A; }")]) == []

# --- to_plantuml: PlantUML emission, one call per view ---
puml = sysmlv2.Session.from_sources(
    [("v.sysml", "package V { part def A; part a : A; }")]
).to_plantuml()
assert puml.startswith("@startuml") and puml.endswith("@enduml\n")
assert "<<part def>>" in puml and "..>" in puml
viz = sysmlv2.Session.from_sources(
    [(
        "w.sysml",
        "package W {\n"
        "  part a { port p; }\n"
        "  part b { port q; }\n"
        "  connection c1 connect a.p to b.q;\n"
        "  state def S { state On; state Off; transition first On then Off; }\n"
        "  action def A { action s1; first s1 then done; }\n"
        "  part c { event occurrence e1; }\n"
        "  part d { event occurrence e2; }\n"
        "  message m1 from c.e1 to d.e2;\n"
        "}\n",
    )]
)
ic = viz.to_plantuml(view="interconnection")
assert "rectangle" in ic and " : c1" in ic
state = viz.to_plantuml(view="state")
assert "<<state def>>" in state and "-->" in state
action = viz.to_plantuml(view="action")
assert "<<action def>>" in action and "--> [*]" in action
seq = viz.to_plantuml(view="sequence")
assert "participant" in seq and " ->> " in seq and " : m1" in seq
mixed = viz.to_plantuml(view="mixed", std_color=True, link_template="x://{file}:{line}")
assert "rectangle" in mixed and "BackgroundColor<<part def>>" in mixed and "[[x://" in mixed
case = sysmlv2.Session.from_sources(
    [("uc.sysml", "package U { part def D; use case def Go { actor a : D; } }\n")]
).to_plantuml(view="case")
assert "usecase" in case and "actor" in case
try:
    viz.to_plantuml(view="usecase")
    raise AssertionError("unknown view must raise")
except ValueError as e:
    assert "unknown view" in str(e)

# --- minimize_qualifications: shortest reference spellings ---
mq = sysmlv2.Session.from_sources(
    [(
        "mq.sysml",
        "package Lib { part def Wheel; }\n"
        "package Car { private import Lib::*; part w : $::Lib::Wheel; }\n",
    )]
)
ids_before = mq.to_compact_json()
respelled, reverted = mq.minimize_qualifications()
assert respelled >= 1 and reverted == 0, (respelled, reverted)
assert "part w : Wheel;" in mq.source(0)
assert mq.to_compact_json() == ids_before  # declarations untouched: id-stable
assert mq.minimize_qualifications() == (0, 0)  # idempotent

# --- extract / inline definition: the one-sided inverse ---
RIG = (
    "package Rig {\n"
    "    part def A;\n"
    "    part engine : A {\n"
    "        attribute mass = 100; // note rides both moves\n"
    "    }\n"
    "}\n"
)
rf = sysmlv2.Session.from_sources([("rig.sysml", RIG)])
b = rf.edit()
b.extract_definition(rf.resolve("Rig::engine"))
rf.commit(b)
assert "part def Engine :> A {" in rf.source(0)
assert "part engine : Engine;" in rf.source(0)
assert rf.resolve("Rig::Engine::mass") is not None
b = rf.edit()
b.inline_definition(rf.resolve("Rig::Engine"))
rf.commit(b)
assert rf.source(0) == RIG  # inline(extract(usage)) is byte-identical

# explicit name, and named refusals surface as ValueError
rf2 = sysmlv2.Session.from_sources([("rig.sysml", RIG)])
b = rf2.edit()
b.extract_definition(rf2.resolve("Rig::engine"), name="Motor")
rf2.commit(b)
assert "part def Motor :> A {" in rf2.source(0)
b = rf2.edit()
b.extract_definition(rf2.resolve("Rig::A"))
try:
    rf2.commit(b)
    raise AssertionError("extract of a definition must raise")
except ValueError as e:
    assert "not an extractable usage" in str(e)

# inline findings: an import left unused by the deletion is reported
imp = sysmlv2.Session.from_sources(
    [
        ("defs.sysml", "package Defs {\n    part def Kit;\n    part def Tool;\n}\n"),
        (
            "use.sysml",
            "package Use {\n    private import Defs::*;\n    part tool : Tool;\n}\n",
        ),
    ]
)
b = imp.edit()
b.inline_definition(imp.resolve("Defs::Tool"))
report = imp.commit(b)
assert any("import now unused" in f for f in report.findings), report.findings
assert "private import Defs::*;" in imp.source(1)  # reported, not removed

assert tuple(int(x) for x in sysmlv2.__version__.split(".")) >= (0, 1, 0)

print("smoke: all assertions passed")
