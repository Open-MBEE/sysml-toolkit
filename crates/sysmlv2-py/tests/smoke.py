"""Smoke test of the sysmlv2 Python binding — the whole public surface."""
import json
import pathlib
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

# --- the ownership tree ---
# `tree_text` draws what the text lowered to: an element's owned
# relationships, the elements they own in turn, every other end as a
# reference; `tree_json` is the same tree as `sysmlv2 tree --format json`.
# (a usage its type features owns its default multiplicity, SysML 7.6.3,
# as its last member)
VEHICLE_TREE = """Rig::Vehicle [PartDefinition]
├─ FeatureMembership
│  └─ front [PartUsage]
│     ├─ FeatureTyping
│     │  └─ type → Defs::Wheel [PartDefinition]
│     └─ OwningMembership
│        └─ (anonymous) [Multiplicity]
├─ FeatureMembership
│  └─ spare [PartUsage]
│     ├─ FeatureTyping
│     │  └─ type → Defs::SpareWheel [PartDefinition]
│     └─ OwningMembership
│        └─ (anonymous) [Multiplicity]
└─ FeatureMembership
   └─ count [AttributeUsage]
      ├─ FeatureValue
      │  └─ (anonymous) [LiteralInteger]
      └─ OwningMembership
         └─ (anonymous) [Multiplicity]
"""
assert s.tree_text(vehicle) == VEHICLE_TREE
assert s.tree_text("Rig::Vehicle") == VEHICLE_TREE      # a qualified name roots it too
assert s.tree_text().startswith("Defs [Package]\n")     # no root: every top-level element
assert "\nRig [Package]\n" in s.tree_text()
assert "→" not in s.tree_text(references=False)
tree = json.loads(s.tree_json(vehicle, depth=1, ids=True))
assert tree[0]["id"] == s.element_id(vehicle)
assert [r["children"][0]["name"] for r in tree[0]["relationships"]] == ["front", "spare", "count"]
assert tree[0]["relationships"][0]["children"][0]["truncated"] is True   # the depth cut the walk
assert "…" in s.tree_text(vehicle, depth=1)
assert json.loads(s.tree_json(front))[0]["relationships"][0]["references"] == [
    {"property": "type", "target": {"metaclass": "PartDefinition", "name": "Wheel", "qualifiedName": "Defs::Wheel"}}
]
try:
    s.tree_text("Rig::Nope")
    raise AssertionError("an unknown root must raise")
except sysmlv2.RefusedError as e:
    assert "element not found" in str(e), e

# --- derived properties by specification name ---
assert [s.name(f) for f in s.derived(vehicle, "ownedFeature")] == ["front", "spare", "count"]
assert s.derived(vehicle, "name") == "Vehicle"
assert s.derived(vehicle, "shortName") is None
assert s.derived(front, "owningType") == vehicle
assert s.derived(front, "type") == [wheel]
assert sysmlv2.Session.derives("PartUsage", "ownedFeature") == "exact"
assert sysmlv2.Session.derives("PartUsage", "feature") == "passthrough"
assert sysmlv2.Session.derives("PartUsage", "declaredName") == "not-declared"
assert sysmlv2.Session.is_owned_property("PartUsage", "declaredName")
assert "owningNamespace" in sysmlv2.Session.computed_names()
try:
    s.derived(vehicle, "declaredName")
    assert False, "an owned property is not derived"
except KeyError:
    pass
try:
    s.derived(front, "mayTimeVary")
    assert False, "not computed yet"
except NotImplementedError:
    pass
# A target outside the model, and the closure policy's effect.
s2 = sysmlv2.Session.from_sources([("o.sysml", "package O { part w : Missing; part def A { part x; } part def B :> A; }")])
w = s2.resolve("O::w")
[outside] = s2.derived(w, "type")
assert isinstance(outside, sysmlv2.OutsideReference) and outside.spelling == "Missing" and outside.id is None
b = s2.resolve("O::B")
assert s2.derived(b, "feature") == []
assert s2.closure_policy() == "passthrough"
s2.set_closure_policy("closure")
assert s2.closure_policy() == "closure"
assert [s2.name(f) for f in s2.derived(b, "feature")] == ["x"]
closure_edit = s2.edit()
closure_edit.rename(w, "renamed")
s2.commit(closure_edit)
assert s2.closure_policy() == "closure"
s2.set_closure_policy("passthrough")
# The full form's closures are an option of the export, not the session's
# read policy: the default writes `[]`, `closures="closure"` the heritage.
b_row = lambda doc: next(e for e in json.loads(doc) if e.get("declaredName") == "B")
assert b_row(s2.to_full_json())["inheritedFeature"] == []
assert len(b_row(s2.to_full_json(closures="closure"))["inheritedFeature"]) == 1
try:
    s2.to_full_json(closures="everything")
    raise AssertionError("an unknown closure level is refused")
except ValueError as e:
    assert "unknown closure policy" in str(e), e
# The strict export refuses the whole document; the checked export keeps the
# rows and lists the refusals beside them (schema-invalid where a required
# property is missing).
try:
    s2.to_full_json_strict()
    raise AssertionError("a model with an unresolved typing is refused strictly")
except sysmlv2.RefusedError as e:
    assert "strict export refused" in str(e), e
checked = json.loads(s2.to_full_json_checked())
assert len(checked["elements"]) == len(json.loads(s2.to_compact_json()))
assert checked["issues"] and all(set(i) == {"elementId", "property", "kind", "reason"} for i in checked["issues"])
assert any(i["kind"] == "unresolved-reference" for i in checked["issues"])

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
# Exact arithmetic: decimals are rationals, integers are unbounded, and
# only transcendental results are floats.
from fractions import Fraction
assert s.query("0.1 + 0.2") == Fraction(3, 10)
assert s.query("0.1 + 0.2 == 0.3") is True
assert s.query("1 / 3") == Fraction(1, 3)
assert s.query("2.5 * 2") == 5 and isinstance(s.query("2.5 * 2"), int)
assert s.query("2 ** 200") == 2 ** 200
assert isinstance(s.query("sqrt(2)"), float)
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
try:
    s.tree_text(wheel)
    raise AssertionError("a stale tree root must raise")
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
except sysmlv2.RefusedError as e:
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

# Flexo MMS returns change records without owningRelationship and
# owningRelatedElement: refused as they are, read with flexo=True.
records = [
    {"payload": {k: v for k, v in e.items()
                 if k not in ("owningRelationship", "owningRelatedElement")},
     "identity": {"@id": e["@id"]}}
    for e in elements
]
try:
    sysmlv2.Session.from_interchange_json(json.dumps(records))
    raise AssertionError("a payload omitting the back-references is refused")
except sysmlv2.Error as e:
    assert "omits the inverse ownership ends" in str(e), e
f = sysmlv2.Session.from_interchange_json(json.dumps(records), flexo=True)
assert f.units() == j.units()
assert f.to_compact_json() == j.to_compact_json()

# recover_refs: dangling references survive full-form emit -> reload
p = sysmlv2.Session.from_sources([("p.sysml", "package P { part x : Missing; }")])
r = sysmlv2.Session.from_interchange_json(p.to_full_json(recover_refs=True))
assert "part x : Missing;" in r.units()[0][2]
r2 = sysmlv2.Session.from_interchange_json(p.to_full_json(recover_refs=False))
assert "Missing" not in r2.units()[0][2]      # the opt-out stays lossy

# --- error surfaces ---
# Everything the package raises is a sysmlv2.Error; a refusal is also a
# ValueError, which is what callers caught before the base class existed.
assert issubclass(sysmlv2.RefusedError, sysmlv2.Error)
assert issubclass(sysmlv2.RefusedError, ValueError)
assert not issubclass(sysmlv2.Error, ValueError)
assert sysmlv2.Error.__module__ == sysmlv2.RefusedError.__module__ == "sysmlv2"
try:
    s2.query("1 +")
    raise AssertionError("bad expression must raise")
except ValueError as e:
    assert isinstance(e, sysmlv2.RefusedError), type(e)
try:
    s2.to_plantuml(element="Nope::Gone")
    raise AssertionError("unknown element must raise")
except sysmlv2.Error as e:
    assert "element not found" in str(e), e

# --- check: the CLI check pipeline as a library call ---
bad = sysmlv2.check([("bad.sysml", "package Bad {\n  part p : ;\n}")])
assert bad and bad[0].severity == "error" and bad[0].stage == "parse"
assert (bad[0].unit, bad[0].line, bad[0].col) == ("bad.sysml", 2, 12)
assert bad[0].rule is None, "a parse finding names no rule"
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

# explicit name, and named refusals surface as sysmlv2.RefusedError
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

# --- library elements are read-only ---
# Their declarations live in units the session does not hold, so an edit
# naming one is refused before anything is spliced. Needs the standard
# library checkout; skipped without it.
LIBRARY = pathlib.Path(__file__).resolve().parents[3] / "spec-refs/SysML-v2-Release/sysml.library"
if LIBRARY.is_dir():
    lb = sysmlv2.Session.from_sources(
        [("u.sysml", "package U {\n    attribute def A;\n    attribute x : A;\n}\n")]
    )
    lb.load_library(str(LIBRARY))
    real = lb.resolve("ScalarValues::Real")
    assert lb.is_library_element(real)
    # The tree spells library targets without expanding them, adds the
    # implied relationships on request, and takes a library root.
    implied = lb.tree_text("U::x", implied=True)
    assert "type → U::A [AttributeDefinition]" in implied, implied
    assert "(implied)" in implied and "[library]" in implied, implied
    assert "(implied)" not in lb.tree_text("U::x")
    assert lb.tree_text(real, depth=1).startswith("ScalarValues::Real [DataType] [library]\n")
    for stage in (
        lambda b: b.rename(real, "Reel"),
        lambda b: b.remove(real),
        lambda b: b.insert_member(real, "attribute q;"),
        lambda b: b.set_feature_value(real, "1"),
        lambda b: b.extract_definition(real),
        lambda b: b.inline_definition(real),
    ):
        batch = lb.edit()
        stage(batch)
        try:
            lb.commit(batch)
            raise AssertionError("editing a library element must raise")
        except sysmlv2.RefusedError as e:
            assert "read-only" in str(e) and "ScalarValues::Real" in str(e), e
    # `check` accepts the library as a path object as well as a string,
    # and reports the same findings either way.
    typo = [("t.sysml", "package T {\n    part p : Nope;\n}\n")]
    by_path = [repr(f) for f in sysmlv2.check(typo, LIBRARY)]
    assert by_path == [repr(f) for f in sysmlv2.check(typo, str(LIBRARY))]
    assert any("Nope" in line for line in by_path), by_path

    # Retargeting a user site *to* a library element stays legal.
    site = next(r for r in lb.references(lb.resolve("U::A")) if r.kind == "type")
    batch = lb.edit()
    batch.retarget(site, real)
    lb.commit(batch)
    assert "attribute x : ScalarValues::Real;" in lb.units()[0][2]
else:
    print("smoke: no standard library checkout — library refusals not exercised")

# --- binary delta: an edit ships as its changes against a store's head ---
head = sysmlv2.Session.from_sources([("t.sysml", DEMO)])
head_json = head.decode_cbor(head.to_compact_cbor())
assert isinstance(json.loads(head_json), list)
edited = sysmlv2.Session.from_sources([("t.sysml", DEMO.replace("part v : Vehicle;", "part v : Vehicle;\n    part w : Vehicle;"))])
for portable in (False, True):
    delta = edited.delta_cbor_from_head(head_json, portable=portable)
    assert isinstance(delta, bytes) and 0 < len(delta) < len(edited.to_compact_cbor()), (portable, len(delta))
# --- a push between two stores: the receiver's head to the sender's state ---
push, pushed_digest, fallback = sysmlv2.store_delta_cbor(head.to_compact_cbor(), edited.to_compact_cbor())
assert isinstance(push, bytes) and 0 < len(push) < len(edited.to_compact_cbor())
assert fallback is None and len(pushed_digest) == 36
try:
    sysmlv2.store_delta_cbor(b"not s2c", edited.to_compact_cbor())
    raise AssertionError("a malformed base is refused")
except sysmlv2.FailedError:
    pass

try:
    edited.delta_cbor_from_head("not json")
    raise AssertionError("a malformed head is refused")
except sysmlv2.RefusedError:
    pass

# --- units as written ---
UNITS = """package U {
    attribute m; attribute s;
    attribute 'in' { attribute unitConversion { attribute referenceUnit = m; attribute conversionFactor = 0.0254; } }
    attribute d = 10 ['in'];
    attribute v = d / (2 [s]);
}
"""
u = sysmlv2.Session.from_sources([("u.sysml", UNITS)])
assert sysmlv2.value_units() == "si"
assert u.query("U::v") == (Fraction(127, 1000), "m/s")
assert "v = 0.127 [m/s]" in u.to_plantuml()
assert "v = 5 [in/s]" in u.to_plantuml(value_units="asWritten")
try:
    u.to_plantuml(value_units="as-written")
    raise AssertionError("an unknown value_units must raise")
except sysmlv2.RefusedError as e:
    assert "asWritten" in str(e), e
sysmlv2.set_value_units("asWritten")
try:
    assert sysmlv2.value_units() == "asWritten"
    assert u.query("U::v") == (5, "in/s")
    assert u.query("(U::v, U::d, 3)") == [(5, "in/s"), (10, "in"), 3]
    assert u.evaluate(u.resolve("U::v")) == (5, "in/s")
    assert "v = 5 [in/s]" in u.to_plantuml()
    assert "v = 0.127 [m/s]" in u.to_plantuml(value_units="si")
    try:
        sysmlv2.set_value_units("SI")
        raise AssertionError("an unknown mode must raise")
    except ValueError:
        pass
    assert sysmlv2.value_units() == "asWritten"
finally:
    sysmlv2.set_value_units("si")
assert u.query("U::v") == (Fraction(127, 1000), "m/s")

server = sysmlv2.LspServer()
server.handle(json.dumps({"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"capabilities": {}}}))
server.handle(json.dumps({"jsonrpc": "2.0", "method": "initialized", "params": {}}))
server.handle(json.dumps({"jsonrpc": "2.0", "method": "textDocument/didOpen", "params": {"textDocument": {"uri": "file:///w/u.sysml", "languageId": "sysml", "version": 1, "text": UNITS}}}))
def unit_hints():
    out = server.handle(json.dumps({"jsonrpc": "2.0", "id": 2, "method": "textDocument/inlayHint", "params": {"textDocument": {"uri": "file:///w/u.sysml"}, "range": {"start": {"line": 0, "character": 0}, "end": {"line": 6, "character": 0}}}}))
    reply = next(json.loads(m) for m in out if json.loads(m).get("id") == 2)
    return [h["label"] for h in reply["result"]]
assert " = 0.127 [m/s]" in unit_hints()
server.set_value_hint_units("asWritten")
assert " = 5 [in/s]" in unit_hints()
try:
    server.set_value_hint_units("as-written")
    raise AssertionError("an unknown mode must raise")
except ValueError:
    pass

assert tuple(int(x) for x in sysmlv2.__version__.split(".")) >= (0, 1, 0)

print("smoke: all assertions passed")
