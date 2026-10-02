// End-to-end smoke of the built wasm module under node, against
// the real standard-library bundle + snapshot. Run build.mjs
// first (pkg-node/ + pkg/stdlib/ must exist).
//
//   node crates/sysmlv2-wasm/npm/smoke.mjs

import { readFileSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";
import { gunzipSync } from "node:zlib";
import assert from "node:assert/strict";

const here = dirname(fileURLToPath(import.meta.url));
const require = createRequire(import.meta.url);
const { PreparedLibrary, Session, check, version } = require(join(here, "pkg-node", "sysmlv2.js"));

console.log(`sysmlv2-wasm ${version()}`);

// Parse error -> positioned finding.
const bad = JSON.parse(check(JSON.stringify([{ name: "bad.sysml", text: "part def {" }])));
assert.equal(bad[0].severity, "error");
assert.equal(bad[0].stage, "parse");
assert.equal(bad[0].unit, "bad.sysml");
assert.ok(bad[0].line >= 1);

// Exercise the linked module's real stack and conversion paths, rather
// than relying only on native threads with an equivalent reservation.
const chainSource = "attribute sum = " + Array(1025).fill("1").join(" + ") + ";";
const chainSession = Session.fromSources(JSON.stringify([{ name: "chain.sysml", text: chainSource }]));
for (const payload of [chainSession.toCompactJson(), chainSession.toFullJson(true)]) {
  const lifted = Session.fromInterchangeJson(payload);
  assert.equal(lifted.query("sum"), "1025", "every operand survives lifting");
  lifted.free();
}
chainSession.free();
const deepIf = JSON.parse(check(JSON.stringify([{ name: "deep.sysml",
  text: "action a { " + "if true {} else ".repeat(1000) + "{} }" }])));
assert.ok(deepIf.some(d => d.message.includes("nesting is too deep")), "else-if depth is diagnosed without trapping");

// Session -> diagram.
const model = JSON.stringify([
  {
    name: "flashlight.sysml",
    text: "package Flashlight { part def Body; part flashlight { part body : Body; } }",
  },
]);
const session = Session.fromSources(model);
// Numbers cross exactly: a terminating decimal is a JSON number, any
// other rational an explicit fraction with a double approximation.
assert.equal(JSON.parse(session.query("0.1 + 0.2")), 0.3);
assert.equal(session.query("0.1 + 0.2 == 0.3"), "true");
assert.deepEqual(JSON.parse(session.query("1 / 3")), { "@rational": "1/3", approx: 1 / 3 });
assert.equal(JSON.parse(session.query("2 ** 200"))["@rational"], `${2n ** 200n}/1`);
const uml = session.toPlantuml(JSON.stringify({ view: "tree" }));
assert.ok(uml.startsWith("@startuml"), "PlantUML emission");

// Interchange round-trip.
const back = Session.fromInterchangeJson(session.toFullJson(true));
assert.ok(back.resolve("Flashlight::flashlight::body"), "round-trip resolve");

// Anonymous graph nodes have IDs, but deliberately have no qualified name.
const anonymous = Session.fromSources(JSON.stringify([{ name: "anonymous.sysml", text:
  "package P { action a; action b; succession first a then b; constraint { true } }" }]));
const graph = JSON.parse(anonymous.toGraph(JSON.stringify({ view: "tree" })));
assert.equal(typeof anonymous.elementById, "function", "ID lookup is exposed to JavaScript");
for (const kind of ["ConstraintUsage", "SuccessionAsUsage"]) {
  const node = graph.nodes.find(n => n.metaclass === kind);
  assert.ok(node && !node.qname, kind + " is anonymous");
  const element = anonymous.elementById(node.id);
  assert.ok(element, kind + " is reachable by graph ID");
  assert.equal(anonymous.metaclass(element), kind);
  assert.equal(anonymous.qualifiedName(element), undefined);
  assert.ok(anonymous.declarationSite(element));
}
assert.equal(anonymous.elementById("not-an-id"), undefined);
assert.equal(anonymous.elementById("00000000-0000-0000-0000-000000000000"), undefined);

// Real standard library: bundle + sealed snapshot. The library-typed
// source below only checks clean when stdlib resolution works, and the
// snapshot must make the warm build decisively faster than the cold one
// (replay engaged — this is the point of the snapshot, so it is asserted, not
// just printed).
const stdlibDir = join(here, "pkg", "stdlib");
const bundle = gunzipSync(readFileSync(join(stdlibDir, "sysml-library.json.gz"))).toString();
const snapshot = new Uint8Array(gunzipSync(readFileSync(join(stdlibDir, "sysml-library.libcache.gz"))));
const user = JSON.stringify([
  {
    name: "demo.sysml",
    text: `package Demo {
      private import ScalarValues::*;
      part def Vehicle { attribute mass : Real = 1500.0; }
      part car : Vehicle;
    }`,
  },
]);
const t0 = performance.now();
const cold = JSON.parse(check(user, bundle));
const t1 = performance.now();
const warm = JSON.parse(check(user, bundle, snapshot));
const t2 = performance.now();
assert.deepEqual(cold, [], `cold check clean, got ${JSON.stringify(cold)}`);
assert.deepEqual(warm, [], `warm check clean, got ${JSON.stringify(warm)}`);
const coldMs = t1 - t0;
const warmMs = t2 - t1;
console.log(`stdlib check: cold ${coldMs.toFixed(0)} ms, warm (snapshot) ${warmMs.toFixed(0)} ms`);
assert.ok(
  warmMs * 1.5 < coldMs,
  `snapshot replay must be decisively faster (cold ${coldMs.toFixed(0)} ms, warm ${warmMs.toFixed(0)} ms)`
);

// Library-aware session navigation over the bundle.
const s2 = Session.fromSources(user);
s2.loadLibrarySources(bundle, snapshot);
const real = s2.resolve("ScalarValues::Real");
assert.ok(real, "stdlib element resolves");
assert.ok(s2.isLibraryElement(real));

// A session started from the outcomes the previous build settled on answers
// as a cold one — over the same units and after an edit — and the outcomes
// outlive the session that produced them, so the host frees it first.
const settledLibrary = new PreparedLibrary(bundle, snapshot);
const workspace = (carName) => JSON.stringify([
  {
    name: "defs.sysml",
    text: `package VehicleDefs {
      private import ISQ::*;
      part def Vehicle { attribute mass : MassValue; part engine : Engine; }
      part def Engine { attribute power : PowerValue; port fuelIn : FuelPort; }
      port def FuelPort { in item fuel : Fuel; }
      item def Fuel;
      calc def KineticEnergy { in m : MassValue; in v : SpeedValue; return : EnergyValue = 0.5 * m * v ** 2; }
    }`,
  },
  {
    name: "usage.sysml",
    text: `package VehicleUsage {
      private import VehicleDefs::*;
      private import ISQ::*;
      private import SI::*;
      part ${carName} : Vehicle {
        attribute :>> mass = 1500 [kg];
        part :>> engine { attribute :>> power = 150000 [W]; }
      }
      part tank { port fuelOut : ~FuelPort; }
      connect tank.fuelOut to ${carName}.engine.fuelIn;
      attribute ke : EnergyValue = KineticEnergy(${carName}.mass, 30 [m/s]);
    }`,
  },
  {
    name: "views.sysml",
    text: `package VehicleViews {
      private import VehicleUsage::*;
      private import Views::*;
      view def PartTree;
      view carTree : PartTree { expose car::**; render asTreeDiagram; }
    }`,
  },
]);
const answerOf = (session) => session.toFullJson(true) + "\n" + session.check() + "\n" + session.unresolvedCount();
const previous = Session.fromSourcesWithPreparedLibrary(workspace("car"), settledLibrary);
const previousAnswer = answerOf(previous);
const settled = previous.settledOutcomes();
assert.ok(settled, "a build on the prepared library keeps the outcomes it settled on");
assert.equal(settled.unitCount(), 3);
previous.free();
const t3 = performance.now();
const sameSeeded = Session.fromSourcesSettled(workspace("car"), settledLibrary, settled);
const sameSeededMs = performance.now() - t3;
assert.equal(answerOf(sameSeeded), previousAnswer, "the same units again");
sameSeeded.free();
const t4 = performance.now();
const editedCold = Session.fromSourcesWithPreparedLibrary(workspace("truck"), settledLibrary);
const editedColdMs = performance.now() - t4;
const t5 = performance.now();
const editedSeeded = Session.fromSourcesSettled(workspace("truck"), settledLibrary, settled);
const editedSeededMs = performance.now() - t5;
assert.equal(answerOf(editedSeeded), answerOf(editedCold), "after a rename that unresolves another unit's references");
assert.ok(JSON.parse(editedSeeded.check()).length > 0, "the rename leaves findings");
settled.free();
editedCold.free();
editedSeeded.free();
settledLibrary.free();
console.log(`settled start: same units ${sameSeededMs.toFixed(1)} ms; after an edit cold ${editedColdMs.toFixed(1)} ms, seeded ${editedSeededMs.toFixed(1)} ms`);

// Shared graph preparation preserves results, including after the host releases
// its handle. Each session keeps its own reference and resolver state.
const prepared = new PreparedLibrary(bundle, snapshot);
const shared = Session.fromSourcesWithPreparedLibrary(user, prepared);
const sibling = Session.fromSourcesWithPreparedLibrary(user, prepared);
assert.equal(shared.toCompactJson(), s2.toCompactJson());
assert.equal(shared.toFullJson(true), s2.toFullJson(true));
assert.equal(shared.check(), s2.check());
const liftedShared = Session.fromInterchangeJsonWithPreparedLibrary(shared.toCompactJson(), prepared);
assert.deepEqual(JSON.parse(liftedShared.check()), []);
liftedShared.free();
prepared.free();

// The prepared snapshot decodes for the package's own bundle, equals the
// source-prepared graph, and is refused for any other bundle.
const preparedBytes = new Uint8Array(gunzipSync(readFileSync(join(stdlibDir, "sysml-library.prepared.gz"))));
const tDecoded = performance.now();
const decoded = PreparedLibrary.fromSnapshot(preparedBytes, bundle, snapshot);
console.log(`stdlib prepared snapshot: decoded in ${(performance.now() - tDecoded).toFixed(0)} ms`);
const overDecoded = Session.fromSourcesWithPreparedLibrary(user, decoded);
assert.equal(overDecoded.toCompactJson(), shared.toCompactJson());
assert.equal(overDecoded.check(), shared.check());
overDecoded.free();
decoded.free();
// ... and streamed from the host's buffer, one window at a time.
const tStreamed = performance.now();
const streamed = PreparedLibrary.fromSnapshotStream(preparedBytes, bundle, snapshot);
console.log(`stdlib prepared snapshot: streamed in ${(performance.now() - tStreamed).toFixed(0)} ms`);
const overStreamed = Session.fromSourcesWithPreparedLibrary(user, streamed);
assert.equal(overStreamed.toCompactJson(), shared.toCompactJson());
overStreamed.free();
streamed.free();
const flipped = new Uint8Array(preparedBytes);
flipped[flipped.length - 1] ^= 0xff;
assert.throws(() => PreparedLibrary.fromSnapshotStream(flipped, bundle, snapshot), "a corrupt snapshot is refused after the decode");
assert.throws(
  () => PreparedLibrary.fromSnapshot(preparedBytes, JSON.stringify([...JSON.parse(bundle), { name: "x.sysml", text: "package X;" }]), snapshot),
  /another toolkit build or from other library units/,
  "a snapshot of other units is refused"
);
shared.edit(JSON.stringify([{ op: "rename", target: "Demo::car", newName: "vehicle" }]));
const edited = shared.resolve("Demo::vehicle");
assert.ok(edited);
edited.free();
assert.equal(sibling.toCompactJson(), s2.toCompactJson());
assert.deepEqual(JSON.parse(shared.check()), []);
shared.free();
sibling.free();

console.log("smoke: ok");
