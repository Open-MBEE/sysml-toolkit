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
const { Session, check, version } = require(join(here, "pkg-node", "sysmlv2.js"));

console.log(`sysmlv2-wasm ${version()}`);

// Parse error -> positioned finding.
const bad = JSON.parse(check(JSON.stringify([{ name: "bad.sysml", text: "part def {" }])));
assert.equal(bad[0].severity, "error");
assert.equal(bad[0].unit, "bad.sysml");
assert.ok(bad[0].line >= 1);

// Session -> diagram.
const model = JSON.stringify([
  {
    name: "flashlight.sysml",
    text: "package Flashlight { part def Body; part flashlight { part body : Body; } }",
  },
]);
const session = Session.fromSources(model);
const uml = session.toPlantuml(JSON.stringify({ view: "tree" }));
assert.ok(uml.startsWith("@startuml"), "PlantUML emission");

// Interchange round-trip.
const back = Session.fromInterchangeJson(session.toFullJson(true));
assert.ok(back.resolve("Flashlight::flashlight::body"), "round-trip resolve");

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

console.log("smoke: ok");
