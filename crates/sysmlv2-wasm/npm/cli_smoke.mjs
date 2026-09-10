// Smoke-test the wasi CLI artifact: the real
// `sysmlv2` binary compiled for wasm32-wasip1 and shipped in the npm
// package under cli/. Runs it under node:wasi (preview1) the way a
// browser host runs it under a WASI shim — argv/env in, preopened
// model directory, captured stdio, real exit codes — and asserts the
// ambient-context behavior end to end. CI runs this after build.mjs;
// there is no browser in CI, so this is the artifact's gate.
//
//   node crates/sysmlv2-wasm/npm/cli_smoke.mjs
//
// Env:
//   SYSMLV2_CLI_WASM  artifact path (default: npm/pkg/cli/sysmlv2-cli.wasm)

import {
  closeSync,
  mkdirSync,
  mkdtempSync,
  openSync,
  readFileSync,
  rmSync,
  statSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { WASI } from "node:wasi";

const npmDir = resolve(dirname(fileURLToPath(import.meta.url)));
const wasmPath =
  process.env.SYSMLV2_CLI_WASM ?? join(npmDir, "pkg", "cli", "sysmlv2-cli.wasm");

// Size budget: the artifact is fetched lazily by browsers; growth past
// this line should be a conscious decision, not drift.
const SIZE_BUDGET = 4 * 1024 * 1024;
const size = statSync(wasmPath).size;
if (size > SIZE_BUDGET) {
  throw new Error(`cli wasm is ${size} bytes — over the ${SIZE_BUDGET} budget`);
}
console.log(`artifact: ${wasmPath} (${(size / 1024 / 1024).toFixed(2)} MB)`);

const mod = new WebAssembly.Module(readFileSync(wasmPath));
const work = mkdtempSync(join(tmpdir(), "sysmlv2-cli-smoke-"));
let runs = 0;

function run(args, { env = {}, preopens = {}, stdinFile } = {}) {
  const outPath = join(work, `out-${runs}`);
  const errPath = join(work, `err-${runs}`);
  runs += 1;
  const stdout = openSync(outPath, "w");
  const stderr = openSync(errPath, "w");
  const stdin = stdinFile ? openSync(stdinFile, "r") : 0;
  try {
    const wasi = new WASI({
      version: "preview1",
      args: ["sysmlv2", ...args],
      env,
      preopens,
      stdin,
      stdout,
      stderr,
      returnOnExit: true,
    });
    const instance = new WebAssembly.Instance(mod, wasi.getImportObject());
    const code = wasi.start(instance);
    return {
      code,
      out: readFileSync(outPath, "utf8"),
      err: readFileSync(errPath, "utf8"),
    };
  } finally {
    closeSync(stdout);
    closeSync(stderr);
    if (stdinFile) closeSync(stdin);
  }
}

function expect(cond, label, r) {
  if (!cond) {
    throw new Error(
      `${label}\n  exit ${r?.code}\n  stdout: ${r?.out}\n  stderr: ${r?.err}`
    );
  }
  console.log(`ok: ${label}`);
}

// The ambient model directory, preopened at /model.
const modelDir = join(work, "model");
mkdirSync(modelDir);
writeFileSync(
  join(modelDir, "chassis.sysml"),
  "package Chassis {\n    part def Frame {\n        attribute mass = 42.0;\n    }\n}\n"
);
writeFileSync(
  join(modelDir, "power.sysml"),
  "package Rover {\n    private import Chassis::*;\n    part base : Frame;\n    attribute payload = 8.5;\n    attribute totalMass = base.mass + payload;\n}\n"
);
writeFileSync(
  join(modelDir, "limits.sysml"),
  "package Limits {\n    attribute def Real;\n    attribute x : Real;\n    assert constraint lo { x >= 1 }\n    assert constraint hi { x <= 5 }\n}\n"
);
const ambient = {
  env: { SYSMLV2_MODEL_DIR: "/model" },
  preopens: { "/model": modelDir },
};

let r = run(["--version"]);
expect(r.code === 0 && /^sysmlv2 \d/.test(r.out), "--version", r);

r = run(["check"], ambient);
expect(
  r.code === 0 && r.err.includes("model = 3 files from /model (SYSMLV2_MODEL_DIR)"),
  "ambient check + provenance",
  r
);

r = run(["-q", "convert", "--to", "compact-json"], ambient);
const elements = JSON.parse(r.out);
expect(
  r.code === 0 &&
    r.err === "" &&
    Array.isArray(elements) &&
    elements.some((e) => e["@type"] === "PartDefinition"),
  "ambient convert to compact JSON, quiet stderr clean",
  r
);

r = run(["-q", "query", "Rover::totalMass + 1"], ambient);
expect(r.code === 0 && r.out.trim() === "51.5", "ambient query expression", r);

r = run(["-q", "describe", "Rover::base"], ambient);
expect(
  r.code === 0 &&
    r.out.includes("metaclass  PartUsage") &&
    r.out.includes("type       Chassis::Frame") &&
    r.out.includes("location   /model/power.sysml:3:10"),
  "ambient describe",
  r
);

r = run(["-q", "verify", "--ranges"], ambient);
expect(
  r.code === 0 && r.out.includes("2 satisfied, 0 violated, 0 undecided"),
  "verify --ranges: propagation decides solverless in wasi",
  r
);

r = run(["-q", "verify", "--solve"], ambient);
expect(
  r.code === 1 && r.err.includes("Z3 is not available"),
  "verify --solve degrades with the documented error",
  r
);

r = run(["fmt"], ambient);
expect(
  r.code === 1 && r.err.includes("--check only"),
  "in-place fmt refuses ambient inputs",
  r
);

// Stdin pipeline: `-` reads fd 0 like the native binary.
const stdinModel = join(work, "stdin.sysml");
writeFileSync(stdinModel, "package P { part def V; }\n");
r = run(["convert", "-", "--to", "compact-json"], { stdinFile: stdinModel });
expect(
  r.code === 0 && JSON.parse(r.out).some((e) => e["@type"] === "PartDefinition"),
  "stdin convert",
  r
);

// The refactor in-place path uses same-directory staging and replacement;
// exercise the WASI filesystem implementation, then require the
// extract→inline inverse to restore the host file byte-for-byte.
const refactorModel = join(modelDir, "refactor.sysml");
const refactorSource =
  "package Txn {\n" +
  "    part def A;\n" +
  "    part engine : A { attribute mass = 1; }\n" +
  "}\n";
writeFileSync(refactorModel, refactorSource);
r = run(["refactor", "extract", "/model/refactor.sysml", "Txn::engine"], ambient);
expect(
  r.code === 0 && readFileSync(refactorModel, "utf8").includes("part def Engine :> A"),
  "refactor extract persists through WASI",
  r
);
r = run(["refactor", "inline", "/model/refactor.sysml", "Txn::Engine"], ambient);
expect(
  r.code === 0 && readFileSync(refactorModel, "utf8") === refactorSource,
  "refactor inline restores bytes through WASI",
  r
);

rmSync(work, { recursive: true, force: true });
console.log("cli wasi smoke: all green");
