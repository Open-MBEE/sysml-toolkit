// Assemble the npm package: wasm-pack web-target build + the
// stdlib bundle/snapshot, packed into a tarball. This script never
// publishes — CI publishes the tarball to the org's GitHub Packages npm
// registry on release tags / manual runs (see .github/workflows/ci.yml,
// wasm job), and it doubles as a release artifact (`npm install
// <tarball>` / `file:` works for local consumers meanwhile).
//
//   node crates/sysmlv2-wasm/npm/build.mjs
//
// Env:
//   WASM_PACK        wasm-pack executable (default: wasm-pack on PATH)
//   SYSMLV2_LIBRARY  standard-library dir (default: the spec-refs
//                    submodule's sysml.library)
//
// Outputs (all under crates/sysmlv2-wasm/npm/, gitignored):
//   pkg/       the package: web-target module + stdlib/ artifacts
//   pkg-node/  nodejs-target build, for smoke.mjs only (not packaged)
//   dist/      sysml-wasm-<version>.tgz

import { execFileSync } from "node:child_process";
import { copyFileSync, readFileSync, writeFileSync, mkdirSync, readdirSync, existsSync } from "node:fs";
import { dirname, join, resolve, delimiter } from "node:path";
import { homedir } from "node:os";
import { fileURLToPath } from "node:url";

const crateDir = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const repoRoot = resolve(crateDir, "..", "..");
const npmDir = join(crateDir, "npm");

// Toolchain resolution — the script must work when invoked from any
// cwd (e.g. a consumer's `npm run kernel`) on machines where another
// rust distribution shadows rustup on PATH (rustup's is the one with
// wasm targets). Explicit env always wins.
const localWasmPack = join(npmDir, "node_modules", ".bin", "wasm-pack");
const wasmPack = process.env.WASM_PACK ?? (existsSync(localWasmPack) ? localWasmPack : "wasm-pack");
const rustupToolchains = join(homedir(), ".rustup", "toolchains");
const pinnedChannel = readFileSync(join(repoRoot, "rust-toolchain.toml"), "utf8")
  .match(/^channel\s*=\s*"([^"]+)"/m)?.[1];
if (!pinnedChannel) throw new Error("rust-toolchain.toml does not declare a channel");
const channel = process.env.RUSTUP_TOOLCHAIN ?? pinnedChannel;
const toolchainBin = existsSync(rustupToolchains)
  ? readdirSync(rustupToolchains)
      .filter((d) => d === channel || d.startsWith(`${channel}-`))
      .map((d) => join(rustupToolchains, d, "bin"))
      .find((b) => existsSync(join(b, "cargo")))
  : undefined;
const env = toolchainBin ? { ...process.env, PATH: `${toolchainBin}${delimiter}${process.env.PATH}` } : process.env;
const libraryDir =
  process.env.SYSMLV2_LIBRARY ??
  join(repoRoot, "spec-refs", "SysML-v2-Release", "sysml.library");

const run = (cmd, args, opts = {}) => {
  console.log(`> ${cmd} ${args.join(" ")}`);
  execFileSync(cmd, args, { stdio: "inherit", env, ...opts });
};

// 1. The package module (web target: explicit init(url) — works in
// browsers, workers, and bundlers without wasm-aware config) and the
// smoke-test module (nodejs target). The linear memory is capped below
// the wasm32 maximum: a runaway allocation then fails inside the module
// (an error the host reports and a worker restart clears) instead of
// growing until the browser kills the whole tab. The cap leaves ample
// room above what the largest models and library snapshots use.
const MAX_MEMORY_BYTES = 2 * 1024 * 1024 * 1024;
// The module's stack is reserved explicitly rather than left at the
// linker's default megabyte, which is below the depths the toolkit's
// recursive passes bound themselves to — on this target running out of
// stack traps instead of unwinding, so a bound the stack cannot hold is
// a crash where the host expects a finding. The size is declared in the
// crate, next to the reasoning, and read from there so the two cannot
// drift; tests/stack.rs holds them together.
const stackSizeBytes = (() => {
  const src = readFileSync(join(crateDir, "src", "lib.rs"), "utf8");
  const found = src.match(/pub const WASM_STACK_BYTES: usize = (\d+);/);
  if (!found) throw new Error("WASM_STACK_BYTES not found in crates/sysmlv2-wasm/src/lib.rs");
  return Number(found[1]);
})();
// The link flag goes in the wasm32-only rustflags variable, never the
// global RUSTFLAGS: the packager inherits this environment when it installs
// its helper binary for the host (a plain `cargo install`, no --target),
// and the host linker rejects a wasm-only argument. Cargo reads exactly
// one rustflags source, and a set (encoded) RUSTFLAGS wins over the
// target variable, so any flags the caller exported are folded into the
// target variable and removed from the environment wasm-pack sees.
const encodedRustflags = process.env.CARGO_ENCODED_RUSTFLAGS?.split("\x1f") ?? [];
const targetRustflags = [
  ...encodedRustflags,
  process.env.RUSTFLAGS,
  process.env.CARGO_TARGET_WASM32_UNKNOWN_UNKNOWN_RUSTFLAGS,
  `-C link-arg=--max-memory=${MAX_MEMORY_BYTES}`,
  `-C link-arg=-zstack-size=${stackSizeBytes}`,
].filter(Boolean).join(" ");
const { RUSTFLAGS: _rustflags, CARGO_ENCODED_RUSTFLAGS: _encoded, ...hostEnv } = env;
const wasmEnv = { ...hostEnv, CARGO_TARGET_WASM32_UNKNOWN_UNKNOWN_RUSTFLAGS: targetRustflags };
run(wasmPack, ["build", crateDir, "--release", "--target", "web", "--out-dir", "npm/pkg", "--out-name", "sysmlv2"], { env: wasmEnv });
run(wasmPack, ["build", crateDir, "--release", "--target", "nodejs", "--out-dir", "npm/pkg-node", "--out-name", "sysmlv2"], { env: wasmEnv });

// 2. Standard-library artifacts into the package. The shipped bundle
// carries the ambient libraries (Web, Template, engine overlays,
// TransformMeta) after the standard library; a second, core-only bundle
// (SYSMLV2_AMBIENT=off) serves the library generator's own validation,
// where a candidate library must not collide with the committed copy.
run("cargo", ["run", "--release", "-p", "sysmlv2-wasm", "--bin", "gen_stdlib_bundle", "--", libraryDir, join(crateDir, "npm", "pkg", "stdlib")], { cwd: repoRoot });
run("cargo", ["run", "--release", "-p", "sysmlv2-wasm", "--bin", "gen_stdlib_bundle", "--", libraryDir, join(crateDir, "npm", "pkg-node", "stdlib-core")], { cwd: repoRoot, env: { ...env, SYSMLV2_AMBIENT: "off" } });

// 2.5. The wasi CLI artifact: the real `sysmlv2`
// binary for wasm32-wasip1, shipped inside the package (cli/) so hosts
// always hold a binary version-locked to the kernel module. Slim
// profile — no lsp verb; z3 stays a runtime-absent subprocess.
// Local note: needs the wasm32-wasip1 rustup target, and the same
// toolchain-path care as any wasm build on machines where another
// cargo shadows rustup (CARGO / CARGO_TARGET_DIR are honored).
const cargo = process.env.CARGO ?? "cargo";
// The same stack reservation as the module above: the recursion bounds
// and the trap-on-overflow behaviour are the target's, not the binding's.
const wasiEnv = {
  ...hostEnv,
  CARGO_TARGET_WASM32_WASIP1_RUSTFLAGS: [
    ...encodedRustflags,
    process.env.RUSTFLAGS,
    process.env.CARGO_TARGET_WASM32_WASIP1_RUSTFLAGS,
    `-C link-arg=-zstack-size=${stackSizeBytes}`,
  ].filter(Boolean).join(" "),
};
run(
  cargo,
  ["build", "-p", "sysmlv2-cli", "--no-default-features", "--features", "solve,viz", "--target", "wasm32-wasip1", "--profile", "wasi-release"],
  { cwd: repoRoot, env: wasiEnv }
);
const targetDir = process.env.CARGO_TARGET_DIR
  ? resolve(repoRoot, process.env.CARGO_TARGET_DIR)
  : join(repoRoot, "target");
mkdirSync(join(crateDir, "npm", "pkg", "cli"), { recursive: true });
copyFileSync(
  join(targetDir, "wasm32-wasip1", "wasi-release", "sysmlv2.wasm"),
  join(crateDir, "npm", "pkg", "cli", "sysmlv2-cli.wasm")
);

// 3. Package identity: scope the wasm-pack-generated manifest and ship
// the stdlib alongside the module.
const pkgJsonPath = join(crateDir, "npm", "pkg", "package.json");
const pkg = JSON.parse(readFileSync(pkgJsonPath, "utf8"));
pkg.name = "@sysml/wasm";
pkg.description =
  "SysML v2 / KerML toolkit for the browser: parsing, checking, interchange JSON, PlantUML emission (wasm)";
pkg.files = [...new Set([...(pkg.files ?? []), "stdlib", "cli", "buildinfo.json"])];

// 3.5. Build provenance, for hosts that surface kernel identity (a
// status-bar tooltip, say). Best-effort fields — a missing git or
// toolchain probe never fails the build.
const probe = (cmd, args) => {
  try {
    return execFileSync(cmd, args, { cwd: repoRoot, env, encoding: "utf8" }).trim();
  } catch {
    return undefined;
  }
};
const buildinfo = {
  name: pkg.name,
  version: pkg.version,
  commit: probe("git", ["rev-parse", "--short", "HEAD"]),
  dirty: probe("git", ["status", "--porcelain"]) ? true : false,
  builtAt: new Date().toISOString(),
  toolchain: probe("rustc", ["--version"]),
};
writeFileSync(join(crateDir, "npm", "pkg", "buildinfo.json"), JSON.stringify(buildinfo, null, 2) + "\n");
// Publishes go to the package registry CI is configured for (release
// tags / manual runs).
pkg.publishConfig = { registry: "https://npm.pkg.github.com" };
writeFileSync(pkgJsonPath, JSON.stringify(pkg, null, 2) + "\n");

// 4. Tarball.
const distDir = join(crateDir, "npm", "dist");
mkdirSync(distDir, { recursive: true });
run("npm", ["pack", "--pack-destination", distDir], { cwd: join(crateDir, "npm", "pkg") });
// npm derives this filename from the scoped package identity. Never pick a
// tarball by directory order: dist may also contain older package versions.
const final = `sysml-wasm-${pkg.version}.tgz`;
if (!existsSync(join(distDir, final))) throw new Error(`npm pack did not produce ${final}`);
console.log(`packaged: npm/dist/${final}`);
