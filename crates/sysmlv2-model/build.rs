//! Stamps the crate with `SYSMLV2_SEMANTICS_FINGERPRINT`: an FNV-1a 64
//! hash over the sources that determine model-build semantics — this
//! crate's `src/` plus the syntax crate's `src/` it lowers from (when the
//! sibling is present; a packaged crate falls back to its own sources,
//! where the pinned dependency version covers the rest).
//!
//! The library resolution cache folds it into the header it stamps on
//! every serialized cache (`libcache::TOOLKIT_BUILD`), so caches recorded
//! by any other toolkit build self-invalidate. The crate version alone
//! cannot tell two working-tree states apart, and a resolution or
//! evaluation change that leaves the pending-reference queue unchanged
//! slips past the sequence fingerprint — observed as a cached library
//! export silently serving pre-change evaluated values.

use std::path::{Path, PathBuf};

fn main() {
    let root = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap());
    let mut hash = Fnv::new();
    for dir in [root.join("src"), root.join("../sysmlv2-syntax/src")] {
        if !dir.is_dir() {
            continue;
        }
        println!("cargo:rerun-if-changed={}", dir.display());
        let mut files = Vec::new();
        collect(&dir, &mut files);
        files.sort();
        for file in &files {
            // (a file gone or unreadable since the walk — a dangling link —
            // is left out)
            let Ok(bytes) = std::fs::read(file) else {
                continue;
            };
            let rel = file.strip_prefix(&dir).unwrap();
            hash.update(rel.to_string_lossy().as_bytes());
            hash.update(&bytes);
        }
    }
    println!(
        "cargo:rustc-env=SYSMLV2_SEMANTICS_FINGERPRINT={:016x}",
        hash.finish()
    );
}

/// Every file under `dir`, but for what an editor keeps beside a source
/// while it is open — a `.#name` lock, a `.swp` swap file, a `name~`
/// backup — and an entry that cannot be read.
fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let name = entry.file_name();
        let name = name.to_string_lossy();
        if name.starts_with(".#") || name.ends_with(".swp") || name.ends_with('~') {
            continue;
        }
        let path = entry.path();
        if path.is_dir() {
            collect(&path, out);
        } else {
            out.push(path);
        }
    }
}

/// FNV-1a, 64-bit, byte by byte — the form `libcache::Fnv` folds eight
/// bytes at a time; the two are never compared (a build script cannot use
/// the crate it builds).
struct Fnv(u64);

impl Fnv {
    fn new() -> Fnv {
        Fnv(0xcbf29ce484222325)
    }
    fn update(&mut self, bytes: &[u8]) {
        for &b in bytes {
            self.0 ^= b as u64;
            self.0 = self.0.wrapping_mul(0x100000001b3);
        }
    }
    fn finish(&self) -> u64 {
        self.0
    }
}
