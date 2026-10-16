//! Stamps the crate with `SYSMLV2_LSP_FINGERPRINT`: an FNV-1a 64 hash over
//! this crate's `src/`, which decides what the server derives from a
//! library's texts.
//!
//! The standard library's symbol table ships in a prepared snapshot
//! stamped with it, and a server reads the table back only under the
//! same stamp: the snapshot's own build identity covers the model and
//! syntax crates, not this one, so a change to the outline or the
//! table's walk would otherwise serve a table the server no longer
//! makes.

use std::path::{Path, PathBuf};

fn main() {
    let dir = PathBuf::from(std::env::var_os("CARGO_MANIFEST_DIR").unwrap()).join("src");
    println!("cargo:rerun-if-changed={}", dir.display());
    let mut files = Vec::new();
    collect(&dir, &mut files);
    files.sort();
    let mut hash = Fnv::new();
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
    println!(
        "cargo:rustc-env=SYSMLV2_LSP_FINGERPRINT={:016x}",
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

/// FNV-1a, 64-bit, byte by byte.
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
