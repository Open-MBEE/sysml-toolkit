//! Generate the browser standard-library artifacts: a gzipped
//! source bundle plus a sealed resolution snapshot, consumed by the
//! wasm binding's `loadLibrarySources(bundle, snapshot)`.
//!
//!     gen-stdlib-bundle <library-dir> <out-dir>
//!
//! Writes to `<out-dir>`:
//! - `sysml-library.json.gz` — `[{name, text}]`, gzip. The **array order
//!   is load order**: the snapshot's fingerprint was recorded against
//!   exactly this sequence, so consumers must add units in array order
//!   (the binding's `parse_sources` does).
//! - `sysml-library.libcache.gz` — `LibraryCache::to_bytes`, gzip.
//! - `manifest.json` — toolkit version, unit count, raw/compressed sizes.
//!
//! Browsers decompress with `DecompressionStream("gzip")`, node with
//! `zlib.gunzipSync`.

use std::io::Write;
use std::path::{Path, PathBuf};

use sysmlv2_model::json::ResolvedModel;
use sysmlv2_model::model::Model;

fn collect(dir: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in std::fs::read_dir(dir)? {
        let path = entry?.path();
        if path.is_dir() {
            collect(&path, files)?;
        } else if matches!(
            path.extension().and_then(|e| e.to_str()),
            Some("sysml") | Some("kerml")
        ) {
            files.push(path);
        }
    }
    Ok(())
}

/// A minimal gzip container around miniz_oxide's raw deflate: 10-byte
/// header, deflate body, CRC-32 + input length trailer (RFC 1952).
fn gzip(data: &[u8]) -> Vec<u8> {
    let mut out = vec![0x1f, 0x8b, 0x08, 0, 0, 0, 0, 0, 0, 0xff];
    out.extend_from_slice(&miniz_oxide::deflate::compress_to_vec(data, 9));
    out.extend_from_slice(&crc32(data).to_le_bytes());
    // The trailer's size field is the input length modulo 2^32, which
    // is what the low 32 bits of the length are.
    #[allow(clippy::cast_possible_truncation)]
    let isize_field = data.len() as u32;
    out.extend_from_slice(&isize_field.to_le_bytes());
    out
}

fn crc32(data: &[u8]) -> u32 {
    let mut table = [0u32; 256];
    for (n, slot) in (0u32..).zip(table.iter_mut()) {
        let mut c = n;
        for _ in 0..8 {
            c = if c & 1 != 0 {
                0xedb88320 ^ (c >> 1)
            } else {
                c >> 1
            };
        }
        *slot = c;
    }
    let mut c = !0u32;
    for &b in data {
        c = table[((c ^ b as u32) & 0xff) as usize] ^ (c >> 8);
    }
    !c
}

fn main() {
    let mut args = std::env::args().skip(1);
    let (Some(lib_dir), Some(out_dir)) = (args.next(), args.next()) else {
        eprintln!("usage: gen-stdlib-bundle <library-dir> <out-dir>");
        std::process::exit(2);
    };
    let lib_dir = PathBuf::from(lib_dir);
    let out_dir = PathBuf::from(out_dir);

    let mut files = Vec::new();
    collect(&lib_dir, &mut files).expect("readable library dir");
    files.sort();
    assert!(
        !files.is_empty(),
        "no .sysml/.kerml files under {}",
        lib_dir.display()
    );

    // Unit name = relative path (forward slashes) so names stay unique
    // and deterministic across platforms; `.kerml` suffixes survive, so
    // dialect selection is unchanged.
    let mut units: Vec<(String, String)> = files
        .iter()
        .map(|p| {
            let name = p
                .strip_prefix(&lib_dir)
                .unwrap_or(p)
                .components()
                .map(|c| c.as_os_str().to_string_lossy())
                .collect::<Vec<_>>()
                .join("/");
            (
                name,
                std::fs::read_to_string(p).expect("readable library file"),
            )
        })
        .collect();
    // The ambient libraries follow the standard library, in their
    // declared load order, exactly as a directory library loads them
    // (`SYSMLV2_AMBIENT=off` yields a core-only bundle).
    units.extend(sysmlv2_model::ambient::units());

    // Record the sealed snapshot against the bundle's exact unit order.
    let mut model = Model::new();
    for (name, src) in &units {
        model.add_library_source(name.clone(), src);
    }
    model.record_library_cache();
    let resolved = ResolvedModel::build(&model);
    let unresolved = resolved.unresolved_count();
    let snapshot = model
        .take_recorded_library_cache()
        .expect("recording armed before the build")
        .to_bytes();

    let bundle = serde_json::to_string(
        &units
            .iter()
            .map(|(name, text)| serde_json::json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
    )
    .expect("serializable");

    std::fs::create_dir_all(&out_dir).expect("writable out dir");
    let write = |file: &str, bytes: &[u8]| {
        let path = out_dir.join(file);
        std::fs::File::create(&path)
            .and_then(|mut f| f.write_all(bytes))
            .expect("writable output file");
        bytes.len()
    };
    let bundle_gz = write("sysml-library.json.gz", &gzip(bundle.as_bytes()));
    let snapshot_gz = write("sysml-library.libcache.gz", &gzip(&snapshot));
    let manifest = serde_json::json!({
        "toolkitVersion": env!("CARGO_PKG_VERSION"),
        "units": units.len(),
        "libraryUnresolvedReferences": unresolved,
        "bundle": {
            "file": "sysml-library.json.gz",
            "rawBytes": bundle.len(),
            "gzipBytes": bundle_gz,
        },
        "snapshot": {
            "file": "sysml-library.libcache.gz",
            "rawBytes": snapshot.len(),
            "gzipBytes": snapshot_gz,
        },
    });
    write(
        "manifest.json",
        serde_json::to_string_pretty(&manifest).unwrap().as_bytes(),
    );
    println!(
        "{} units; bundle {} -> {} gz; snapshot {} -> {} gz; {} library-internal unresolved",
        units.len(),
        bundle.len(),
        bundle_gz,
        snapshot.len(),
        snapshot_gz,
        unresolved,
    );
}
