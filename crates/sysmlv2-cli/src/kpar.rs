//! KerML 10.3 project archives (`.kpar`): a ZIP holding textual model
//! units plus two manifests — `.project.json` (project name/version/
//! usage) and `.meta.json` (root-namespace index, metamodel URI, creation
//! time, SHA-256 checksums) — the exact shape of the normative archives
//! published with SysML-v2-Release (deflate entries, zeroed DOS dates).

use serde_json::{Map, Value, json};

/// One extracted model unit.
pub struct KparUnit {
    pub file_name: String,
    pub source: String,
}

/// A read archive: the two manifests (as parsed JSON, `Null` when absent)
/// and the textual units in archive order.
pub struct Kpar {
    // The manifests are parsed and kept for completeness (and the module
    // tests); the CLI itself only consumes the units and checksums.
    #[allow(dead_code)]
    pub project: Value,
    #[allow(dead_code)]
    pub meta: Value,
    pub units: Vec<KparUnit>,
    /// Units whose `.meta.json` SHA-256 does not match their bytes.
    pub checksum_mismatches: Vec<String>,
}

// ---- reading ---------------------------------------------------------------

/// Parse a `.kpar` archive. Only what the normative archives use is
/// supported: stored (0) and deflate (8) entries, sizes taken from the
/// central directory.
pub fn read(bytes: &[u8]) -> Result<Kpar, String> {
    let entries = zip_entries(bytes)?;
    let mut project = Value::Null;
    let mut meta = Value::Null;
    let mut units = Vec::new();
    for (name, data) in &entries {
        match name.as_str() {
            ".project.json" => {
                project = serde_json::from_slice(data)
                    .map_err(|e| format!(".project.json is not valid JSON: {e}"))?;
            }
            ".meta.json" => {
                meta = serde_json::from_slice(data)
                    .map_err(|e| format!(".meta.json is not valid JSON: {e}"))?;
            }
            n if crate::is_model_source(n) => {
                let source =
                    String::from_utf8(data.clone()).map_err(|_| format!("`{n}` is not UTF-8"))?;
                units.push(KparUnit {
                    file_name: n.to_string(),
                    source,
                });
            }
            _ => {}
        }
    }
    if units.is_empty() {
        return Err("archive holds no .sysml/.kerml units".into());
    }
    let mut checksum_mismatches = Vec::new();
    if let Some(checks) = meta.get("checksum").and_then(|v| v.as_object()) {
        for (name, data) in &entries {
            if let Some(expected) = checks
                .get(name)
                .and_then(|c| c.get("value"))
                .and_then(|v| v.as_str())
            {
                if !sha256_hex(data).eq_ignore_ascii_case(expected) {
                    checksum_mismatches.push(name.clone());
                }
            }
        }
    }
    Ok(Kpar {
        project,
        meta,
        units,
        checksum_mismatches,
    })
}

/// A little-endian field of `header`, which the caller has already
/// bounded: `at` is a fixed offset inside a fixed-size header, so the
/// slicing cannot fail.
fn u16_of(header: &[u8], at: usize) -> usize {
    u16::from_le_bytes([header[at], header[at + 1]]) as usize
}

fn u32_of(header: &[u8], at: usize) -> usize {
    u32::from_le_bytes([header[at], header[at + 1], header[at + 2], header[at + 3]]) as usize
}

/// Everything one archive may expand to.
///
/// A project archive holds model sources; the largest real ones are a few
/// megabytes. The archive's own headers say how far each entry expands,
/// so they cannot also be the budget — a crafted directory can declare an
/// entry that inflates to far more than the file's own size suggests, and
/// can name it as many times as it has records. One ceiling over
/// everything the archive expands to bounds both.
const MAX_INFLATED: usize = 512 * 1024 * 1024;

/// Every offset and length below comes from the archive itself, so none
/// of them is trusted: each header and each span is taken with a checked
/// addition and a bounds-checked slice, and an archive that points past
/// its own end is rejected with a message instead of an index panic.
/// The additions matter on a 32-bit target, where an offset near the top
/// of the `u32` field range would otherwise wrap and slip past a guard.
fn zip_entries(bytes: &[u8]) -> Result<Vec<(String, Vec<u8>)>, String> {
    let mut inflated_total = 0usize;
    // End-of-central-directory: scan backwards for PK\x05\x06.
    let eocd = bytes
        .windows(4)
        .rposition(|w| w == b"PK\x05\x06")
        .ok_or("not a ZIP archive (no end-of-central-directory)")?;
    let end = bytes
        .get(eocd..eocd + 22)
        .ok_or("truncated end-of-central-directory")?;
    let count = u16_of(end, 10);
    let mut off = u32_of(end, 16);
    let mut out = Vec::new();
    for _ in 0..count {
        let header = off
            .checked_add(46)
            .and_then(|to| bytes.get(off..to))
            .filter(|h| h.starts_with(b"PK\x01\x02"))
            .ok_or("malformed central directory")?;
        let method = u16_of(header, 10);
        let csize = u32_of(header, 20);
        let declared = u32_of(header, 24);
        let name_len = u16_of(header, 28);
        let extra_len = u16_of(header, 30);
        let comment_len = u16_of(header, 32);
        let local_off = u32_of(header, 42);
        let name_at = off + 46;
        let name = name_at
            .checked_add(name_len)
            .and_then(|to| bytes.get(name_at..to))
            .map(|n| String::from_utf8_lossy(n).into_owned())
            .ok_or("malformed central directory")?;
        // Local header: skip its (possibly different) name/extra lengths.
        let local = local_off
            .checked_add(30)
            .and_then(|to| bytes.get(local_off..to))
            .filter(|h| h.starts_with(b"PK\x03\x04"))
            .ok_or_else(|| format!("malformed local header for `{name}`"))?;
        let lname = u16_of(local, 26);
        let lextra = u16_of(local, 28);
        let data = local_off
            .checked_add(30)
            .and_then(|at| at.checked_add(lname))
            .and_then(|at| at.checked_add(lextra))
            .and_then(|at| Some((at, at.checked_add(csize)?)))
            .and_then(|(at, to)| bytes.get(at..to))
            .ok_or_else(|| format!("truncated data for `{name}`"))?;
        // What is left of the archive-wide ceiling also caps this entry,
        // so a declared size larger than the budget is refused before a
        // byte of it is decompressed.
        let budget = MAX_INFLATED - inflated_total;
        if declared > budget {
            return Err(format!("`{name}` expands past the archive size limit"));
        }
        let inflated = match method {
            0 => data.to_vec(),
            // The central directory declares the inflated size, so it
            // also caps it: an entry that expands past what it claims is
            // refused rather than allowed to exhaust memory.
            8 => miniz_oxide::inflate::decompress_to_vec_with_limit(data, declared)
                .map_err(|e| format!("cannot inflate `{name}`: {e}"))?,
            m => return Err(format!("`{name}` uses unsupported compression method {m}")),
        };
        if inflated.len() != declared {
            return Err(format!("size mismatch for `{name}`"));
        }
        inflated_total += inflated.len();
        out.push((name, inflated));
        off = off
            .checked_add(46 + name_len + extra_len + comment_len)
            .ok_or("malformed central directory")?;
    }
    Ok(out)
}

// ---- writing ---------------------------------------------------------------

/// Build a `.kpar` archive: `.project.json`, `.meta.json` (index of the
/// given root names, metamodel URI chosen by dialect, SHA-256 checksums,
/// `created` = now), then the units — deflate entries with the normative
/// zeroed date (1980-01-01), so archives are byte-deterministic apart
/// from the creation timestamp. Fails when a name, an entry or the whole
/// archive outgrows the 16/32-bit header fields.
pub fn write(
    project_name: &str,
    version: &str,
    units: &[(String, String, String)],
) -> Result<Vec<u8>, String> {
    let sysml = units
        .iter()
        .any(|(f, _, _)| crate::has_extension(f, "sysml"));
    let metamodel = if sysml {
        "https://www.omg.org/spec/SysML/20250201"
    } else {
        "https://www.omg.org/spec/KerML/20250201"
    };
    let project = json!({
        "name": project_name,
        "version": version,
        "usage": [],
    });
    let mut index = Map::new();
    let mut checksum = Map::new();
    for (file, source, root) in units {
        index.insert(root.clone(), json!(file));
        checksum.insert(
            file.clone(),
            json!({ "value": sha256_hex(source.as_bytes()), "algorithm": "SHA256" }),
        );
    }
    let meta = json!({
        "index": index,
        "created": now_utc_iso(),
        "metamodel": metamodel,
        "checksum": checksum,
    });
    let mut entries: Vec<(String, Vec<u8>)> = vec![
        (
            ".project.json".into(),
            serde_json::to_vec(&project).unwrap(),
        ),
        (".meta.json".into(), serde_json::to_vec(&meta).unwrap()),
    ];
    for (file, source, _) in units {
        entries.push((file.clone(), source.as_bytes().to_vec()));
    }
    zip_write(&entries)
}

/// The ZIP headers this writer emits hold offsets and sizes in 32 bits
/// and counts and name lengths in 16, and there is no ZIP64 record to
/// escape into; anything that does not fit is refused rather than
/// silently truncated into a header that describes a different archive.
fn too_large(what: impl std::fmt::Display) -> String {
    format!("archive too large (no ZIP64 support): {what}")
}

fn zip_write(entries: &[(String, Vec<u8>)]) -> Result<Vec<u8>, String> {
    let mut out = Vec::new();
    let mut central = Vec::new();
    // The normative archives' zeroed timestamp: 1980-01-01 00:00.
    let (dos_time, dos_date) = (0u16, 0x0021u16);
    for (name, data) in entries {
        let crc = crc32(data);
        let deflated = miniz_oxide::deflate::compress_to_vec(
            data,
            miniz_oxide::deflate::CompressionLevel::DefaultLevel as u8,
        );
        let (method, payload): (u16, &[u8]) = if deflated.len() < data.len() {
            (8, &deflated)
        } else {
            (0, data)
        };
        let local_off =
            u32::try_from(out.len()).map_err(|_| too_large(format_args!("entry offset")))?;
        let csize = u32::try_from(payload.len())
            .map_err(|_| too_large(format_args!("compressed `{name}`")))?;
        let usize_ = u32::try_from(data.len()).map_err(|_| too_large(format_args!("`{name}`")))?;
        let name_len =
            u16::try_from(name.len()).map_err(|_| too_large(format_args!("the name `{name}`")))?;
        out.extend_from_slice(b"PK\x03\x04");
        out.extend_from_slice(&20u16.to_le_bytes()); // version needed
        out.extend_from_slice(&0u16.to_le_bytes()); // flags
        out.extend_from_slice(&method.to_le_bytes());
        out.extend_from_slice(&dos_time.to_le_bytes());
        out.extend_from_slice(&dos_date.to_le_bytes());
        out.extend_from_slice(&crc.to_le_bytes());
        out.extend_from_slice(&csize.to_le_bytes());
        out.extend_from_slice(&usize_.to_le_bytes());
        out.extend_from_slice(&name_len.to_le_bytes());
        out.extend_from_slice(&0u16.to_le_bytes()); // extra
        out.extend_from_slice(name.as_bytes());
        out.extend_from_slice(payload);

        central.extend_from_slice(b"PK\x01\x02");
        central.extend_from_slice(&20u16.to_le_bytes()); // version made by
        central.extend_from_slice(&20u16.to_le_bytes()); // version needed
        central.extend_from_slice(&0u16.to_le_bytes());
        central.extend_from_slice(&method.to_le_bytes());
        central.extend_from_slice(&dos_time.to_le_bytes());
        central.extend_from_slice(&dos_date.to_le_bytes());
        central.extend_from_slice(&crc.to_le_bytes());
        central.extend_from_slice(&csize.to_le_bytes());
        central.extend_from_slice(&usize_.to_le_bytes());
        central.extend_from_slice(&name_len.to_le_bytes());
        central.extend_from_slice(&[0u8; 8]); // extra/comment/disk/internal
        central.extend_from_slice(&0u32.to_le_bytes()); // external attrs
        central.extend_from_slice(&local_off.to_le_bytes());
        central.extend_from_slice(name.as_bytes());
    }
    let cd_off = u32::try_from(out.len())
        .map_err(|_| too_large(format_args!("central-directory offset")))?;
    let cd_len =
        u32::try_from(central.len()).map_err(|_| too_large(format_args!("central directory")))?;
    let count = u16::try_from(entries.len()).map_err(|_| too_large(format_args!("entry count")))?;
    out.extend_from_slice(&central);
    out.extend_from_slice(b"PK\x05\x06");
    out.extend_from_slice(&[0u8; 4]); // disk numbers
    out.extend_from_slice(&count.to_le_bytes());
    out.extend_from_slice(&count.to_le_bytes());
    out.extend_from_slice(&cd_len.to_le_bytes());
    out.extend_from_slice(&cd_off.to_le_bytes());
    out.extend_from_slice(&0u16.to_le_bytes()); // comment
    Ok(out)
}

// ---- hashing ---------------------------------------------------------------

fn crc32(data: &[u8]) -> u32 {
    let mut crc = !0u32;
    for &b in data {
        crc ^= b as u32;
        for _ in 0..8 {
            let mask = (crc & 1).wrapping_neg();
            crc = (crc >> 1) ^ (0xEDB8_8320 & mask);
        }
    }
    !crc
}

/// SHA-256 (FIPS 180-4) — small and dependency-free; the `.meta.json`
/// checksums of the normative archives are the conformance gate.
fn sha256_hex(data: &[u8]) -> String {
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let mut h: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    let mut msg = data.to_vec();
    let bit_len = (data.len() as u64) * 8;
    msg.push(0x80);
    while msg.len() % 64 != 56 {
        msg.push(0);
    }
    msg.extend_from_slice(&bit_len.to_be_bytes());
    for chunk in msg.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (i, word) in chunk.chunks_exact(4).enumerate() {
            w[i] = u32::from_be_bytes([word[0], word[1], word[2], word[3]]);
        }
        for i in 16..64 {
            let s0 = w[i - 15].rotate_right(7) ^ w[i - 15].rotate_right(18) ^ (w[i - 15] >> 3);
            let s1 = w[i - 2].rotate_right(17) ^ w[i - 2].rotate_right(19) ^ (w[i - 2] >> 10);
            w[i] = w[i - 16]
                .wrapping_add(s0)
                .wrapping_add(w[i - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut hh] = h;
        for i in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let ch = (e & f) ^ (!e & g);
            let t1 = hh
                .wrapping_add(s1)
                .wrapping_add(ch)
                .wrapping_add(K[i])
                .wrapping_add(w[i]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let maj = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(maj);
            hh = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        for (i, v) in [a, b, c, d, e, f, g, hh].into_iter().enumerate() {
            h[i] = h[i].wrapping_add(v);
        }
    }
    h.iter().map(|v| format!("{v:08x}")).collect()
}

fn now_utc_iso() -> String {
    let secs = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or(0);
    let days = (secs / 86_400) as i64;
    let rem = secs % 86_400;
    // Civil-from-days (Howard Hinnant's algorithm).
    let z = days + 719_468;
    let era = z.div_euclid(146_097);
    let doe = z.rem_euclid(146_097);
    let yoe = (doe - doe / 1460 + doe / 36_524 - doe / 146_096) / 365;
    let y = yoe + era * 400;
    let doy = doe - (365 * yoe + yoe / 4 - yoe / 100);
    let mp = (5 * doy + 2) / 153;
    let d = doy - (153 * mp + 2) / 5 + 1;
    let m = if mp < 10 { mp + 3 } else { mp - 9 };
    let y = if m <= 2 { y + 1 } else { y };
    format!(
        "{y:04}-{m:02}-{d:02}T{:02}:{:02}:{:02}Z",
        rem / 3600,
        (rem % 3600) / 60,
        rem % 60
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sha256_test_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn zip_round_trips() {
        let units = vec![(
            "M.sysml".to_string(),
            "package M;\n".to_string(),
            "M".to_string(),
        )];
        let bytes = write("Test", "1.0.0", &units).expect("writable");
        let kpar = read(&bytes).expect("readable");
        assert_eq!(kpar.units.len(), 1);
        assert_eq!(kpar.units[0].source, "package M;\n");
        assert!(kpar.checksum_mismatches.is_empty());
        assert_eq!(kpar.project["name"], "Test");
        assert_eq!(kpar.meta["index"]["M"], "M.sysml");
    }

    /// An archive whose one unit is repetitive enough to be stored
    /// deflated, so the inflation path is exercised.
    fn sample() -> Vec<u8> {
        let units = vec![(
            "M.sysml".to_string(),
            format!("package M {{\n{}}}\n", "    part def P;\n".repeat(200)),
            "M".to_string(),
        )];
        write("Test", "1.0.0", &units).expect("writable")
    }

    fn u16_at(bytes: &[u8], at: usize) -> usize {
        u16::from_le_bytes(bytes[at..at + 2].try_into().unwrap()) as usize
    }

    fn put_u16(bytes: &mut [u8], at: usize, v: u16) {
        bytes[at..at + 2].copy_from_slice(&v.to_le_bytes());
    }

    fn put_u32(bytes: &mut [u8], at: usize, v: u32) {
        bytes[at..at + 4].copy_from_slice(&v.to_le_bytes());
    }

    /// Offsets of the central-directory headers, in archive order. The
    /// archive carries no trailing comment, so its end record is the
    /// last 22 bytes.
    fn headers(bytes: &[u8]) -> Vec<usize> {
        let end = bytes.len() - 22;
        let count = u16_at(bytes, end + 10);
        let mut off = u32::from_le_bytes(bytes[end + 16..end + 20].try_into().unwrap()) as usize;
        let mut out = Vec::new();
        for _ in 0..count {
            out.push(off);
            off += 46 + u16_at(bytes, off + 28) + u16_at(bytes, off + 30) + u16_at(bytes, off + 32);
        }
        out
    }

    /// The message from an archive the reader must refuse.
    fn refusal(bytes: &[u8]) -> String {
        match read(bytes) {
            Ok(_) => panic!("the archive was accepted"),
            Err(e) => e,
        }
    }

    fn deflated_header(bytes: &[u8]) -> usize {
        headers(bytes)
            .into_iter()
            .find(|&h| u16_at(bytes, h + 10) == 8)
            .expect("one entry is stored deflated")
    }

    #[test]
    fn a_name_running_past_the_end_is_refused() {
        let mut bytes = sample();
        let header = headers(&bytes)[0];
        put_u16(&mut bytes, header + 28, u16::MAX);
        let err = refusal(&bytes);
        assert!(err.contains("malformed central directory"), "{err}");
    }

    #[test]
    fn a_central_directory_running_past_the_end_is_refused() {
        // Both a directory that starts just short of the end and one
        // whose offset is near the top of the 32-bit field — the latter
        // is what wraps where a pointer is 32 bits wide.
        for start in [u32::MAX - 10, u32::try_from(sample().len() - 2).unwrap()] {
            let mut bytes = sample();
            let end = bytes.len() - 22;
            put_u32(&mut bytes, end + 16, start);
            let err = refusal(&bytes);
            assert!(err.contains("malformed central directory"), "{err}");
        }
    }

    #[test]
    fn a_local_offset_running_past_the_end_is_refused() {
        for local in [u32::MAX - 10, 1] {
            let mut bytes = sample();
            let header = headers(&bytes)[0];
            put_u32(&mut bytes, header + 42, local);
            let err = refusal(&bytes);
            assert!(err.contains("malformed local header"), "{err}");
        }
    }

    #[test]
    fn entry_data_running_past_the_end_is_refused() {
        let mut bytes = sample();
        let header = headers(&bytes)[0];
        put_u32(&mut bytes, header + 20, u32::MAX);
        let err = refusal(&bytes);
        assert!(err.contains("truncated data"), "{err}");
    }

    #[test]
    fn a_declared_size_that_understates_the_entry_caps_inflation() {
        let mut bytes = sample();
        let header = deflated_header(&bytes);
        put_u32(&mut bytes, header + 24, 4);
        let err = refusal(&bytes);
        assert!(err.contains("cannot inflate"), "{err}");
    }

    #[test]
    fn a_declared_size_that_overstates_the_entry_is_refused() {
        let mut bytes = sample();
        let header = deflated_header(&bytes);
        put_u32(&mut bytes, header + 24, 10_000_000);
        let err = refusal(&bytes);
        assert!(err.contains("size mismatch"), "{err}");
    }

    /// The ceiling is over everything the archive expands to, not over
    /// one entry: a declared size past it is refused before a byte is
    /// decompressed, and a size that would fit on its own is refused once
    /// the entries before it have spent part of the budget.
    #[test]
    fn a_declared_size_past_the_archive_ceiling_is_refused() {
        let mut bytes = sample();
        let header = deflated_header(&bytes);
        put_u32(&mut bytes, header + 24, MAX_INFLATED as u32 + 1);
        let err = refusal(&bytes);
        assert!(err.contains("expands past the archive size limit"), "{err}");

        // Exactly the ceiling, on an entry that is not the first: what
        // the entries before it expanded to is already spent.
        let mut bytes = sample();
        let header = headers(&bytes)[1];
        put_u32(&mut bytes, header + 24, MAX_INFLATED as u32);
        let err = refusal(&bytes);
        assert!(err.contains("expands past the archive size limit"), "{err}");
    }

    #[test]
    fn a_truncated_archive_is_refused() {
        let bytes = sample();
        let err = refusal(&bytes[..bytes.len() / 2]);
        assert!(err.contains("not a ZIP archive"), "{err}");
    }
}
