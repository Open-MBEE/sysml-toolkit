//! Full-form corpus baseline: every derived (and owned) property of every
//! element the standard corpus emits, digested per (metaclass, property)
//! and pinned in `tests/fixtures/full-form-baseline.tsv`.
//!
//! The gate that the derived-property port (plan §33) runs under: a
//! change to the emitter must leave every (metaclass, property) digest
//! identical except for the names the change deliberately promotes. A
//! difference prints the changed pairs, so a promotion is adjudicated
//! name by name rather than discovered as a byte diff of a 50k-element
//! payload. Refresh the baseline deliberately with
//! `SYSMLV2_UPDATE_BASELINE=1 cargo test --test full_baseline`; the
//! resulting fixture diff is the change's allowlist and belongs in the
//! same commit.
//!
//! Per pair the fixture carries an order-independent digest of
//! `(element id, canonical JSON value)`, the element count, and how many
//! values are *non-empty* — not `null`, `[]`, `false`, or a self-reference
//! (the catalog's required-reference placeholder; `featureTarget` is the
//! one name whose normative value is legitimately `self` for every
//! unchained feature, so its non-empty count under-reports). The counts
//! feed the derived-property census (`tools/derived_census.py`).

#![cfg(feature = "json")]

use serde_json::Value;
use std::collections::BTreeMap;
use std::fs;
use std::path::PathBuf;
use sysmlv2_parser::full::model_to_full_json;
use sysmlv2_parser::model::Model;

/// Order-independent, version-stable digest of one property across a
/// metaclass: the wrapping sum of per-element FNV-1a hashes, so element
/// order cannot move it and no hashing crate is needed.
#[derive(Default, Clone, Copy, PartialEq, Eq)]
struct Digest {
    sum: u64,
    elements: u64,
    nonempty: u64,
}

fn fnv1a(bytes: &[u8]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &b in bytes {
        h ^= b as u64;
        h = h.wrapping_mul(0x0000_0100_0000_01b3);
    }
    h
}

fn is_empty_value(v: &Value, self_id: &str) -> bool {
    match v {
        Value::Null => true,
        Value::Bool(b) => !b,
        Value::Array(a) => a.is_empty(),
        Value::Object(o) => o.get("@id").and_then(Value::as_str) == Some(self_id),
        _ => false,
    }
}

type Table = BTreeMap<(String, String), Digest>;

fn digest_corpus() -> Option<Table> {
    let root = sysmlv2_testkit::workspace_root().join("spec-refs/SysML-v2-Release");
    if !root.join("sysml.library").exists() {
        eprintln!("skipping: corpus not present");
        return None;
    }
    let files = sysmlv2_testkit::user_files();
    if files.is_empty() {
        eprintln!("skipping: corpus model files not present (sparse checkout without sysml/src)");
        return None;
    }
    let mut model = Model::new();
    model
        .load_library_dir(&root.join("sysml.library"))
        .expect("library loads");
    for path in files {
        let src = fs::read_to_string(&path).unwrap();
        // Unit names salt the root ids; two corpus files share a basename,
        // so name units by corpus-relative path to keep every id unique
        // (as the parity and loader gates do).
        let name = path
            .strip_prefix(&root)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        model.add_source(name, &src);
    }
    let full = model_to_full_json(&model);
    let elements = full.as_array().expect("full form is an element array");
    let mut table: Table = BTreeMap::new();
    for el in elements {
        let obj = el.as_object().expect("element object");
        let ty = obj["@type"].as_str().expect("@type").to_string();
        let id = obj["@id"].as_str().expect("@id");
        for (k, v) in obj {
            if k == "@type" || k == "@id" {
                continue;
            }
            // Canonical: serde_json's map is key-sorted, so nested objects
            // serialize deterministically.
            let canon = serde_json::to_string(v).unwrap();
            let entry = table.entry((ty.clone(), k.clone())).or_default();
            entry.sum = entry
                .sum
                .wrapping_add(fnv1a(format!("{id}\t{canon}").as_bytes()));
            entry.elements += 1;
            if !is_empty_value(v, id) {
                entry.nonempty += 1;
            }
        }
    }
    Some(table)
}

fn fixture_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/full-form-baseline.tsv")
}

fn render(table: &Table) -> String {
    let mut out = String::from("# metaclass\tproperty\tdigest\telements\tnonempty\n");
    for ((ty, prop), d) in table {
        out.push_str(&format!(
            "{ty}\t{prop}\t{:016x}\t{}\t{}\n",
            d.sum, d.elements, d.nonempty
        ));
    }
    out
}

fn parse(text: &str) -> Table {
    let mut table = Table::new();
    for line in text
        .lines()
        .filter(|l| !l.starts_with('#') && !l.is_empty())
    {
        let cols: Vec<&str> = line.split('\t').collect();
        assert_eq!(cols.len(), 5, "malformed baseline line: {line}");
        table.insert(
            (cols[0].to_string(), cols[1].to_string()),
            Digest {
                sum: u64::from_str_radix(cols[2], 16).unwrap(),
                elements: cols[3].parse().unwrap(),
                nonempty: cols[4].parse().unwrap(),
            },
        );
    }
    table
}

#[test]
fn corpus_full_form_matches_baseline() {
    let Some(actual) = digest_corpus() else {
        return;
    };
    let path = fixture_path();
    if std::env::var_os("SYSMLV2_UPDATE_BASELINE").is_some() {
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(&path, render(&actual)).unwrap();
        eprintln!(
            "baseline written: {} pairs over {} metaclasses",
            actual.len(),
            actual
                .keys()
                .map(|(t, _)| t)
                .collect::<std::collections::BTreeSet<_>>()
                .len()
        );
        return;
    }
    let text = fs::read_to_string(&path).unwrap_or_else(|_| {
        panic!(
            "no baseline at {} — create it with SYSMLV2_UPDATE_BASELINE=1",
            path.display()
        )
    });
    let expected = parse(&text);
    // Aggregate by property: a promoted Type-level name touches ~90
    // metaclasses, so per-pair lines would swamp the report. Metaclasses
    // are listed only for properties with few affected pairs.
    #[derive(Default)]
    struct Change {
        added: Vec<String>,
        removed: Vec<String>,
        changed: Vec<String>,
        nonempty_before: u64,
        nonempty_after: u64,
    }
    let mut by_prop: BTreeMap<String, Change> = BTreeMap::new();
    for (key, d) in &actual {
        match expected.get(key) {
            None => by_prop
                .entry(key.1.clone())
                .or_default()
                .added
                .push(key.0.clone()),
            Some(e) if e != d => {
                let c = by_prop.entry(key.1.clone()).or_default();
                let what = if e.nonempty == d.nonempty && e.elements == d.elements {
                    format!("{} (values changed)", key.0)
                } else {
                    format!(
                        "{} (non-empty {} -> {}, elements {} -> {})",
                        key.0, e.nonempty, d.nonempty, e.elements, d.elements
                    )
                };
                c.changed.push(what);
                c.nonempty_before += e.nonempty;
                c.nonempty_after += d.nonempty;
            }
            Some(_) => {}
        }
    }
    for key in expected.keys() {
        if !actual.contains_key(key) {
            by_prop
                .entry(key.1.clone())
                .or_default()
                .removed
                .push(key.0.clone());
        }
    }
    if !by_prop.is_empty() {
        let mut report = String::new();
        for (prop, c) in by_prop.iter().take(100) {
            let pairs = c.added.len() + c.removed.len() + c.changed.len();
            report.push_str(&format!(
                "  {prop}: {pairs} pairs (+{} -{} ~{}; non-empty {} -> {} over the changed pairs)\n",
                c.added.len(),
                c.removed.len(),
                c.changed.len(),
                c.nonempty_before,
                c.nonempty_after
            ));
            if pairs <= 10 {
                for m in &c.added {
                    report.push_str(&format!("      + {m}\n"));
                }
                for m in &c.removed {
                    report.push_str(&format!("      - {m}\n"));
                }
                for m in &c.changed {
                    report.push_str(&format!("      ~ {m}\n"));
                }
            }
        }
        if by_prop.len() > 100 {
            report.push_str(&format!("  … {} more properties\n", by_prop.len() - 100));
        }
        panic!(
            "full-form emission differs from the baseline in {} properties; adjudicate each, then \
             refresh with SYSMLV2_UPDATE_BASELINE=1 and commit the fixture diff:\n{report}",
            by_prop.len()
        );
    }
}
