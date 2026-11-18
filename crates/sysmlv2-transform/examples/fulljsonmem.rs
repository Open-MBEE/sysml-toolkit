//! Heap and time of the full-form JSON export, by step, and where the
//! built document's bytes sit.
//!
//!     SYSMLV2_THREADS=1 fulljsonmem <LIB_DIR> <POLICY> [--interchange] [--text] MODEL_FILE...
//!
//! `POLICY` is `passthrough`, `closure` or `closure-implied`. The model
//! files open as one session over the library directory; with
//! `--interchange` the session is emitted as compact JSON and reopened
//! from it, as a host holding a stored payload opens it. The export is
//! then measured twice: as the document value followed by its
//! serialization (with a census of the value's nodes), and, with
//! `--text`, as the text written row by row. Byte counts are the
//! allocator's: live bytes kept by each step and the peak above the live
//! bytes the step started from.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
use sysmlv2_model::full::{EmissionPolicy, TextLayout, UnresolvedReferencePolicy};
use sysmlv2_model::json::ClosurePolicy;
use sysmlv2_transform::{Library, Session};

/// The system allocator, counting live bytes and their high-water mark.
struct Counting;
static LIVE: AtomicUsize = AtomicUsize::new(0);
static PEAK: AtomicUsize = AtomicUsize::new(0);

fn grew(by: usize) {
    let now = LIVE.fetch_add(by, Relaxed) + by;
    PEAK.fetch_max(now, Relaxed);
}

// SAFETY: every call forwards to `System` with the caller's arguments; the
// counters are only bookkeeping.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() {
            grew(layout.size());
        }
        p
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(layout) };
        if !p.is_null() {
            grew(layout.size());
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
        unsafe { System.dealloc(p, layout) };
        LIVE.fetch_sub(layout.size(), Relaxed);
    }
    unsafe fn realloc(&self, p: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let q = unsafe { System.realloc(p, layout, size) };
        if !q.is_null() {
            if size >= layout.size() {
                grew(size - layout.size());
            } else {
                LIVE.fetch_sub(layout.size() - size, Relaxed);
            }
        }
        q
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

fn mb(bytes: isize) -> f64 {
    bytes as f64 / 1e6
}

/// Run `step`, printing the live bytes it kept, the peak above where it
/// started and the time it took.
fn measure<T>(label: &str, step: impl FnOnce() -> T) -> T {
    let start = LIVE.load(Relaxed);
    PEAK.store(start, Relaxed);
    let clock = std::time::Instant::now();
    let value = step();
    let took = clock.elapsed();
    let live = LIVE.load(Relaxed);
    let peak = PEAK.load(Relaxed);
    println!(
        "{label:<28} kept {:>9.2} MB   peak +{:>9.2} MB   {:>9.2} ms",
        mb(live as isize - start as isize),
        mb((peak - start) as isize),
        took.as_secs_f64() * 1e3,
    );
    value
}

/// What the document's nodes are: how many single-key `{"@id": …}`
/// objects (one per reference), and how many of them sit in each
/// property's list.
#[derive(Default)]
struct Census {
    rows: usize,
    references: usize,
    other_objects: usize,
    arrays: usize,
    array_slots: usize,
    strings: usize,
    string_bytes: usize,
    scalars: usize,
    by_property: std::collections::BTreeMap<String, usize>,
}

fn is_reference(v: &serde_json::Value) -> bool {
    v.as_object()
        .is_some_and(|m| m.len() == 1 && m.contains_key("@id"))
}

fn census(v: &serde_json::Value, property: Option<&str>, out: &mut Census) {
    use serde_json::Value;
    match v {
        Value::Object(m) if is_reference(v) => {
            out.references += 1;
            if let Some(p) = property {
                *out.by_property.entry(p.to_string()).or_default() += 1;
            }
            out.strings += 1;
            out.string_bytes += m["@id"].as_str().map_or(0, str::len);
        }
        Value::Object(m) => {
            out.other_objects += 1;
            for (k, v) in m {
                census(v, Some(k), out);
            }
        }
        Value::Array(a) => {
            out.arrays += 1;
            out.array_slots += a.capacity();
            for v in a {
                census(v, property, out);
            }
        }
        Value::String(s) => {
            out.strings += 1;
            out.string_bytes += s.len();
        }
        _ => out.scalars += 1,
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let dir = args.next().expect("LIB_DIR");
    let closures = match args.next().expect("POLICY").as_str() {
        "passthrough" => ClosurePolicy::Passthrough,
        "closure" => ClosurePolicy::Closure {
            include_implied: false,
        },
        "closure-implied" => ClosurePolicy::Closure {
            include_implied: true,
        },
        other => panic!("unknown policy {other}"),
    };
    let rest: Vec<String> = args.collect();
    let interchange = rest.iter().any(|a| a == "--interchange");
    let text = rest.iter().any(|a| a == "--text");
    let sources: Vec<(String, String)> = rest
        .iter()
        .filter(|a| !a.starts_with("--"))
        .map(|p| (p.clone(), std::fs::read_to_string(p).unwrap()))
        .collect();
    let policy = EmissionPolicy {
        unresolved: UnresolvedReferencePolicy::Preserve,
        closures,
    };

    let library = Library::dir(&dir);
    let mut session = measure("session from sources", || {
        Session::from_sources_with_library(sources, Some(library.clone())).unwrap()
    });
    if interchange {
        let compact = measure("compact json", || session.to_compact_json());
        session = measure("session from interchange", || {
            Session::from_interchange_json_with(&compact, Some(&library)).unwrap()
        });
    }

    // What every export of this session pays before its first row: a
    // model resolved afresh, and the compact rows.
    measure("  (a resolved model)", || {
        drop(sysmlv2_model::json::ResolvedModel::build(session.model()));
    });
    measure("  (the compact rows)", || drop(session.to_compact_json()));
    let value = measure("full form, as a value", || {
        session.to_full_json_with_policy(policy).unwrap()
    });
    let serialized = measure("  its serialization", || value.to_string());
    println!(
        "  serialized bytes            {:>9.2} MB",
        mb(serialized.len() as isize)
    );
    let mut tally = Census {
        rows: value.as_array().map_or(0, Vec::len),
        ..Default::default()
    };
    census(&value, None, &mut tally);
    // One leaf node of the map behind every JSON object, whatever it holds.
    let leaf = 11 * (std::mem::size_of::<String>() + std::mem::size_of::<serde_json::Value>()) + 16;
    println!(
        "  rows {}  references {}  other objects {}  arrays {} ({} slots)  strings {} ({:.2} MB)  scalars {}",
        tally.rows,
        tally.references,
        tally.other_objects,
        tally.arrays,
        tally.array_slots,
        tally.strings,
        mb(tally.string_bytes as isize),
        tally.scalars,
    );
    println!(
        "  a reference holds {} B (map node {leaf} + key 3 + id 36) and serializes to 46 B: {:.2} MB of the value",
        leaf + 3 + 36,
        mb((tally.references * (leaf + 3 + 36)) as isize),
    );
    let mut by_property: Vec<_> = tally.by_property.iter().collect();
    by_property.sort_by(|a, b| b.1.cmp(a.1));
    for (name, count) in by_property.iter().take(16) {
        println!(
            "    {name:<32} {count:>9} references  {:>5.1}%",
            100.0 * **count as f64 / tally.references as f64
        );
    }
    measure("  dropping the value", || drop(value));

    if text {
        let streamed = measure("full form, as text", || {
            session
                .to_full_json_text_with_policy(policy, TextLayout::Compact)
                .unwrap()
        });
        println!(
            "  text bytes                  {:>9.2} MB   identical: {}",
            mb(streamed.len() as isize),
            streamed == serialized
        );
    }
}
