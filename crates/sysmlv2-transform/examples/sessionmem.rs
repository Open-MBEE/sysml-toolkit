//! Heap retained by each live session over one prepared library, and the
//! peak while one builds: what a host holding several sessions (a live
//! one, a fork, a staged check) pays per session.
//!
//!     SYSMLV2_THREADS=1 sessionmem <LIB_DIR> [sessions] [MODEL_FILE] [plans]
//!
//! The library is prepared, written as a snapshot and read back, as a host
//! reading the shipped snapshot has it; with `plans`, its plans are made
//! before it is written, as the package's generator makes them, so that
//! the first check reads them back instead of planning the library. Each
//! session is built over the same
//! small model (or `MODEL_FILE`), then checked, then emitted as compact
//! JSON, then (for the small model) edited and checked again; every
//! session stays live. Byte counts are the allocator's: live
//! bytes after each step, relative to the step before, and the peak above
//! the live bytes the step started from. Each step's wall time follows.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};
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

const MODEL: &str = r#"package VehicleModel {
    private import ISQ::*;
    private import SI::*;
    private import ScalarValues::*;
    part def Engine {
        attribute mass : MassValue;
        attribute power : PowerValue;
        port fuelIn : FuelPort;
    }
    port def FuelPort { in item fuel : Fuel; }
    item def Fuel;
    part def Wheel { attribute diameter : LengthValue; }
    part def Vehicle {
        attribute mass : MassValue = engine.mass + 4 * wheel.diameter * 0 [kg/m];
        attribute name : String;
        part engine : Engine;
        part wheel : Wheel[4];
    }
    part car : Vehicle {
        attribute :>> name = "car";
    }
}
"#;

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
        "{label:<28} kept {:>8.2} MB   peak +{:>8.2} MB   {:>9.2} ms",
        mb(live as isize - start as isize),
        mb((peak - start) as isize),
        took.as_secs_f64() * 1e3,
    );
    value
}

fn main() {
    let mut args = std::env::args().skip(1);
    let dir = args.next().expect("LIB_DIR");
    let sessions: usize = args.next().map_or(3, |n| n.parse().expect("a count"));
    let model = args.next().filter(|arg| arg != "plans").map_or_else(
        || MODEL.to_string(),
        |p| std::fs::read_to_string(p).unwrap(),
    );
    let plans = std::env::args().skip(2).any(|arg| arg == "plans");
    let mut files = Vec::new();
    sysmlv2_testkit::collect_files(std::path::Path::new(&dir), &mut files);
    files.sort();
    let units: Vec<(String, String)> = files
        .iter()
        .map(|p| {
            (
                p.strip_prefix(&dir).unwrap().display().to_string(),
                std::fs::read_to_string(p).unwrap(),
            )
        })
        .collect();
    let key =
        sysmlv2_model::libcache::hash_units(units.iter().map(|(n, t)| (n.as_str(), t.as_str())));
    let bytes = {
        let mut base = sysmlv2_model::model::Model::new();
        for (name, text) in &units {
            base.add_library_source(name.clone(), text);
        }
        let prepared = base.prepare_library().unwrap();
        if plans {
            prepared.make_plans();
        }
        prepared.to_bytes(key).unwrap()
    };
    let library = measure("library decode", || {
        Library::prepared_snapshot(units.clone(), &bytes, None).unwrap()
    });
    drop(bytes);
    let sources = vec![("model.sysml".to_string(), model)];
    let mut live = Vec::new();
    for i in 1..=sessions {
        let mut session = measure(&format!("session {i} build"), || {
            Session::from_sources_with_library(sources.clone(), Some(library.clone())).unwrap()
        });
        measure(&format!("session {i} check"), || {
            session.check_findings().len()
        });
        measure(&format!("session {i} compact json"), || {
            session.to_compact_json().to_string().len()
        });
        // An edit commits a rebuilt model (the old one alive meanwhile),
        // and the next check reads the rebuilt one.
        if let Some(car) = session.resolved().resolve_qualified("VehicleModel::car") {
            measure(&format!("session {i} edit"), || {
                let mut edit = session.edit();
                edit.rename(car, "car2");
                edit.commit().is_ok()
            });
            measure(&format!("session {i} check again"), || {
                session.check_findings().len()
            });
        }
        live.push(session);
    }
    println!("live sessions: {}", live.len());
}
