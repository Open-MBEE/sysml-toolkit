//! Session build timings: the language server's completion/navigation
//! session over a workspace plus the standard library.
//!
//!     sessionbench <LIB_DIR> <CORPUS_DIR> [reps] [only=<case,...>]
//!
//! Wall and thread-CPU milliseconds per case (min / median over reps).
use std::path::{Path, PathBuf};
use std::time::Instant;
use sysmlv2_model::json::ResolvedModel;
use sysmlv2_model::model::Model;
use sysmlv2_transform::{Library, Session};

#[cfg(any(target_os = "macos", target_os = "linux"))]
#[repr(C)]
struct Timespec {
    sec: i64,
    nsec: i64,
}
#[cfg(any(target_os = "macos", target_os = "linux"))]
extern "C" {
    fn clock_gettime(clock: u32, tp: *mut Timespec) -> i32;
}
/// The calling thread's CPU time in milliseconds: what a build costs
/// regardless of what else the machine is running.
#[cfg(any(target_os = "macos", target_os = "linux"))]
fn cpu_ms() -> f64 {
    // CLOCK_THREAD_CPUTIME_ID: 16 on macOS, 3 on Linux.
    let id = if cfg!(target_os = "macos") { 16 } else { 3 };
    let mut ts = Timespec { sec: 0, nsec: 0 };
    // SAFETY: `ts` is a valid, writable timespec for the call's duration.
    unsafe { clock_gettime(id, &mut ts) };
    ts.sec as f64 * 1e3 + ts.nsec as f64 / 1e6
}
/// Elsewhere the wall clock stands in.
#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn cpu_ms() -> f64 {
    thread_local! { static START: Instant = Instant::now(); }
    START.with(|start| start.elapsed().as_secs_f64() * 1e3)
}

const VEHICLE: &str = r#"package VehicleModel {
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
        part :>> engine { attribute :>> mass = 150 [kg]; }
    }
}
"#;

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for e in entries.flatten() {
        let p = e.path();
        if p.is_dir() {
            collect(&p, out);
        } else if matches!(
            p.extension().and_then(|e| e.to_str()),
            Some("sysml" | "kerml")
        ) {
            out.push(p);
        }
    }
}

fn read_units(dir: &Path, relative: bool) -> Vec<(String, String)> {
    let mut files = Vec::new();
    collect(dir, &mut files);
    files.sort();
    files
        .iter()
        .map(|p| {
            let name = if relative {
                p.strip_prefix(dir)
                    .unwrap()
                    .components()
                    .map(|c| c.as_os_str().to_string_lossy())
                    .collect::<Vec<_>>()
                    .join("/")
            } else {
                p.display().to_string()
            };
            (name, std::fs::read_to_string(p).unwrap())
        })
        .collect()
}

fn stats(xs: &mut [f64]) -> (f64, f64) {
    xs.sort_by(|a, b| a.partial_cmp(b).unwrap());
    (xs[0], xs[xs.len() / 2])
}

/// Time `f` over `reps` after one untimed warm-up (disk caches, allocator).
/// What `f` returns is dropped after the next timing, not within it, as a
/// server drops the session it held while building the next.
fn case<T>(
    name: &str,
    reps: usize,
    only: &Option<Vec<String>>,
    units: usize,
    mut f: impl FnMut() -> T,
) {
    if let Some(only) = only {
        if !only.iter().any(|o| o == name) {
            return;
        }
    }
    let mut previous = Some(f());
    let mut wall = Vec::new();
    let mut cpu = Vec::new();
    for _ in 0..reps {
        let c0 = cpu_ms();
        let t0 = Instant::now();
        let result = std::hint::black_box(f());
        wall.push(t0.elapsed().as_secs_f64() * 1e3);
        cpu.push(cpu_ms() - c0);
        previous = Some(result);
    }
    drop(previous);
    let (wmin, wmed) = stats(&mut wall);
    let (cmin, cmed) = stats(&mut cpu);
    println!(
        "{name:<14} cpu min {cmin:8.1} med {cmed:8.1} | wall min {wmin:8.1} med {wmed:8.1} ms  (units {units})"
    );
}

fn main() {
    let mut args = std::env::args().skip(1);
    let lib_dir = PathBuf::from(args.next().expect("LIB_DIR"));
    let corpus_dir = PathBuf::from(args.next().expect("CORPUS_DIR"));
    let mut reps = 5;
    let mut only: Option<Vec<String>> = None;
    let mut exclude: Vec<String> = Vec::new();
    for a in args {
        if let Some(pat) = a.strip_prefix("exclude=") {
            exclude.push(pat.to_string());
        } else if let Some(list) = a.strip_prefix("only=") {
            only = Some(list.split(',').map(str::to_string).collect());
        } else {
            reps = a.parse().unwrap();
        }
    }
    let mut ws = read_units(&corpus_dir, false);
    ws.retain(|(name, _)| !exclude.iter().any(|pat| name.contains(pat.as_str())));
    ws.push(("vehicle.sysml".to_string(), VEHICLE.to_string()));
    let one = vec![("vehicle.sysml".to_string(), VEHICLE.to_string())];
    eprintln!("workspace {} units", ws.len());

    // In-memory library in bundle order: sorted library files, then the
    // ambient units, as the browser bundle lays them out.
    let mut lib_units = read_units(&lib_dir, true);
    lib_units.extend(sysmlv2_model::ambient::units());
    let snapshot = {
        let mut model = Model::new();
        for (name, src) in &lib_units {
            model.add_library_source(name.clone(), src);
        }
        model.record_library_cache();
        let _ = ResolvedModel::build(&model);
        model.take_recorded_library_cache().unwrap().to_bytes()
    };
    eprintln!(
        "library {} units; snapshot {} bytes",
        lib_units.len(),
        snapshot.len()
    );

    let dir = Library::dir(&lib_dir);
    // The previous session outlives the next build, as it does in a
    // server, so the in-process prepared library stays shared.
    let build = |sources: &Vec<(String, String)>, lib: &Library| {
        Session::from_sources_with_library(sources.clone(), Some(lib.clone())).unwrap()
    };
    case("dir-ws", reps, &only, ws.len(), || build(&ws, &dir));
    case("dir-one", reps, &only, one.len(), || build(&one, &dir));
    let snap = Library::sources_with_snapshot(lib_units.clone(), snapshot.clone());
    case("snap-one", reps, &only, one.len(), || build(&one, &snap));
    case("snap-ws", reps, &only, ws.len(), || build(&ws, &snap));
    let src = Library::sources(lib_units.clone());
    case("src-one", reps, &only, one.len(), || build(&one, &src));
    let prepared = Library::prepared_sources(lib_units.clone(), Some(snapshot.clone())).unwrap();
    case("prep-one", reps, &only, one.len(), || {
        build(&one, &prepared)
    });
    case("prep-ws", reps, &only, ws.len(), || build(&ws, &prepared));

    // Sessions started from the outcomes the previous one settled on, as
    // the language server starts them: the same units; a comment appended
    // to the first unit on alternate builds; the last unit's `name`
    // retyped on alternate builds, which changes one outcome.
    let retyped = VEHICLE.replace("attribute name : String;", "attribute name : Real;");
    assert_ne!(retyped, VEHICLE);
    for (label, edit) in [("warm-same", 0), ("warm-comment", 1), ("warm-retype", 2)] {
        let mut settled = Session::from_sources_with_library(ws.clone(), Some(prepared.clone()))
            .unwrap()
            .settled_outcomes();
        let mut flip = false;
        case(label, reps, &only, ws.len(), || {
            let mut sources = ws.clone();
            flip = !flip;
            match edit {
                1 if flip => sources[0].1.push_str("\n// edited\n"),
                2 if flip => sources.last_mut().unwrap().1 = retyped.clone(),
                _ => {}
            }
            let session =
                Session::from_sources_settled(sources, Some(prepared.clone()), settled.clone())
                    .unwrap();
            settled = session.settled_outcomes();
            session
        });
    }

    // Post-build semantic queries a unit completion issues: quantity
    // dimensions of every attribute definition, on a fresh session.
    for (label, lib, sources) in [
        ("dims-dir-one", &dir, &one),
        ("dims-snap-one", &snap, &one),
        ("dims-prep-one", &prepared, &one),
    ] {
        if only.as_ref().is_some_and(|o| !o.iter().any(|s| s == label)) {
            continue;
        }
        let mut firsts = Vec::new();
        let mut seconds = Vec::new();
        for _ in 0..reps.max(1) {
            let mut s =
                Session::from_sources_with_library(sources.clone(), Some(lib.clone())).unwrap();
            let r = s.resolved();
            let defs = r.elements_of_metaclass("AttributeDefinition");
            let c0 = cpu_ms();
            let mut known = 0;
            for &d in &defs {
                known += r.quantity_dims_of_type(d).is_some() as usize;
            }
            let c1 = cpu_ms();
            for &d in &defs {
                std::hint::black_box(r.quantity_dims_of_type(d));
            }
            let c2 = cpu_ms();
            firsts.push(c1 - c0);
            seconds.push(c2 - c1);
            if firsts.len() == 1 {
                eprintln!(
                    "{label}: {} attribute definitions, {known} with dimensions",
                    defs.len()
                );
            }
        }
        let (f, _) = stats(&mut firsts);
        let (g, _) = stats(&mut seconds);
        println!("{label:<14} cpu min first {f:8.1} repeat {g:8.1} ms");
    }

    // Stage breakdown of the directory path over the workspace.
    if only
        .as_ref()
        .is_none_or(|o| o.iter().any(|s| s == "stages"))
    {
        for _ in 0..3 {
            let c0 = cpu_ms();
            let mut model = Model::new();
            let load =
                sysmlv2_model::prepared::load_library_with_cache(&mut model, &lib_dir).unwrap();
            let c1 = cpu_ms();
            for (name, src) in &ws {
                model.add_source(name.clone(), src);
            }
            let c2 = cpu_ms();
            let resolved = ResolvedModel::build(&model);
            let c3 = cpu_ms();
            std::hint::black_box((&resolved, &load.recording_path));
            println!(
                "stages(dir-ws) cpu: library {:.1}  user parse {:.1}  resolve {:.1} ms",
                c1 - c0,
                c2 - c1,
                c3 - c2
            );
        }
    }
}
