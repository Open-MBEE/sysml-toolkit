//! Reproducible checking-stage benchmark (release builds only).
//! cargo run --release -p sysmlv2-transform --example importbench -- MODEL_DIR [cold]
use serde_json::json;
use std::{fs, time::Instant};
use sysmlv2_model::{ambient, check, json::ResolvedModel, model::Model};

fn main() {
    let args: Vec<_> = std::env::args().collect();
    let path = std::path::Path::new(args.get(1).expect("MODEL_DIR required"));
    let cold = args.get(2).is_some_and(|s| s == "cold");
    let library = sysmlv2_testkit::library_dir();
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    ambient::add_to(&mut base);
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache = base.take_recorded_library_cache().unwrap();
    let mut paths = Vec::new();
    sysmlv2_testkit::collect_files(path, &mut paths);
    paths.sort();
    assert!(!paths.is_empty());
    let sources: Vec<_> = paths
        .iter()
        .map(|p| (p.display().to_string(), fs::read_to_string(p).unwrap()))
        .collect();
    let mut rows = Vec::new();
    for _ in 0..3 {
        let total = Instant::now();
        let mut model = Model::new();
        model.load_library_dir(&library).unwrap();
        ambient::add_to(&mut model);
        if !cold {
            model.set_library_cache(cache.clone());
        }
        let offset = model.unit_count();
        let texts: Vec<_> = sources
            .iter()
            .enumerate()
            .map(|(i, (name, text))| {
                model.add_source(name, text);
                (offset + i, text.clone())
            })
            .collect();
        let start = Instant::now();
        let mut resolved = ResolvedModel::build(&model);
        let resolution = start.elapsed().as_secs_f64() * 1000.;
        let start = Instant::now();
        let references = check::validate_model_with(&mut resolved, &model);
        let referential = start.elapsed().as_secs_f64() * 1000.;
        let start = Instant::now();
        let semantics = check::validate_semantics_with(&mut resolved, &model);
        let semantic = start.elapsed().as_secs_f64() * 1000.;
        let start = Instant::now();
        let unused = sysmlv2_transform::unused_private_imports_with(&mut resolved, &texts);
        let imports = start.elapsed().as_secs_f64() * 1000.;
        rows.push(json!({"resolution_ms": resolution, "referential_ms": referential,
            "semantic_ms": semantic, "unused_imports_ms": imports, "total_ms": total.elapsed().as_secs_f64()*1000.,
            "referential_count": references.len(), "semantic_count": semantics.len(),
            "findings": unused.into_iter().map(|(u, s)| json!({"file": sources[u-offset].0, "start": s.start, "end": s.end})).collect::<Vec<_>>() }));
    }
    println!("{}", serde_json::to_string_pretty(&json!({"cold": cold, "files": sources.len(), "bytes": sources.iter().map(|(_, s)|s.len()).sum::<usize>(), "runs": rows})).unwrap());
}
