//! Stage timings for prepared-library startup and validation.
//! Append `reuse` to retain the library, `syntax` to request all library ASTs.
use std::{sync::Arc, time::Instant};
use sysmlv2_model::{check, json::ResolvedModel, model::Model, prepared::PreparedLibrary};
fn main() {
    let path = std::env::args().nth(1).expect("MODEL_DIR");
    let mut files = Vec::new();
    sysmlv2_testkit::collect_files(std::path::Path::new(&path), &mut files);
    files.sort();
    let sources: Vec<_> = files
        .iter()
        .map(|p| (p.display().to_string(), std::fs::read_to_string(p).unwrap()))
        .collect();
    let mut base = Model::new();
    let start = Instant::now();
    base.load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let parse = start.elapsed();
    let start = Instant::now();
    let prepared = base.prepare_library().unwrap();
    let prepare = start.elapsed();
    let start = Instant::now();
    let bytes = prepared.to_bytes(1).unwrap();
    let encode = start.elapsed();
    eprintln!(
        "library parse {:?}; prepare {:?}; encode {:?}; bytes {}",
        parse,
        prepare,
        encode,
        bytes.len()
    );
    drop(base);
    drop(prepared);
    let reuse = std::env::args().skip(2).any(|s| s == "reuse");
    let syntax = std::env::args().skip(2).any(|s| s == "syntax");
    let retained = reuse.then(|| Arc::new(PreparedLibrary::from_bytes(&bytes, 1).unwrap()));
    let mut rows = Vec::new();
    for _ in 0..3 {
        let start = Instant::now();
        let prepared = retained
            .clone()
            .unwrap_or_else(|| Arc::new(PreparedLibrary::from_bytes(&bytes, 1).unwrap()));
        let decode = start.elapsed();
        let mut model = Model::new();
        let start = Instant::now();
        prepared.clone().install(&mut model).unwrap();
        let install = start.elapsed();
        let start = Instant::now();
        if syntax {
            std::hint::black_box(model.units());
        }
        let syntax_time = start.elapsed();
        let start = Instant::now();
        let offset = model.unit_count();
        let texts: Vec<_> = sources
            .iter()
            .enumerate()
            .map(|(i, (n, s))| {
                model.add_source(n, s);
                (offset + i, s.clone())
            })
            .collect();
        let user_parse = start.elapsed();
        let start = Instant::now();
        let mut r = ResolvedModel::build(&model);
        let build = start.elapsed();
        let start = Instant::now();
        let refs = check::validate_model_with(&mut r, &model);
        let referential = start.elapsed();
        let start = Instant::now();
        let semantics = check::validate_semantics_with(&mut r, &model);
        let semantic = start.elapsed();
        let start = Instant::now();
        let unused = sysmlv2_transform::unused_private_imports_with(&mut r, &texts);
        let imports = start.elapsed();
        let start = Instant::now();
        drop(r);
        drop(model);
        drop(prepared);
        let destruction = start.elapsed();
        rows.push(serde_json::json!({"retained_library":reuse,"requested_syntax":syntax,"syntax_ms":syntax_time.as_secs_f64()*1000.,"decode_ms":decode.as_secs_f64()*1000.,"install_ms":install.as_secs_f64()*1000.,"user_parse_ms":user_parse.as_secs_f64()*1000.,"build_ms":build.as_secs_f64()*1000.,"referential_ms":referential.as_secs_f64()*1000.,"semantic_ms":semantic.as_secs_f64()*1000.,"imports_ms":imports.as_secs_f64()*1000.,"drop_ms":destruction.as_secs_f64()*1000.,"refs":refs.len(),"semantics":semantics.len(),"unused":unused.len()}));
    }
    println!("{}", serde_json::to_string_pretty(&rows).unwrap());
}
