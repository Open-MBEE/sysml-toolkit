//! Corpus benchmark for `CBOR.md`: compact JSON vs compact CBOR over
//! real models — bytes on the wire (raw and deflate-compressed) and the
//! time each pipeline stage takes, from textual notation to serialized
//! form and back.
//!
//! Corpora:
//! - `library` — every textual unit of the vendored standard library,
//!   loaded as *user* sources so they serialize (the compact form emits
//!   user units only).
//! - `model` — the vendored end-to-end validation model
//!   (`spec-refs/apollo-11-sysml-v2`), resolved against the standard
//!   library; skipped with a note when the submodule is absent.
//!
//! Run: `cargo run --release -p sysmlv2-cbor --example corpus_bench`

use std::fs;
use std::time::Instant;

use serde_json::Value;
use sysmlv2_cbor::{from_compact_cbor, to_compact_cbor};
use sysmlv2_parser::json::model_to_compact_json;
use sysmlv2_parser::lift::from_compact_json;
use sysmlv2_parser::model::Model;
use sysmlv2_parser::print::print_source;

/// Median wall time of `runs` executions (1 warmup), in milliseconds.
fn time_ms<T>(runs: usize, mut f: impl FnMut() -> T) -> f64 {
    let _warmup = f();
    let mut samples: Vec<f64> = (0..runs)
        .map(|_| {
            let t = Instant::now();
            std::hint::black_box(f());
            t.elapsed().as_secs_f64() * 1e3
        })
        .collect();
    samples.sort_by(f64::total_cmp);
    samples[samples.len() / 2]
}

fn deflate_len(bytes: &[u8]) -> usize {
    miniz_oxide::deflate::compress_to_vec(bytes, 8).len()
}

struct Corpus {
    name: &'static str,
    sources: Vec<(String, String)>,
    with_library: bool,
}

fn bench(c: &Corpus) {
    let runs = 5;

    // Textual notation → parsed model (parse only; lowering/resolution
    // happens on first emission below).
    let parse_ms = time_ms(runs, || {
        let mut m = Model::new();
        if c.with_library {
            m.load_library_dir(&sysmlv2_testkit::library_dir()).unwrap();
        }
        for (name, text) in &c.sources {
            m.add_source(name.clone(), text);
        }
        m
    });
    let mut model = Model::new();
    if c.with_library {
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
    }
    for (name, text) in &c.sources {
        model.add_source(name.clone(), text);
    }

    // Model → compact element array (lowering + resolution + Value).
    let emit_ms = time_ms(runs, || model_to_compact_json(&model));
    let value = model_to_compact_json(&model);
    let n_elems = value.as_array().map_or(0, Vec::len);

    // Value → serialized form.
    let minify_ms = time_ms(runs, || serde_json::to_string(&value).unwrap());
    let pretty = serde_json::to_string_pretty(&value).unwrap();
    let minified = serde_json::to_string(&value).unwrap();
    let encode_ms = time_ms(runs, || to_compact_cbor(&value).unwrap());
    let cbor = to_compact_cbor(&value).unwrap();

    // Serialized form → Value.
    let json_parse_ms = time_ms(runs, || serde_json::from_str::<Value>(&minified).unwrap());
    let cbor_decode_ms = time_ms(runs, || from_compact_cbor(&cbor).unwrap());

    // Value → textual notation (shared lift + print; identical for both
    // serialized forms once the Value is in hand).
    let lift_ms = time_ms(runs, || {
        let lifted = from_compact_json(&value).unwrap();
        print_source(&lifted.unit)
    });

    // Id elision: the library names effective-name targets
    // when the corpus resolved against one.
    let lib_names: std::collections::HashMap<String, String> = if c.with_library {
        sysmlv2_parser::json::library_name_map(&model)
            .into_iter()
            .filter_map(|(id, segs)| segs.last().cloned().map(|n| (id.to_string(), n)))
            .collect()
    } else {
        Default::default()
    };
    let resolver = |s: &str| lib_names.get(s).cloned();
    let elided = sysmlv2_cbor::to_compact_cbor_elided(&value, &resolver).unwrap();
    let elide_encode_ms = time_ms(runs, || {
        sysmlv2_cbor::to_compact_cbor_elided(&value, &resolver).unwrap()
    });
    let elide_decode_ms = time_ms(runs, || {
        sysmlv2_cbor::from_compact_cbor_elided(&elided, &resolver).unwrap()
    });

    println!(
        "\n## {} — {} elements, {} textual units",
        c.name,
        n_elems,
        c.sources.len()
    );
    println!("\n| form | bytes | +deflate |");
    println!("|---|---:|---:|");
    println!(
        "| pretty JSON | {} | {} |",
        pretty.len(),
        deflate_len(pretty.as_bytes())
    );
    println!(
        "| minified JSON | {} | {} |",
        minified.len(),
        deflate_len(minified.as_bytes())
    );
    println!("| compact CBOR | {} | {} |", cbor.len(), deflate_len(&cbor));
    println!(
        "| compact CBOR --elide-ids | {} | {} |",
        elided.len(),
        deflate_len(&elided)
    );
    println!(
        "| ratio min-JSON / CBOR | {:.2}x | {:.2}x |",
        minified.len() as f64 / cbor.len() as f64,
        deflate_len(minified.as_bytes()) as f64 / deflate_len(&cbor) as f64
    );
    println!("\n| stage | median ms |");
    println!("|---|---:|");
    println!("| text → model (parse) | {parse_ms:.1} |");
    println!("| model → element array (lower+resolve+Value) | {emit_ms:.1} |");
    println!("| Value → minified JSON | {minify_ms:.1} |");
    println!("| Value → CBOR | {encode_ms:.1} |");
    println!("| minified JSON → Value | {json_parse_ms:.1} |");
    println!("| CBOR → Value | {cbor_decode_ms:.1} |");
    println!("| Value → CBOR --elide-ids (derive+verify) | {elide_encode_ms:.1} |");
    println!("| CBOR --elide-ids → Value (derive+digest) | {elide_decode_ms:.1} |");
    println!("| Value → textual notation (lift+print) | {lift_ms:.1} |");

    // Delta: an edit-sized commit — append a small package to
    // the last unit, diff, and compare against shipping the snapshot.
    let mut edited_sources = c.sources.clone();
    edited_sources
        .last_mut()
        .unwrap()
        .1
        .push_str("\npackage ZDeltaScratch { part def X; part x : X; }\n");
    let mut edited = Model::new();
    if c.with_library {
        edited
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
    }
    for (name, text) in &edited_sources {
        edited.add_source(name.clone(), text);
    }
    let target = model_to_compact_json(&edited);
    let strict = sysmlv2_cbor::delta_compact_cbor(&value, &target, &Default::default()).unwrap();
    let portable = sysmlv2_cbor::delta_compact_cbor(
        &value,
        &target,
        &sysmlv2_cbor::DeltaOptions {
            portable: true,
            ..Default::default()
        },
    )
    .unwrap();
    let snapshot = to_compact_cbor(&target).unwrap();
    println!("\n| edit-sized commit (append a small package) | bytes |");
    println!("|---|---:|");
    println!("| snapshot (compact CBOR) | {} |", snapshot.len());
    println!("| delta, strict | {} |", strict.len());
    println!("| delta, portable | {} |", portable.len());

    // Full form (emit view): derived properties materialized.
    let full = sysmlv2_parser::full::model_to_full_json_with(&model, false);
    let full_min = serde_json::to_string(&full).unwrap();
    let full_cbor = sysmlv2_cbor::to_full_cbor(&full).unwrap();
    println!("\n| full form | bytes | +deflate |");
    println!("|---|---:|---:|");
    println!(
        "| minified full JSON | {} | {} |",
        full_min.len(),
        deflate_len(full_min.as_bytes())
    );
    println!(
        "| full CBOR | {} | {} |",
        full_cbor.len(),
        deflate_len(&full_cbor)
    );
    println!(
        "| ratio | {:.2}x | {:.2}x |",
        full_min.len() as f64 / full_cbor.len() as f64,
        deflate_len(full_min.as_bytes()) as f64 / deflate_len(&full_cbor) as f64
    );
}

fn main() {
    let mut lib_files = Vec::new();
    sysmlv2_testkit::collect_files(&sysmlv2_testkit::library_dir(), &mut lib_files);
    let library = Corpus {
        name: "library",
        sources: lib_files
            .iter()
            .map(|f| {
                (
                    f.file_name().unwrap().to_string_lossy().into_owned(),
                    fs::read_to_string(f).unwrap(),
                )
            })
            .collect(),
        with_library: false,
    };
    bench(&library);

    match sysmlv2_testkit::apollo_files() {
        Some(files) => {
            let model = Corpus {
                name: "model",
                sources: files
                    .iter()
                    .map(|f| {
                        (
                            f.file_name().unwrap().to_string_lossy().into_owned(),
                            fs::read_to_string(f).unwrap(),
                        )
                    })
                    .collect(),
                with_library: true,
            };
            bench(&model);
        }
        None => eprintln!("note: end-to-end model submodule absent — corpus skipped"),
    }
}
