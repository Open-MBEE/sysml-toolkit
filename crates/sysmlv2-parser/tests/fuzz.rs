//! Deterministic in-tree fuzz gate: mutated corpus samples and
//! synthesized garbage must never panic any pipeline stage — lexer, both
//! parsers, compact/full JSON emission, printer, formatter, JSON reader.
//!
//! A fixed-seed xorshift PRNG makes every run reproducible; failures print
//! the seed and mutation index. Deeper runs: `FUZZ_ITERS=10000 cargo test
//! --release --test fuzz`. (True coverage-guided fuzzing via cargo-fuzz /
//! libFuzzer needs a nightly toolchain and is tracked in the plan as an
//! optional follow-up; this gate is the always-on floor.)

use std::fs;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};

/// xorshift64* — tiny, deterministic, no dependencies.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x >> 12;
        x ^= x << 25;
        x ^= x >> 27;
        self.0 = x;
        x.wrapping_mul(0x2545F4914F6CDD1D)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// One byte-level mutation, repaired to valid UTF-8.
fn mutate(rng: &mut Rng, src: &str) -> String {
    let mut bytes = src.as_bytes().to_vec();
    let printable = b"{}();:.*=<>[]'\"@#$/\\ \t\n_abcdefXYZ0123456789";
    for _ in 0..=rng.below(8) {
        if bytes.is_empty() {
            break;
        }
        match rng.below(6) {
            // Flip a byte to a printable.
            0 => {
                let i = rng.below(bytes.len());
                bytes[i] = printable[rng.below(printable.len())];
            }
            // Delete a run.
            1 => {
                let i = rng.below(bytes.len());
                let n = (rng.below(24) + 1).min(bytes.len() - i);
                bytes.drain(i..i + n);
            }
            // Duplicate a run elsewhere.
            2 => {
                let i = rng.below(bytes.len());
                let n = (rng.below(24) + 1).min(bytes.len() - i);
                let chunk: Vec<u8> = bytes[i..i + n].to_vec();
                let at = rng.below(bytes.len());
                for (k, b) in chunk.into_iter().enumerate() {
                    bytes.insert(at + k, b);
                }
            }
            // Truncate.
            3 => {
                let i = rng.below(bytes.len());
                bytes.truncate(i);
            }
            // Insert structural noise.
            4 => {
                let at = rng.below(bytes.len() + 1);
                let noise: &[u8] = match rng.below(6) {
                    0 => b"{",
                    1 => b"}",
                    2 => b"/*",
                    3 => b"'",
                    4 => b";;",
                    _ => b"::>",
                };
                for (k, &b) in noise.iter().enumerate() {
                    bytes.insert(at + k, b);
                }
            }
            // Swap two runs' first bytes.
            _ => {
                let i = rng.below(bytes.len());
                let j = rng.below(bytes.len());
                bytes.swap(i, j);
            }
        }
    }
    String::from_utf8_lossy(&bytes).into_owned()
}

/// Exercise every stage on one input; panics propagate to the test.
fn exercise(src: &str) {
    for parse in [parse_source(src), parse_kerml_source(src)] {
        // Emission must accept any parse result (diagnostics or not).
        let json = sysmlv2_parser::json::to_compact_json(&parse.unit);
        let _ = sysmlv2_parser::full::to_full_json(&parse.unit);
        // Printing must accept any AST the parser produces.
        let printed = sysmlv2_parser::print::print_source(&parse.unit);
        // The printer's output must itself re-parse without panicking.
        let _ = parse_source(&printed);
        // The JSON reader must accept whatever the emitter produced.
        let _ = sysmlv2_parser::lift::from_compact_json(&json);
    }
    let _ = sysmlv2_parser::print::format_source(src, sysmlv2_parser::ast::Dialect::Sysml);
    let _ = sysmlv2_parser::print::format_source(src, sysmlv2_parser::ast::Dialect::Kerml);
}

fn seeds() -> Vec<String> {
    let root = sysmlv2_testkit::corpus_root();
    // A deliberately diverse sample: structure, behavior, expressions,
    // views/metadata, KerML kernel, and interconnect-heavy files.
    let picks = [
        "sysml/src/examples/Vehicle Example/VehicleUsages.sysml",
        "sysml/src/examples/Simple Tests/ConstraintTest.sysml",
        "sysml/src/training/16. Conditional Succession/Conditional Succession Example-1.sysml",
        "sysml/src/training/25. Views/Views Example.sysml",
        "sysml/src/validation/05-State-based Behavior/5-State-based Behavior-1.sysml",
        "sysml.library/Kernel Libraries/Kernel Functions Library/ControlFunctions.kerml",
        "sysml.library/Kernel Libraries/Kernel Data Type Library/ScalarValues.kerml",
    ];
    let mut seeds: Vec<String> = picks
        .iter()
        .filter_map(|p| fs::read_to_string(root.join(p)).ok())
        .collect();
    assert!(seeds.len() >= 4, "expected corpus seed files");
    // Plus small synthetic seeds that stress token-level edges.
    seeds.push("part def P { attribute x : Real = 1 + 2 * (3 .. 4); }".into());
    seeds.push("package '„Ünïcodé–ID‟ x' { /* … */ comment C /* body */ }".into());
    seeds.push(String::new());
    seeds
}

#[test]
fn mutated_sources_never_panic() {
    install_panic_hook();
    let iters: usize = std::env::var("FUZZ_ITERS")
        .ok()
        .and_then(|v| v.parse().ok())
        .unwrap_or(400);
    let seeds = seeds();
    let mut rng = Rng(0x5EED_CAFE_F00D_D00D);
    for i in 0..iters {
        let seed = &seeds[rng.below(seeds.len())];
        let mutated = mutate(&mut rng, seed);
        // On panic the hook prints this context before unwinding.
        LAST.with(|l| *l.borrow_mut() = Some((i, mutated.clone())));
        exercise(&mutated);
    }
    LAST.with(|l| *l.borrow_mut() = None);
}

#[test]
fn pathological_inputs_never_panic() {
    for src in [
        "{".repeat(2000),
        "}".repeat(2000),
        "(".repeat(2000),
        "part ".repeat(2000),
        "a.".repeat(2000),
        "x::".repeat(2000),
        "'".repeat(999),
        "/*".repeat(500),
        "if ".repeat(600),
        "#".repeat(1000),
        "$::".repeat(800),
        format!("part def P {{ x = {}1; }}", "-".repeat(1500)),
    ] {
        exercise(&src);
    }
}

thread_local! {
    static LAST: std::cell::RefCell<Option<(usize, String)>> =
        const { std::cell::RefCell::new(None) };
}

/// Print the failing mutation (iteration + full input) before the panic
/// unwinds, so failures are reproducible from the log alone.
fn install_panic_hook() {
    let default = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        LAST.with(|l| {
            if let Some((i, src)) = &*l.borrow() {
                eprintln!(
                    "fuzz failure at iteration {i}; input ({} bytes):\n{src}",
                    src.len()
                );
            }
        });
        default(info);
    }));
}
