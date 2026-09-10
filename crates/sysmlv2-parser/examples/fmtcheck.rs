//! Dev tool: run formatter gates over the corpus and show failure context.
#![allow(clippy::needless_range_loop)]
use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::ast::Dialect;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};
use sysmlv2_parser::print::format_source;
use sysmlv2_parser::span::LineIndex;

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    if let Ok(entries) = fs::read_dir(dir) {
        for e in entries.flatten() {
            let p = e.path();
            if p.is_dir() {
                collect(&p, out);
            } else if matches!(
                p.extension().and_then(|x| x.to_str()),
                Some("sysml" | "kerml")
            ) {
                out.push(p);
            }
        }
    }
}

fn main() {
    let root = std::env::args()
        .nth(1)
        .unwrap_or("spec-refs/SysML-v2-Release".into());
    let only = std::env::args().nth(2);
    let mut files = Vec::new();
    collect(Path::new(&root), &mut files);
    files.sort();
    let (mut ok, mut bad) = (0, 0);
    for f in &files {
        if let Some(o) = &only {
            if !f.to_string_lossy().contains(o.as_str()) {
                continue;
            }
        }
        let src = fs::read_to_string(f).unwrap();
        let dialect = if f.extension().and_then(|x| x.to_str()) == Some("kerml") {
            Dialect::Kerml
        } else {
            Dialect::Sysml
        };
        let formatted = match format_source(&src, dialect) {
            Ok(x) => x,
            Err(d) => {
                bad += 1;
                println!("== {} FORMAT-ERR {}", f.display(), d[0].message);
                continue;
            }
        };
        let re = match dialect {
            Dialect::Sysml => parse_source(&formatted),
            Dialect::Kerml => parse_kerml_source(&formatted),
        };
        if !re.diagnostics.is_empty() {
            bad += 1;
            let d = &re.diagnostics[0];
            let idx = LineIndex::new(&formatted);
            let pos = idx.line_col(d.span.start);
            let line = formatted.lines().nth(pos.line as usize - 1).unwrap_or("");
            println!(
                "== {} REPARSE {}\n    | {}",
                f.display(),
                d.message,
                line.trim()
            );
            continue;
        }
        let orig = match dialect {
            Dialect::Sysml => parse_source(&src),
            Dialect::Kerml => parse_kerml_source(&src),
        };
        let norm = |u: &sysmlv2_parser::ast::SourceUnit| {
            format!("{u:#?}")
                .lines()
                .filter(|l| !l.trim_start().starts_with("span:"))
                .collect::<Vec<_>>()
                .join("\n")
        };
        let (a, b) = (norm(&orig.unit), norm(&re.unit));
        if a != b {
            bad += 1;
            // First differing line with context.
            let (al, bl): (Vec<_>, Vec<_>) = (a.lines().collect(), b.lines().collect());
            for i in 0..al.len().min(bl.len()) {
                if al[i] != bl[i] {
                    println!("== {} AST-DIFF at line {i}", f.display());
                    let lo = i.saturating_sub(10);
                    for j in lo..(i + 3).min(al.len()) {
                        println!("    - {}", al[j].trim());
                    }
                    for j in lo..(i + 3).min(bl.len()) {
                        println!("    + {}", bl[j].trim());
                    }
                    break;
                }
            }
            continue;
        }
        let second = format_source(&formatted, dialect);
        match second {
            Ok(s2) if s2 == formatted => ok += 1,
            Ok(s2) => {
                bad += 1;
                for (i, (x, y)) in formatted.lines().zip(s2.lines()).enumerate() {
                    if x != y {
                        println!(
                            "== {} NOT-IDEMPOTENT at line {i}\n    1: {}\n    2: {}",
                            f.display(),
                            x.trim(),
                            y.trim()
                        );
                        break;
                    }
                }
            }
            Err(d) => {
                bad += 1;
                println!("== {} SECOND-FORMAT-ERR {}", f.display(), d[0].message);
            }
        }
    }
    println!("{ok} ok, {bad} failing");
}
