//! Dev tool: JSON round-trip gate — emit(parse(print(lift(emit(parse(x))))))
//! must equal emit(parse(x)) for every corpus file.
use std::fs;
use std::path::{Path, PathBuf};
use sysmlv2_parser::ast::Dialect;
use sysmlv2_parser::json::to_compact_json;
use sysmlv2_parser::lift::from_compact_json;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};
use sysmlv2_parser::print::print_source;

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
        let parse = |s: &str| match dialect {
            Dialect::Sysml => parse_source(s),
            Dialect::Kerml => parse_kerml_source(s),
        };
        let orig = parse(&src);
        let json1 = to_compact_json(&orig.unit);
        let lifted = match from_compact_json(&json1) {
            Ok(l) => l,
            Err(e) => {
                bad += 1;
                println!("== {} LIFT-ERR {e}", f.display());
                continue;
            }
        };
        if !lifted.errors.is_empty() {
            bad += 1;
            println!("== {} LIFT-WARN {}", f.display(), lifted.errors[0]);
            continue;
        }
        let text2 = print_source(&lifted.unit);
        let reparsed = parse(&text2);
        if !reparsed.diagnostics.is_empty() {
            bad += 1;
            let d = &reparsed.diagnostics[0];
            let idx = sysmlv2_parser::span::LineIndex::new(&text2);
            let pos = idx.line_col(d.span.start);
            let line = text2.lines().nth(pos.line as usize - 1).unwrap_or("");
            println!(
                "== {} REPARSE {}\n    | {}",
                f.display(),
                d.message,
                line.trim()
            );
            continue;
        }
        let json2 = to_compact_json(&reparsed.unit);
        if json1 == json2 {
            ok += 1;
        } else {
            bad += 1;
            // Find first differing element.
            let (a1, a2) = (json1.as_array().unwrap(), json2.as_array().unwrap());
            let mut shown = false;
            let types1: std::collections::HashMap<&str, &str> = a1
                .iter()
                .filter_map(|e| Some((e["@id"].as_str()?, e["@type"].as_str()?)))
                .collect();
            let types2: std::collections::HashMap<&str, &str> = a2
                .iter()
                .filter_map(|e| Some((e["@id"].as_str()?, e["@type"].as_str()?)))
                .collect();
            for i in 0..a1.len().min(a2.len()) {
                if a1[i] != a2[i] {
                    println!(
                        "== {} JSON-DIFF elem {i} @type {}",
                        f.display(),
                        a1[i]["@type"]
                    );
                    let kids =
                        |v: &serde_json::Value, types: &std::collections::HashMap<&str, &str>| {
                            v["ownedRelationship"]
                                .as_array()
                                .map(|a| {
                                    a.iter()
                                        .filter_map(|r| r["@id"].as_str())
                                        .map(|id| types.get(id).unwrap_or(&"?").to_string())
                                        .collect::<Vec<_>>()
                                        .join(",")
                                })
                                .unwrap_or_default()
                        };
                    println!("    - kids: {}", kids(&a1[i], &types1));
                    println!("    + kids: {}", kids(&a2[i], &types2));
                    for (k, v) in a1[i].as_object().unwrap() {
                        if a2[i].get(k) != Some(v) && k != "ownedRelationship" {
                            println!("    key {k}: {v} => {}", a2[i][k]);
                        }
                    }
                    // Dump the first differing child pair fully.
                    let ids1: Vec<&str> = a1[i]["ownedRelationship"]
                        .as_array()
                        .map(|a| a.iter().filter_map(|r| r["@id"].as_str()).collect())
                        .unwrap_or_default();
                    let ids2: Vec<&str> = a2[i]["ownedRelationship"]
                        .as_array()
                        .map(|a| a.iter().filter_map(|r| r["@id"].as_str()).collect())
                        .unwrap_or_default();
                    let by1: std::collections::HashMap<&str, &serde_json::Value> = a1
                        .iter()
                        .filter_map(|e| Some((e["@id"].as_str()?, e)))
                        .collect();
                    let by2: std::collections::HashMap<&str, &serde_json::Value> = a2
                        .iter()
                        .filter_map(|e| Some((e["@id"].as_str()?, e)))
                        .collect();
                    for (x, y) in ids1.iter().zip(ids2.iter()) {
                        if x != y {
                            println!("    child- {}", serde_json::to_string(by1[x]).unwrap());
                            println!("    child+ {}", serde_json::to_string(by2[y]).unwrap());
                            break;
                        }
                    }
                    shown = true;
                    break;
                }
            }
            if !shown {
                println!(
                    "== {} JSON-DIFF lengths {} vs {}",
                    f.display(),
                    a1.len(),
                    a2.len()
                );
            }
        }
    }
    println!("{ok} ok, {bad} failing");
}
