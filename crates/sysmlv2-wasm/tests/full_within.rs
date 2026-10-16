//! `toGraph`'s `summary.fullWithin` answers what a summary request
//! followed by a full request would draw: the full graph, byte for
//! byte, when the summary's would-draw total is within the budget, and
//! the summary, byte for byte, when it is not.
use std::path::{Path, PathBuf};

use serde_json::{Value, json};
use sysmlv2_wasm::{PreparedLibrary, Session};

fn sources(units: &[(String, String)]) -> String {
    serde_json::to_string(
        &units
            .iter()
            .map(|(name, text)| json!({"name": name, "text": text}))
            .collect::<Vec<_>>(),
    )
    .unwrap()
}

fn owned(units: &[(&str, &str)]) -> Vec<(String, String)> {
    units
        .iter()
        .map(|(name, text)| (name.to_string(), text.to_string()))
        .collect()
}

const SUMMARY_MODEL: &str = "package P { package Q { part def A; part def B :> A; part q : A; } part def D { part d1 : Q::A; } part def L; comment about L /* c */ }";

fn graph(s: &mut Session, opts: &Value) -> String {
    s.to_graph(Some(opts.to_string())).unwrap()
}

/// The full-within reply with its marker removed, re-serialized.
fn unmarked(reply: &str) -> String {
    let mut g: Value = serde_json::from_str(reply).unwrap();
    assert_eq!(g["full"], true, "the full graph is marked");
    g.as_object_mut().unwrap().remove("full");
    g.to_string()
}

/// `fullWithin` against the full graph and the summary on one scope:
/// the would-draw total of the summary, then the full graph at that
/// budget and above, and the summary just below it.
fn assert_full_within(s: &mut Session, base: &Value, summary: &Value, label: &str) {
    let full = graph(s, base);
    let mut request = base.clone();
    request["summary"] = summary.clone();
    let as_summary = graph(s, &request);
    let would_draw = sysmlv2_viz::summary_would_draw(&serde_json::from_str(&as_summary).unwrap());
    // the host's own arithmetic over the reply: nodes plus every hidden count
    let parsed: Value = serde_json::from_str(&as_summary).unwrap();
    let nodes = parsed["nodes"].as_array().unwrap();
    let by_hand = nodes.len()
        + nodes
            .iter()
            .map(|n| n["summary"]["hidden"].as_u64().unwrap_or(0) as usize)
            .sum::<usize>();
    assert_eq!(would_draw, by_hand, "{label}");
    for (within, is_full) in [
        (would_draw as f64, true),
        (would_draw as f64 + 0.5, true),
        (would_draw as f64 + 1000.0, true),
        (would_draw as f64 - 0.5, false),
        (would_draw as f64 - 1.0, false),
        (-1.0, false),
    ] {
        request["summary"]["fullWithin"] = json!(within);
        let reply = graph(s, &request);
        if is_full {
            assert_eq!(unmarked(&reply), full, "{label} within {within}");
            assert!(
                serde_json::from_str::<Value>(&reply)
                    .unwrap()
                    .get("summary")
                    .is_none()
            );
        } else {
            assert_eq!(reply, as_summary, "{label} within {within}");
        }
    }
}

#[test]
fn full_within_returns_the_full_graph_when_the_scope_fits() {
    let mut s = Session::from_sources(&sources(&owned(&[("p.sysml", SUMMARY_MODEL)]))).unwrap();
    let base = json!({"view": "tree", "showNotes": true});
    // closed, opened at the root, and with a leaf budget that truncates
    assert_full_within(&mut s, &base, &json!({"open": []}), "closed");
    assert_full_within(&mut s, &base, &json!({"open": ["P"]}), "open");
    assert_full_within(
        &mut s,
        &base,
        &json!({"open": ["P", "P::Q"], "leafBudget": 1, "noteBudget": 1}),
        "truncated",
    );
    assert_full_within(
        &mut s,
        &json!({"view": "tree", "roots": ["P"], "showNotes": false, "showImported": true}),
        &json!({"open": ["P"]}),
        "rooted",
    );
    // A view that exposes nothing is within any budget that is not negative.
    let mut s = Session::from_sources(&sources(&owned(&[(
        "v.sysml",
        "package V { part def A; view def E; view nothing : E; }",
    )])))
    .unwrap();
    let base = json!({"view": "tree", "element": "V::nothing"});
    let empty = graph(&mut s, &base);
    assert_eq!(
        serde_json::from_str::<Value>(&empty).unwrap()["nodes"],
        json!([])
    );
    let mut request = base.clone();
    request["summary"] = json!({"open": [], "fullWithin": 0});
    assert_eq!(unmarked(&graph(&mut s, &request)), empty);
    request["summary"]["fullWithin"] = json!(-1);
    let reply: Value = serde_json::from_str(&graph(&mut s, &request)).unwrap();
    assert!(reply["summary"].is_object() && reply.get("full").is_none());
    // A malformed budget is refused like any option.
    assert!(
        s.to_graph(Some(r#"{"summary":{"open":[],"fullWithin":"all"}}"#.into()))
            .unwrap_err()
            .contains("bad options")
    );
}

/// Two units with one name share their same-named elements' ids, and
/// the summary keys a container's counts by id: the last container
/// recorded under one stands for every node carrying it. A count that
/// walks the bigger one first passes the summary's total before its
/// end; the reply is still the one the two requests give.
#[test]
fn units_sharing_ids_answer_as_the_two_requests() {
    let big = "package P { part def A { part a1; part a2; part a3; part a4; } doc /* d */ }";
    let small = "package P { part def Z; part def Y; comment about Z /* z */ }";
    for (order, units) in [("big first", [big, small]), ("big last", [small, big])] {
        let units: Vec<(String, String)> = units
            .iter()
            .map(|text| ("a.sysml".to_string(), text.to_string()))
            .collect();
        let mut s = Session::from_sources(&sources(&units)).unwrap();
        let base = json!({"view": "tree", "showNotes": true});
        assert_full_within(&mut s, &base, &json!({"open": []}), order);
        assert_full_within(
            &mut s,
            &base,
            &json!({"open": ["P"], "leafBudget": 1, "noteBudget": 1}),
            order,
        );
    }
}

/// Every element kind the tree draws, notes on drawn and hidden
/// elements, an import, a dependency, an enumeration and an empty
/// package.
const PINNED_MODEL: &str = "package P { doc /* on P */ package Q { part def A; part def B :> A; part q : A; comment about A /* c2 */ } part def D :> Q::A { part d1 : Q::A; part d2 : Q::B; attribute mass = 3; } part def L; part x : D; dependency Dep from D to L; enum def E { a; b; } package Empty; comment about L /* c1 */ } package R { private import P::*; part r : L; }";

/// The replies' bytes are pinned: the full graph when the scope fits,
/// the summary with its selector lists when it does not, and both
/// answers for a view that exposes nothing.
#[test]
fn full_within_replies_keep_their_bytes() {
    let mut s = Session::from_sources(&sources(&owned(&[("p.sysml", PINNED_MODEL)]))).unwrap();
    let request = |within: f64| {
        json!({
            "view": "tree", "showNotes": true, "showImported": true,
            "summary": {
                "open": ["P", "P::D", "Nope"], "unbounded": ["P::D"],
                "leafBudget": 3, "noteBudget": 1, "fullWithin": within,
            },
        })
    };
    let fits = graph(&mut s, &request(1000.0));
    assert_eq!(
        fits,
        include_str!("golden/full-within-fits.json").trim_end()
    );
    let over = graph(&mut s, &request(4.0));
    assert_eq!(
        over,
        include_str!("golden/full-within-over.json").trim_end()
    );
    // the summary's own total sits between the two budgets
    let would_draw = sysmlv2_viz::summary_would_draw(&serde_json::from_str(&over).unwrap());
    assert!(4 < would_draw && would_draw <= 1000, "{would_draw}");
    let mut s = Session::from_sources(&sources(&owned(&[(
        "v.sysml",
        "package V { part def A; view def E; view nothing : E; }",
    )])))
    .unwrap();
    let mut request =
        json!({"view": "tree", "element": "V::nothing", "summary": {"open": [], "fullWithin": 0}});
    assert_eq!(
        graph(&mut s, &request),
        r#"{"edges":[],"full":true,"nodes":[],"view":"tree"}"#
    );
    request["summary"]["fullWithin"] = json!(-1);
    assert_eq!(
        graph(&mut s, &request),
        r#"{"edges":[],"nodes":[],"summary":{"resolved":[],"unresolved":[]},"view":"tree"}"#
    );
}

/// The corpus checkout's directory, `None` (with a note) when absent.
fn corpus_dir(relative: &str) -> Option<PathBuf> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("crates/sysmlv2-wasm sits two levels below the root")
        .join("spec-refs/SysML-v2-Release")
        .join(relative);
    if dir.is_dir() {
        Some(dir)
    } else {
        eprintln!("corpus not found at {}; skipping", dir.display());
        None
    }
}

fn units_under(dir: &Path) -> Vec<(String, String)> {
    let mut files = Vec::new();
    let mut stack = vec![dir.to_path_buf()];
    while let Some(dir) = stack.pop() {
        for entry in std::fs::read_dir(&dir).unwrap().flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("sysml" | "kerml")
            ) {
                files.push(path);
            }
        }
    }
    files.sort();
    files
        .into_iter()
        .map(|p| {
            let name = p.strip_prefix(dir).unwrap().display().to_string();
            (name, std::fs::read_to_string(&p).unwrap())
        })
        .collect()
}

#[test]
fn full_within_matches_the_two_requests_on_the_spec_examples() {
    let (Some(library), Some(examples)) = (
        corpus_dir("sysml.library"),
        corpus_dir("sysml/src/examples"),
    ) else {
        return;
    };
    let mut library = units_under(&library);
    library.extend(sysmlv2_model::ambient::units());
    let library = PreparedLibrary::new(&sources(&library), None).unwrap();
    let mut dirs: Vec<PathBuf> = std::fs::read_dir(&examples)
        .unwrap()
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.is_dir())
        .collect();
    dirs.sort();
    let mut drawn = 0;
    for dir in dirs {
        let label = dir.file_name().unwrap().to_string_lossy().to_string();
        let units = units_under(&dir);
        if units.is_empty() {
            continue;
        }
        let Ok(mut s) = Session::from_sources_with_prepared_library(&sources(&units), &library)
        else {
            eprintln!("{label}: does not build; skipped");
            continue;
        };
        // the whole model, closed and open at its roots
        let roots: Vec<String> = s
            .roots()
            .iter()
            .filter_map(|e| s.qualified_name(e).unwrap())
            .collect();
        let base = json!({"view": "tree", "showNotes": true});
        assert_full_within(&mut s, &base, &json!({"open": []}), &label);
        assert_full_within(
            &mut s,
            &base,
            &json!({"open": roots, "leafBudget": 20}),
            &label,
        );
        drawn += 1;
    }
    assert!(drawn >= 15, "only {drawn} example directories built");
}
