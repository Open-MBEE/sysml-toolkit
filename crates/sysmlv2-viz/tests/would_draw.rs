//! `summary_would_draw_within` counts, without emitting it, what
//! `summary_would_draw` reads off the emitted document: on fixtures
//! with every option that adds or hides a node, and on a 28-unit model,
//! for several open sets and budgets — and stops once past its limit.

use sysmlv2_model::json::{ElementRef, ResolvedModel};
use sysmlv2_model::model::Model;
use sysmlv2_viz::{SummaryOptions, View, VizOptions};

/// Every node kind the tree draws: packages, definitions and usages,
/// owner cards nesting cards, enumerations in both spellings, an empty
/// package, metadata, notes on drawn and nested elements, imports, a
/// dependency, and typings and specializations into the library.
const FIXTURE: &str = "package P {
    private import ScalarValues::*;
    doc /* on P */
    metadata def Tag;
    package Q {
        part def A { @Tag; part a1; part a2 : A; attribute w : Real; }
        part def B :> A;
        part q : A { part q1 : Parts::Part; }
        comment about A /* c2 */
        comment about B /* c3 */
    }
    part def D :> Q::A { part d1 : Q::A; part d2 : Q::B; attribute mass : Real = 3; doc /* on D */ }
    part def L :> Parts::Part;
    part x : D;
    dependency Dep from D to L;
    enum def E { a; b; }
    enum e : E;
    package Empty;
    comment about L /* c1 */
    comment about x /* c4 */
}
package R { private import P::*; part r : P::L { part r1 : P::Q::A; } item i : Items::Item; }
";

/// KerML features: a leaf is a row, one nesting features a card.
const KERML: &str = "package K { classifier C { feature f { feature g; } feature h; } }";

fn with_library(units: &[(&str, &str)]) -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library loads");
    for (name, text) in units {
        let unit = model.add_source(name.to_string(), text);
        assert!(
            unit.diagnostics.is_empty(),
            "fixture must parse: {name}: {:?}",
            unit.diagnostics
        );
    }
    ResolvedModel::build(&model)
}

/// The count against the emitted document's total: exact up to any
/// limit at or above it, and stopped at any limit below it.
fn assert_counts(r: &mut ResolvedModel, root: Option<ElementRef>, opts: &VizOptions, label: &str) {
    let document = sysmlv2_viz::graph(r, root, opts).unwrap();
    let total = sysmlv2_viz::summary_would_draw(&document);
    let mut within = |limit| sysmlv2_viz::summary_would_draw_within(r, root, opts, limit).unwrap();
    assert_eq!(within(usize::MAX), Some(total), "{label}");
    assert_eq!(within(total), Some(total), "{label}");
    assert_eq!(within(total + 1), Some(total), "{label}");
    if total > 0 {
        assert_eq!(within(total - 1), None, "{label}");
        assert_eq!(within(total / 2), None, "{label}");
        assert_eq!(within(0), None, "{label}");
    }
}

/// The elements the full picture draws, in its order: the containers a
/// summary can open.
fn drawn(r: &mut ResolvedModel, root: Option<ElementRef>, opts: &VizOptions) -> Vec<ElementRef> {
    let mut full = opts.clone();
    full.summary = None;
    let g = sysmlv2_viz::graph(r, root, &full).unwrap();
    g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|n| n["kind"] != "note" && n.get("lib").is_none())
        .filter_map(|n| r.element_by_id(n["id"].as_str().unwrap()))
        .collect()
}

/// Summaries of one scope: closed, open at every drawn element, open at
/// every other one with some drawing all their members, and open at the
/// first few — each under generous, tight and zero budgets.
fn assert_summaries(
    r: &mut ResolvedModel,
    root: Option<ElementRef>,
    base: &VizOptions,
    label: &str,
) {
    let all = drawn(r, root, base);
    let alternate: Vec<ElementRef> = all.iter().copied().step_by(2).collect();
    let unbounded: Vec<ElementRef> = alternate.iter().copied().step_by(3).collect();
    let first: Vec<ElementRef> = all.iter().copied().take(4).collect();
    let open_sets = [
        ("closed", Vec::new(), Vec::new()),
        ("all open", all.clone(), Vec::new()),
        ("alternate", alternate, unbounded),
        ("first", first.clone(), first),
    ];
    for (name, open, unbounded) in open_sets {
        for (note_budget, leaf_budget) in [(200, 500), (1, 1), (0, 2), (usize::MAX, usize::MAX)] {
            let opts = base.clone().with_summary(Some(SummaryOptions {
                open: open.clone(),
                note_budget,
                leaf_budget,
                unbounded: unbounded.clone(),
            }));
            assert_counts(
                r,
                root,
                &opts,
                &format!("{label}, {name}, notes {note_budget}, leaves {leaf_budget}"),
            );
        }
    }
    assert_counts(r, root, base, &format!("{label}, full"));
}

#[test]
fn the_count_is_the_document_s_total_on_every_option() {
    let mut r = with_library(&[("a.sysml", FIXTURE), ("k.kerml", KERML)]);
    let bases = [
        ("defaults", VizOptions::default()),
        ("no notes", VizOptions::default().with_show_notes(false)),
        (
            "no metadata",
            VizOptions::default().with_show_metadata(false),
        ),
        (
            "library, imports, inherited",
            VizOptions::default()
                .with_show_lib(true)
                .with_show_imported(true)
                .with_show_inherited(true),
        ),
    ];
    for (label, base) in &bases {
        assert_summaries(&mut r, None, base, label);
    }
    // overlapping roots draw an element twice, and the scoped root
    let roots: Vec<ElementRef> = ["P", "P::Q", "R"]
        .iter()
        .map(|q| r.resolve_qualified(q).unwrap())
        .collect();
    let overlapping = VizOptions::default()
        .with_show_lib(true)
        .with_roots(Some(roots));
    assert_summaries(&mut r, None, &overlapping, "overlapping roots");
    let q = r.resolve_qualified("P::Q").unwrap();
    assert_summaries(&mut r, Some(q), &VizOptions::default(), "rooted at Q");
    // Library packages as roots: a library target hidden under one is
    // reached through it, not drawn on demand.
    for names in [["Parts", "P"], ["Items", "R"], ["ScalarValues", "P"]] {
        let roots: Vec<ElementRef> = names
            .iter()
            .map(|q| r.resolve_qualified(q).unwrap())
            .collect();
        let rooted = VizOptions::default()
            .with_show_lib(true)
            .with_roots(Some(roots));
        assert_summaries(&mut r, None, &rooted, &format!("rooted at {names:?}"));
    }
}

/// Two units with one name: their same-named packages share an id, and
/// so do the containers' counts in the document, the last recorded
/// standing for both nodes.
const SHARED_BIG: &str =
    "package P { part def A { part a1; part a2; part a3; part a4; } doc /* d */ }";
const SHARED_SMALL: &str = "package P { part def Z; part def Y; comment about Z /* z */ }";

#[test]
fn elements_sharing_an_id_count_as_the_document_keys_them() {
    for (big_first, units) in [
        (true, [SHARED_BIG, SHARED_SMALL]),
        (false, [SHARED_SMALL, SHARED_BIG]),
    ] {
        let mut model = Model::new();
        for text in units {
            let unit = model.add_source("a.sysml".to_string(), text);
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        }
        let mut r = ResolvedModel::build(&model);
        let opts = VizOptions::default().with_summary(Some(SummaryOptions {
            open: Vec::new(),
            note_budget: 5,
            leaf_budget: 20,
            unbounded: Vec::new(),
        }));
        let document = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
        let nodes = document["nodes"].as_array().unwrap();
        let ids: Vec<&str> = nodes
            .iter()
            .filter(|n| n["kind"] == "package")
            .map(|n| n["id"].as_str().unwrap())
            .collect();
        assert!(ids.len() == 2 && ids[0] == ids[1], "{ids:?}");
        let total = sysmlv2_viz::summary_would_draw(&document);
        // two packages and the doc on the first, each package carrying
        // what the last one hides: Z and Y, or A and its four parts
        assert_eq!(total, if big_first { 3 + 2 * 2 } else { 3 + 2 * 5 });
        let mut within =
            |limit| sysmlv2_viz::summary_would_draw_within(&mut r, None, &opts, limit).unwrap();
        assert_eq!(within(usize::MAX), Some(total), "big first: {big_first}");
        // The walk counts each package's own hidden elements, 3 + 5 + 2:
        // ahead of a smaller last one it passes the document's total and
        // stops, the early stop the function's doc describes.
        if big_first {
            assert_eq!(within(total), None);
            assert_eq!(within(9), None);
            assert_eq!(within(10), Some(total));
        } else {
            assert_eq!(within(total), Some(total));
            assert_eq!(within(total - 1), None);
        }
    }
}

#[test]
fn views_without_a_summary_count_their_nodes() {
    let mut r = with_library(&[("a.sysml", FIXTURE)]);
    for view in [View::Interconnection, View::State, View::Action] {
        let opts = VizOptions::default().with_view(view);
        assert_counts(&mut r, None, &opts, view.as_str());
    }
    let opts = VizOptions::default().with_view(View::Sequence);
    assert!(sysmlv2_viz::summary_would_draw_within(&mut r, None, &opts, usize::MAX).is_err());
}

#[test]
fn the_count_is_the_document_s_total_on_the_28_unit_model() {
    let Some(files) = sysmlv2_testkit::apollo_files() else {
        eprintln!("skipping: the 28-unit model's checkout is not initialized");
        return;
    };
    let root = sysmlv2_testkit::apollo_root().unwrap();
    let units: Vec<(String, String)> = files
        .iter()
        .map(|f| {
            (
                sysmlv2_testkit::relative_source_name(&root, f),
                std::fs::read_to_string(f).unwrap(),
            )
        })
        .collect();
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library loads");
    for (name, text) in &units {
        model.add_source(name.clone(), text);
    }
    let mut r = ResolvedModel::build(&model);
    let base = VizOptions::default().with_show_imported(true);
    let all = drawn(&mut r, None, &base);
    assert!(all.len() > 500, "{} drawn elements", all.len());
    let tops: Vec<ElementRef> = all
        .iter()
        .copied()
        .filter(|&e| r.owner(e).is_some_and(|o| r.owner(o).is_none()))
        .collect();
    let alternate: Vec<ElementRef> = all.iter().copied().step_by(2).collect();
    let open_sets = [
        ("closed", Vec::new()),
        ("tops", tops.clone()),
        ("alternate", alternate),
        ("all open", all.clone()),
    ];
    for (name, open) in open_sets {
        for (base_label, base) in [
            ("imports", base.clone()),
            ("library", base.clone().with_show_lib(true)),
            ("no notes", base.clone().with_show_notes(false)),
        ] {
            for (note_budget, leaf_budget) in [(200, 500), (2, 20)] {
                let opts = base.clone().with_summary(Some(SummaryOptions {
                    open: open.clone(),
                    note_budget,
                    leaf_budget,
                    unbounded: tops.iter().copied().take(2).collect(),
                }));
                let label =
                    format!("{name}, {base_label}, notes {note_budget}, leaves {leaf_budget}");
                assert_counts(&mut r, None, &opts, &label);
            }
        }
    }
    // one package's scope, opened at its root
    let scope = tops[0];
    let opts = base.clone().with_summary(Some(SummaryOptions {
        open: vec![scope],
        note_budget: 200,
        leaf_budget: 500,
        unbounded: Vec::new(),
    }));
    assert_counts(&mut r, Some(scope), &opts, "one package");
}

/// Members a body introduces in a role of their own (subjects, actors,
/// objectives, results, state actions, ends, …) and a port's directed
/// features are rows of their owners: the count, like the document,
/// neither draws nor hides them.
#[test]
fn role_members_count_as_the_rows_they_are() {
    let mut r = with_library(&[(
        "body_members.sysml",
        include_str!("fixtures/body_members.sysml"),
    )]);
    for (label, base) in [
        ("defaults", VizOptions::default()),
        (
            "library, inherited",
            VizOptions::default()
                .with_show_lib(true)
                .with_show_inherited(true),
        ),
    ] {
        assert_summaries(&mut r, None, &base, label);
    }
    // Closed at the package, the summary hides what the full picture
    // draws but its notes: no role member is among them.
    let full = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let cards = full["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|n| n["kind"] != "note")
        .count();
    let opts = VizOptions::default().with_summary(Some(SummaryOptions {
        open: Vec::new(),
        note_budget: 200,
        leaf_budget: 500,
        unbounded: Vec::new(),
    }));
    let closed = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    assert_eq!(sysmlv2_viz::summary_would_draw(&closed), cards);
    assert_eq!(
        sysmlv2_viz::summary_would_draw_within(&mut r, None, &opts, usize::MAX).unwrap(),
        Some(cards)
    );
}
