//! Context view, the system context diagram: the owned part usages of
//! a context as `rectangle` nodes, the most connected one in the centre
//! (`<<system>>`), and each two-ended connector between two different
//! parts as one edge labelled by its definition (else its name).
//!
//! Ports stay off the diagram: an end attaches to the part its feature
//! chain starts at, so `connect a.sub.p to b.q` joins `a` and `b`. The
//! centre's neighbours go up and down in turn: the other parts form one row
//! above and one row below the centre, where edges do not cross. The
//! stereotypes stay hidden; the bold border marks the centre.

use std::collections::{HashMap, HashSet};
use std::fmt::Write as _;

use sysmlv2_model::json::{ElementRef, ResolvedModel};

use crate::interconnect::CONNECTORS;
use crate::{
    VizOptions, escape, frame, inline_label, link_suffix, node_usage_label, stereo_text,
    style_header,
};

const DIRECTIONS: [&str; 2] = ["-up-", "-down-"];

const CENTRE_STYLE: &str = "hide stereotype
skinparam rectangle {
  BorderThickness<<system>> 2.5
  FontStyle<<system>> bold
}
";

/// The parts and connectors of a context: its own, then those of its
/// types (a usage's definitions, a definition's written generals) in
/// turn. A part that an earlier level already has by name, such as a
/// redefinition, keeps that level's node.
#[derive(Default)]
struct Found {
    parts: Vec<ElementRef>,
    index: HashMap<ElementRef, usize>,
    names: HashMap<String, usize>,
    connectors: Vec<ElementRef>,
    visited: HashSet<ElementRef>,
}

fn collect(r: &mut ResolvedModel, e: ElementRef, found: &mut Found) {
    if !found.visited.insert(e) || r.is_library_element(e) {
        return;
    }
    for m in r.owned_members(e) {
        let ty = r.element_type(m);
        if ty == "PartUsage" {
            let name = r.element_name(m).map(str::to_string);
            let known = name.as_ref().and_then(|n| found.names.get(n).copied());
            let i = known.unwrap_or_else(|| {
                found.parts.push(m);
                found.parts.len() - 1
            });
            found.index.insert(m, i);
            if let Some(n) = name {
                found.names.entry(n).or_insert(i);
            }
        } else if CONNECTORS.contains(&ty) {
            found.connectors.push(m);
        }
    }
    let mut generals = r.typings(e);
    generals.extend(r.explicit_supertypes(e));
    for g in generals {
        collect(r, g, found);
    }
}

pub(crate) fn emit(r: &mut ResolvedModel, tops: &[ElementRef], opts: &VizOptions) -> String {
    let mut found = Found::default();
    for &top in tops {
        collect(r, top, &mut found);
    }
    let Found {
        parts,
        index,
        connectors,
        ..
    } = found;
    let mut edges: Vec<(usize, usize, Option<String>)> = Vec::new();
    for c in connectors {
        let ends = r.connector_end_targets(c);
        if ends.len() != 2 {
            continue;
        }
        let at: Vec<Option<usize>> = ends
            .iter()
            .map(|end| {
                end.chain
                    .first()
                    .and_then(|first| index.get(first).copied())
            })
            .collect();
        let (Some(a), Some(b)) = (at[0], at[1]) else {
            continue;
        };
        if a == b {
            continue;
        }
        let label = r
            .typings(c)
            .into_iter()
            .find_map(|t| r.element_name(t).map(str::to_string))
            .or_else(|| r.element_name(c).map(str::to_string));
        edges.push((a, b, label));
    }

    let mut degree = vec![0usize; parts.len()];
    for (a, b, _) in &edges {
        degree[*a] += 1;
        degree[*b] += 1;
    }
    // The first declared part wins a tie: `max_by_key` keeps the last
    // maximum, so the search runs over the parts in reverse.
    let centre = (0..parts.len()).rev().max_by_key(|&i| degree[i]);

    let mut body = String::new();
    for (i, &p) in parts.iter().enumerate() {
        let label = node_usage_label(r, p);
        let mut stereos = stereo_text(r, opts, p, "part");
        if Some(i) == centre {
            stereos.push_str(" <<system>>");
        }
        let link = link_suffix(r, opts, p);
        let _ = writeln!(
            body,
            "rectangle \"{}\" as n{} {stereos}{link}",
            escape(&label),
            i + 1
        );
    }

    let mut lines = String::new();
    let mut side: HashMap<usize, &str> = HashMap::new();
    for (a, b, label) in edges {
        let suffix = label
            .map(|l| format!(" : {}", inline_label(&l)))
            .unwrap_or_default();
        let (from, arrow, to) = match centre {
            Some(c) if a == c || b == c => {
                let other = if a == c { b } else { a };
                let turn = side.len();
                let arrow = *side
                    .entry(other)
                    .or_insert(DIRECTIONS[turn % DIRECTIONS.len()]);
                (c, arrow, other)
            }
            _ => (a, "--", b),
        };
        let _ = writeln!(lines, "n{} {arrow} n{}{suffix}", from + 1, to + 1);
    }

    let mut header = style_header(opts, &["rectangle"]);
    header.push_str(CENTRE_STYLE);
    frame(opts, &header, &body, &lines)
}
