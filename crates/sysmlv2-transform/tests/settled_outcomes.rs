//! A session started from the outcomes a previous session settled on
//! answers as a session built cold does: the corpus's Vehicle example on
//! the prepared standard library, rebuilt after an edit to each of its
//! units in turn — a comment appended, which changes no outcome, and the
//! unit emptied, which unresolves every reference into it.

use std::path::{Path, PathBuf};
use sysmlv2_transform::{Library, Session};

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

/// The standard library prepared from the corpus, and the Vehicle example's
/// units; `None` when the corpus is not initialized.
fn fixture() -> Option<(Library, Vec<(String, String)>)> {
    let root = sysmlv2_testkit::workspace_root().join("spec-refs/SysML-v2-Release");
    let example: PathBuf = root.join("sysml/src/examples/Vehicle Example");
    if !example.exists() {
        eprintln!("corpus not initialized; skipping");
        return None;
    }
    let mut library = units_under(&root.join("sysml.library"));
    library.extend(sysmlv2_model::ambient::units());
    let library = Library::prepared_sources(library, None).unwrap();
    Some((library, units_under(&example)))
}

/// What a session answers: its full and compact interchange documents,
/// its findings and its unresolved references.
fn answers(session: &mut Session) -> String {
    let mut out = serde_json::to_string(&session.to_full_json()).unwrap();
    out.push('\n');
    out.push_str(&serde_json::to_string(&session.to_compact_json()).unwrap());
    for finding in session.check_findings() {
        out.push_str(&format!(
            "\n{:?} {:?} {}:{}:{} {}",
            finding.severity,
            finding.stage,
            finding.unit,
            finding.line,
            finding.col,
            finding.message
        ));
    }
    for unresolved in session.resolved().unresolved_references() {
        out.push_str(&format!("\n{unresolved:?}"));
    }
    out
}

#[test]
fn a_seeded_session_answers_as_a_cold_one_after_every_edit() {
    let Some((library, units)) = fixture() else {
        return;
    };
    assert!(units.len() >= 3, "the example has several units");
    let mut cold =
        Session::from_sources_with_library(units.clone(), Some(library.clone())).unwrap();
    let settled = cold
        .settled_outcomes()
        .expect("a cold build on the prepared library settles");
    assert_eq!(settled.unit_count(), units.len());
    // the same units again
    let mut same =
        Session::from_sources_settled(units.clone(), Some(library.clone()), Some(settled.clone()))
            .unwrap();
    assert_eq!(answers(&mut same), answers(&mut cold));
    assert!(same.settled_outcomes().is_some());
    for i in 0..units.len() {
        for edit in ["comment", "emptied"] {
            let mut edited = units.clone();
            match edit {
                "comment" => edited[i].1.push_str("\n// edited\n"),
                _ => edited[i].1 = "package Edited;".to_string(),
            }
            let mut cold =
                Session::from_sources_with_library(edited.clone(), Some(library.clone())).unwrap();
            // from the unedited build's outcomes
            let mut seeded = Session::from_sources_settled(
                edited.clone(),
                Some(library.clone()),
                Some(settled.clone()),
            )
            .unwrap();
            assert_eq!(
                answers(&mut seeded),
                answers(&mut cold),
                "unit {} {edit}",
                units[i].0
            );
            // and back from the edited build's
            let mut back = Session::from_sources_settled(
                units.clone(),
                Some(library.clone()),
                seeded.settled_outcomes(),
            )
            .unwrap();
            assert_eq!(
                answers(&mut back),
                answers(&mut same),
                "unit {} {edit}, back",
                units[i].0
            );
        }
    }
}
