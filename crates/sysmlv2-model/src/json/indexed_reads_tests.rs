//! Reads that answer from an index — the elements a membership owns, the
//! specialization index — answer what a scan of the whole table answers.

use super::ResolvedModel;
use crate::model::Model;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Calculations whose bodies run statements, reached through typing,
/// subclassification, redefinition and library specializations, beside
/// ones that do not.
const CALCULATIONS: &str = "package Calcs {
    private import ScalarValues::*;
    calc def Halve { in n : Real; attribute i : Real = n; assign i := i / 2; return result : Real = i; }
    calc def Quarter :> Halve;
    calc def Plain { in x : Real; return : Real = x + 1; }
    calc halve : Halve;
    calc quarter : Quarter;
    calc plain : Plain;
    part def Holder { calc h : Halve; calc p : Plain; }
    part holder : Holder { calc :>> h; calc :>> p; }
    requirement def Small { subject s : Holder; require constraint { true } }
    part ctx { requirement small : Small; satisfy small by holder; }
}";

/// Each owned element's owning relationship lists it, and each element
/// a relationship lists names that relationship as its owner.
fn assert_ownership_pairs(r: &ResolvedModel, label: &str) {
    for (i, row) in r.b.elements.iter().enumerate() {
        if let Some(rel) = row.owning_relationship {
            assert!(
                r.b.elements[rel].children.contains(&i),
                "{label}: row {i} names {rel} as its owner, which does not list it"
            );
        }
        for &child in &row.children {
            assert_eq!(
                r.b.elements[child].owning_relationship,
                Some(i),
                "{label}: row {i} lists {child}, which names another owner"
            );
        }
    }
}

/// [`ResolvedModel::members_under`] for every build element and every
/// membership metaclass it owns, against a scan of every row.
fn assert_members_like_a_scan(r: &ResolvedModel, label: &str) -> usize {
    let mut claimed: HashMap<usize, Vec<usize>> = HashMap::new();
    for (i, row) in r.b.elements.iter().enumerate() {
        if let Some(rel) = row.owning_relationship {
            claimed.entry(rel).or_default().push(i);
        }
    }
    let mut checked = 0;
    for e in r.b.lib_boundary..r.b.elements.len() {
        let kinds: HashSet<&'static str> = r.b.elements[e]
            .owned_relationships
            .iter()
            .map(|&rel| r.b.elements[rel].ty)
            .filter(|ty| ty.ends_with("Membership"))
            .collect();
        for kind in kinds {
            let mut scanned: Vec<usize> = r.b.elements[e]
                .owned_relationships
                .iter()
                .filter(|&&rel| r.b.elements[rel].ty == kind)
                .flat_map(|rel| claimed.get(rel).into_iter().flatten().copied())
                .collect();
            scanned.sort_unstable();
            scanned.dedup();
            assert_eq!(r.members_under(e, kind), scanned, "{label}: {kind} of {e}");
            checked += 1;
        }
    }
    checked
}

/// [`super::Builder::calculation_requires_execution`] through the index
/// for every element from `from` on, against reachability over every
/// table entry, whatever its kind. Answers how many elements require
/// execution.
fn assert_execution_like_the_table(r: &mut ResolvedModel, from: usize, label: &str) -> usize {
    let b = &mut r.b;
    let mut owners_of: HashMap<usize, Vec<usize>> = HashMap::new();
    for (i, &(owner, _, _, _)) in b.spec_targets.iter().enumerate() {
        if let Some(target) = b.spec_resolved.get(i).copied().flatten() {
            owners_of.entry(target).or_default().push(owner);
        }
    }
    let mut reaching: HashSet<usize> = b.executable_calculations.clone();
    let mut stack: Vec<usize> = reaching.iter().copied().collect();
    while let Some(target) = stack.pop() {
        for &owner in owners_of.get(&target).into_iter().flatten() {
            if reaching.insert(owner) {
                stack.push(owner);
            }
        }
    }
    for e in from..b.elements.len() {
        assert_eq!(
            b.indexed_calculation_requires_execution(e),
            reaching.contains(&e),
            "{label}: element {e}"
        );
    }
    assert!(
        b.executable_calculations.is_empty() || b.spec_index.is_some(),
        "{label}: a settled build reads the index"
    );
    reaching.len()
}

fn standard_library() -> Option<Arc<crate::prepared::PreparedLibrary>> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../spec-refs/SysML-v2-Release/sysml.library");
    if !path.exists() {
        return None;
    }
    let mut model = Model::new();
    model.load_library_dir(&path).unwrap();
    Some(model.prepare_library().unwrap())
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect(&path, out);
        } else if path.extension().is_some_and(|e| e == "sysml") {
            out.push(path);
        }
    }
}

/// Every directory of the corpus's example, training and validation
/// models as one workspace, the external corpus model when present, and
/// the calculations above, on the prepared standard library; every eighth
/// of them, the external model and the calculations again with the
/// implied relationships materialized (a whole-model pass, the sweep's
/// main cost).
#[test]
fn corpus_workspaces_read_owned_members_and_executing_calculations_like_a_scan() {
    let Some(library) = standard_library() else {
        return;
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../spec-refs");
    let mut workspaces: std::collections::BTreeMap<String, Vec<PathBuf>> = Default::default();
    let mut files = Vec::new();
    for dir in ["examples", "training", "validation"] {
        collect(
            &root.join("SysML-v2-Release/sysml/src").join(dir),
            &mut files,
        );
    }
    for file in files {
        let dir = file.parent().unwrap().display().to_string();
        workspaces.entry(dir).or_default().push(file);
    }
    let mut external = Vec::new();
    collect(&root.join("apollo-11-sysml-v2"), &mut external);
    if !external.is_empty() {
        workspaces.insert("external".into(), external);
    }
    let mut units: Vec<(String, Vec<(String, String)>)> = workspaces
        .into_iter()
        .map(|(label, mut files)| {
            files.sort();
            let texts = files
                .iter()
                .map(|file| {
                    (
                        file.file_name().unwrap().to_string_lossy().into_owned(),
                        std::fs::read_to_string(file).unwrap(),
                    )
                })
                .collect();
            (label, texts)
        })
        .collect();
    units.push((
        "calculations".into(),
        vec![("calcs.sysml".into(), CALCULATIONS.into())],
    ));
    let (mut members, mut executing, mut materialized) = (0, 0, 0);
    for (k, (label, texts)) in units.iter().enumerate() {
        let mut model = Model::new();
        Arc::clone(&library).install(&mut model).unwrap();
        for (name, text) in texts {
            model.add_source(name.clone(), text);
        }
        let mut r = ResolvedModel::build(&model);
        assert_ownership_pairs(&r, label);
        members += assert_members_like_a_scan(&r, label);
        // The library's rows are the same in every build: walk them once.
        let from = if k == 0 { 0 } else { r.b.lib_boundary };
        let reaching = assert_execution_like_the_table(&mut r, from, label);
        if label == "calculations" {
            // Halve, Quarter, halve, quarter, Holder::h, holder::h
            assert!(reaching >= 6, "{reaching} elements require execution");
        }
        executing += reaching;
        if k % 8 == 0 || label == "external" || label == "calculations" {
            r.ensure_implied();
            assert_ownership_pairs(&r, label);
            members += assert_members_like_a_scan(&r, label);
            materialized += 1;
        }
    }
    eprintln!(
        "{} workspaces ({materialized} materialized), {members} member reads, {executing} executing",
        units.len()
    );
    assert!(units.len() > 80, "{} workspaces", units.len());
    assert!(materialized > 10, "{materialized} materialized");
    assert!(members > 10_000, "{members} member reads");
    assert!(executing > 0);
}

/// A build still lowering may hold an index made from a partial table:
/// the walk scans instead, and the indexing variant leaves the index
/// unbuilt.
#[test]
fn an_unsettled_table_is_scanned() {
    let mut model = Model::new();
    let parsed = model.add_source(
        "calcs.sysml",
        "calc def Halve { in n; attribute i = n; assign i := i / 2; return result = i; }
         calc def Quarter :> Halve;
         calc quarter : Quarter;
         calc def Plain { in x; x + 1 }
         calc plain : Plain;",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut r = ResolvedModel::build(&model);
    let quarter = r.resolve_qualified("quarter").unwrap().0;
    let plain = r.resolve_qualified("plain").unwrap().0;
    r.b.semantic_ready = false;
    r.b.spec_index = None;
    assert!(r.b.indexed_calculation_requires_execution(quarter));
    assert!(r.b.spec_index.is_none());
    r.b.spec_index = Some(Default::default());
    assert!(r.b.calculation_requires_execution(quarter));
    assert!(!r.b.calculation_requires_execution(plain));
    r.b.semantic_ready = true;
    r.b.spec_index = None;
    assert!(r.b.indexed_calculation_requires_execution(quarter));
    assert!(!r.b.indexed_calculation_requires_execution(plain));
    assert!(r.b.spec_index.is_some());
}
