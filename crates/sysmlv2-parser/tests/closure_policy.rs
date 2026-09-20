//! The closure policy on the standard corpus (plan §33h): the full form
//! with the inheritance and import closures materialized per element
//! stays schema-shaped and a superset of the passthrough form, and its
//! size is measured — the number INTEROP.md's "passthrough level"
//! paragraph is about. The `Reject` unresolved-reference policy must not
//! count the library members a closure lists (they are ids, not
//! unresolved spellings).

#![cfg(feature = "json")]

use std::collections::{HashMap, HashSet};
use std::fs;
use sysmlv2_parser::full::{EmissionPolicy, UnresolvedReferencePolicy, resolved_to_full_json};
use sysmlv2_parser::json::{
    CLOSURE_NAMES, ClosurePolicy, Derives, ResolvedModel, derives, is_owned_property,
};
use sysmlv2_parser::model::Model;

/// The serialized size, without materializing the document: the corpus
/// full form runs to hundreds of megabytes and only the count is read.
struct CountingWriter(usize);

impl std::io::Write for CountingWriter {
    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
        self.0 += buf.len();
        Ok(buf.len())
    }

    fn flush(&mut self) -> std::io::Result<()> {
        Ok(())
    }
}

fn serialized_len(value: &serde_json::Value) -> usize {
    let mut counter = CountingWriter(0);
    serde_json::to_writer(&mut counter, value).unwrap();
    counter.0
}

/// Index an emitted array by element id, borrowing: the corpus full form
/// is hundreds of megabytes, and a copy per policy is gigabytes.
fn by_id(value: &serde_json::Value) -> HashMap<&str, &serde_json::Value> {
    value
        .as_array()
        .unwrap()
        .iter()
        .map(|e| (e["@id"].as_str().unwrap(), e))
        .collect()
}

/// A list of bare `{"@id": …}` references, or nothing if any entry
/// carries more than the id — then the values must be compared whole.
fn reference_ids(list: &[serde_json::Value]) -> Option<Vec<&str>> {
    list.iter()
        .map(|v| {
            let object = v.as_object()?;
            if object.len() != 1 {
                return None;
            }
            object.get("@id")?.as_str()
        })
        .collect()
}

/// Whether `whole` holds every value in `part`. Reference lists compare
/// by id through a set: the corpus lists are long enough that scanning
/// the longer one per entry dominates the test.
fn contains_all(part: &[serde_json::Value], whole: &[serde_json::Value]) -> bool {
    match (reference_ids(part), reference_ids(whole)) {
        (Some(part_ids), Some(whole_ids)) => {
            let whole_ids: HashSet<&str> = whole_ids.into_iter().collect();
            part_ids.iter().all(|id| whole_ids.contains(id))
        }
        _ => part.iter().all(|x| whole.contains(x)),
    }
}

#[test]
fn corpus_closure_form_is_a_superset_and_measured() {
    let root = sysmlv2_testkit::workspace_root().join("spec-refs/SysML-v2-Release");
    if !root.join("sysml.library").exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let files = sysmlv2_testkit::user_files();
    if files.is_empty() {
        eprintln!("skipping: corpus model files not present");
        return;
    }
    let mut model = Model::new();
    model
        .load_library_dir(&root.join("sysml.library"))
        .expect("library loads");
    for path in files {
        let src = fs::read_to_string(&path).unwrap();
        let name = path
            .strip_prefix(&root)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        model.add_source(name, &src);
    }
    let mut r = ResolvedModel::build(&model);
    let emit = |r: &mut ResolvedModel, closures: ClosurePolicy| {
        let t0 = std::time::Instant::now();
        let value = resolved_to_full_json(
            r,
            &model,
            EmissionPolicy {
                unresolved: UnresolvedReferencePolicy::Preserve,
                closures,
            },
        )
        .expect("the corpus emits under every policy");
        let bytes = serialized_len(&value);
        (value, bytes, t0.elapsed())
    };
    let (passthrough, pass_bytes, pass_time) = emit(&mut r, ClosurePolicy::Passthrough);
    let (explicit, explicit_bytes, explicit_time) = emit(
        &mut r,
        ClosurePolicy::Closure {
            include_implied: false,
        },
    );
    // Per element: the closure names are empty at the passthrough level
    // and the inheritance-aware lists grow into supersets. The lengths
    // the implied heritage is measured against outlive the two documents
    // they come from — a third corpus document alongside them is
    // gigabytes, so they are carried out and the documents dropped.
    let implied_floor: HashMap<String, [Option<usize>; 2]> = {
        let pass = by_id(&passthrough);
        let closed = by_id(&explicit);
        assert_eq!(pass.len(), closed.len());
        let mut closure_nonempty = 0usize;
        let mut feature_grew = 0usize;
        for (id, p) in &pass {
            let c = &closed[id];
            let ty = p["@type"].as_str().unwrap();
            for name in CLOSURE_NAMES {
                // `importedMembership` is owned on a MembershipImport: not a
                // closure there.
                if is_owned_property(ty, name) {
                    continue;
                }
                if let Some(v) = p.get(*name) {
                    assert!(
                        v.as_array().is_some_and(|a| a.is_empty()),
                        "{id}.{name} at passthrough"
                    );
                }
                if c.get(*name)
                    .and_then(|v| v.as_array())
                    .is_some_and(|a| !a.is_empty())
                {
                    closure_nonempty += 1;
                }
            }
            // An exact name is the same under both policies: an owned rule
            // routed through the policy by mistake would move here.
            for (key, value) in p.as_object().unwrap() {
                if key.starts_with('@') || CLOSURE_NAMES.contains(&key.as_str()) {
                    continue;
                }
                if derives(ty, key) == Derives::Exact {
                    assert_eq!(value, &c[key], "{id}.{key} moved under the closure policy");
                }
            }
            for name in ["feature", "featureMembership", "membership", "member"] {
                let (Some(a), Some(b)) = (
                    p.get(name).and_then(|v| v.as_array()),
                    c.get(name).and_then(|v| v.as_array()),
                ) else {
                    continue;
                };
                assert!(
                    b.len() >= a.len(),
                    "{id}.{name} shrank under the closure policy"
                );
                assert!(
                    contains_all(a, b),
                    "{id}.{name} lost a value under the closure policy"
                );
                if b.len() > a.len() {
                    feature_grew += 1;
                }
            }
        }
        eprintln!(
            "closure values written: {closure_nonempty}; inheritance-aware lists that grew: {feature_grew}"
        );
        assert!(closure_nonempty > 0);
        assert!(feature_grew > 0);
        closed
            .iter()
            .map(|(id, c)| {
                let len = |name: &str| c.get(name).and_then(|v| v.as_array()).map(Vec::len);
                ((*id).to_string(), [len("feature"), len("inheritedFeature")])
            })
            .collect()
    };
    drop(passthrough);
    drop(explicit);
    let (implied, implied_bytes, implied_time) = emit(
        &mut r,
        ClosurePolicy::Closure {
            include_implied: true,
        },
    );
    eprintln!(
        "full form: passthrough {pass_bytes} bytes ({pass_time:?}); closures over the written heritage {explicit_bytes} bytes ({explicit_time:?}, x{:.2}); with the implied heritage {implied_bytes} bytes ({implied_time:?}, x{:.2})",
        explicit_bytes as f64 / pass_bytes as f64,
        implied_bytes as f64 / pass_bytes as f64
    );
    // The implied heritage only adds.
    let more = by_id(&implied);
    for (id, floor) in &implied_floor {
        let m = more[id.as_str()];
        for (name, b) in ["feature", "inheritedFeature"].iter().zip(floor) {
            let (Some(b), Some(c2)) = (b, m.get(*name).and_then(|v| v.as_array())) else {
                continue;
            };
            assert!(
                c2.len() >= *b,
                "{id}.{name} shrank with the implied heritage"
            );
        }
    }
}

/// The `Reject` policy counts unresolved spellings, not the library ids
/// a closure lists.
#[test]
fn reject_policy_ignores_library_closure_members() {
    let root = sysmlv2_testkit::workspace_root().join("spec-refs/SysML-v2-Release");
    if !root.join("sysml.library").exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model
        .load_library_dir(&root.join("sysml.library"))
        .expect("library loads");
    model.add_source(
        "m.sysml",
        "package P { import ScalarValues::*; part def V; part v : V { attribute mass : Real; } }",
    );
    let mut r = ResolvedModel::build(&model);
    let value = resolved_to_full_json(
        &mut r,
        &model,
        EmissionPolicy {
            unresolved: UnresolvedReferencePolicy::Reject,
            closures: ClosurePolicy::Closure {
                include_implied: true,
            },
        },
    )
    .expect("library closure members are ids, not unresolved spellings");
    let v = value
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["declaredName"] == "v")
        .unwrap();
    // A part inherits the library `Parts::Part` members with the implied
    // heritage on.
    assert!(!v["inheritedFeature"].as_array().unwrap().is_empty());
}
