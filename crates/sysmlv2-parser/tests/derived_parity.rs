//! Parity between the derived-property read API and the full-form
//! emitter over the standard corpus: for every user element and every
//! name the read API computes, the API's answer must equal the value the
//! emitter writes for the same `@id`.
//!
//! The emitter now *projects* the layer for most computed names, so for
//! those the gate compares the layer with itself and the corpus baseline
//! (`full_baseline.rs`) is the real guard. It still compares independently
//! wherever the emitter keeps its own derivation — every unprojected
//! element (implied relationships, a lift failure, an id collision) and
//! the names the emitter deliberately retains (`name`, `qualifiedName`,
//! `featureTarget`, `annotatedElement` and its narrowings, `shortName`).
//! `ALLOWED` records the divergences those comparisons expose; a
//! divergence not listed there fails the gate with a per-(metaclass,
//! name) count and one example.

#![cfg(feature = "json")]

use serde_json::Value;
use std::collections::{BTreeMap, HashMap};
use std::fs;
use sysmlv2_parser::full::{EmissionPolicy, UnresolvedReferencePolicy, resolved_to_full_json};
use sysmlv2_parser::json::{
    CLOSURE_NAMES, ClosurePolicy, Derived, DerivedValue, Reference, ResolvedModel, computed_names,
    is_owned_property,
};
use sysmlv2_parser::model::Model;

/// Names on which the read API and the emitter are known to differ, with
/// the justification. An entry excuses a mismatch only when its predicate
/// over `(element, metaclass, api value, emitter value)` holds, so each
/// excuse is as narrow as the divergence it names.
type Excuse = fn(&Value, &str, &Value, &Value) -> bool;
const ALLOWED: &[(&str, &str, Excuse)] = &[
    // A required reference the layer cannot fill — an enumeration usage
    // whose definition did not resolve, an expression with no return
    // parameter, a transition whose source is no action, a reference
    // whose target is not of the required kind: the read API answers
    // null, the full form the catalog's self-reference placeholder. Only
    // the names whose specification can yield null are excused, so a
    // layer answering null where the element itself is the value
    // (`performedAction` of an unreferenced perform) is still caught.
    (
        "*",
        "required-reference placeholder: null in the API, self-reference on the wire",
        |el, _, api, emitter| api.is_null() && emitter.get("@id") == el.get("@id"),
    ),
];

/// The names the placeholder excuse applies to.
const MAY_BE_NULL: &[&str] = &[
    "assertedConstraint",
    "bodyAction",
    "enumerationDefinition",
    "eventOccurrence",
    "exhibitedState",
    "ifArgument",
    "instantiatedType",
    "loopVariable",
    "payloadArgument",
    "performedAction",
    "referencedConcern",
    "referencedConstraint",
    "referencedElement",
    "referencedRendering",
    "referent",
    "result",
    "satisfiedRequirement",
    "satisfyingFeature",
    "seqArgument",
    "source",
    "subjectParameter",
    "succession",
    "target",
    "thenAction",
    "useCaseIncluded",
    "verifiedRequirement",
    "whileArgument",
];

/// A reference as the wire spells it: an unresolved spelling becomes the
/// emitter's deterministic dangling id.
fn reference(r: &Reference, id: &dyn Fn(sysmlv2_parser::json::ElementRef) -> Value) -> Value {
    let wrap = |s: String| {
        Value::Object(
            [("@id".to_string(), Value::String(s))]
                .into_iter()
                .collect(),
        )
    };
    match r {
        Reference::Element(e) => id(*e),
        Reference::External(u) => wrap(u.to_string()),
        Reference::Unresolved(s) => wrap(
            uuid::Uuid::new_v5(
                &uuid::Uuid::NAMESPACE_OID,
                format!("unresolved:{s}").as_bytes(),
            )
            .to_string(),
        ),
        other => panic!("unhandled reference {other:?}"),
    }
}

fn to_json(r: &ResolvedModel, v: &DerivedValue) -> Value {
    let id = |e| {
        Value::Object(
            [(
                "@id".to_string(),
                Value::String(r.element_id(e).to_string()),
            )]
            .into_iter()
            .collect(),
        )
    };
    match v {
        DerivedValue::Null => Value::Null,
        DerivedValue::Bool(b) => Value::Bool(*b),
        DerivedValue::Str(s) => Value::String(s.clone()),
        DerivedValue::Element(e) => id(*e),
        DerivedValue::Elements(es) => Value::Array(es.iter().map(|&e| id(e)).collect()),
        DerivedValue::Reference(r) => reference(r, &id),
        DerivedValue::References(rs) => {
            Value::Array(rs.iter().map(|r| reference(r, &id)).collect())
        }
        DerivedValue::Strings(ss) => {
            Value::Array(ss.iter().map(|s| Value::String(s.clone())).collect())
        }
        // `DerivedValue` is non-exhaustive: a new variant must fail the
        // gate loudly rather than compare as something else.
        other => panic!("unhandled derived value {other:?}"),
    }
}

#[test]
fn corpus_read_api_matches_full_form() {
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
        // Unit names salt the root ids: two corpus files share a basename,
        // so name units by their corpus-relative path to keep ids unique.
        let name = path
            .strip_prefix(&root)
            .unwrap_or(&path)
            .to_string_lossy()
            .into_owned();
        model.add_source(name, &src);
    }
    // Without unresolved-reference recovery: the recovery annotations are
    // an emission policy, not model content, and would inflate
    // `ownedElement` on the referencing elements.
    let t0 = std::time::Instant::now();
    let full = sysmlv2_parser::full::model_to_full_json_with(&model, false);
    // The compact form: a key the full form writes that the compact form
    // already carries is an owned property, never a derived one.
    let compact = sysmlv2_parser::json::model_to_compact_json(&model);
    let owned_keys: HashMap<&str, &Value> = compact
        .as_array()
        .unwrap()
        .iter()
        .map(|el| (el["@id"].as_str().unwrap(), el))
        .collect();
    let emitted = t0.elapsed();
    let mut by_id: HashMap<&str, &Value> = HashMap::new();
    let mut duplicate_ids = 0usize;
    for el in full.as_array().unwrap() {
        if by_id.insert(el["@id"].as_str().unwrap(), el).is_some() {
            duplicate_ids += 1;
        }
    }
    let t0 = std::time::Instant::now();
    let mut r = ResolvedModel::build(&model);
    let built = t0.elapsed();
    // The four closure names are empty at the passthrough level by
    // design; the read API answers them (over the written heritage
    // under its default policy), so they are compared against an
    // emission under the closure policy.
    let closed = resolved_to_full_json(
        &mut r,
        &model,
        EmissionPolicy {
            unresolved: UnresolvedReferencePolicy::LegacyDanglingId,
            closures: ClosurePolicy::Closure {
                include_implied: false,
            },
        },
    )
    .expect("the corpus emits under the closure policy");
    let closed_by_id: HashMap<&str, &Value> = closed
        .as_array()
        .unwrap()
        .iter()
        .map(|el| (el["@id"].as_str().unwrap(), el))
        .collect();
    let names: Vec<&str> = computed_names().collect();
    let type_of = |v: &Value| -> String {
        v.get("@id")
            .and_then(Value::as_str)
            .and_then(|id| by_id.get(id))
            .map(|el| el["@type"].as_str().unwrap_or("?").to_string())
            .unwrap_or_else(|| "?".into())
    };

    // (metaclass, name) -> (mismatches, compared, first example)
    let mut report: BTreeMap<(String, String), (usize, usize, String)> = BTreeMap::new();
    let mut missing_elements = 0usize;
    let mut skipped_duplicates = 0usize;
    let mut per_name: BTreeMap<&str, std::time::Duration> = BTreeMap::new();
    let elements: Vec<_> = r.user_elements().collect();
    // Ids that occur more than once in the payload cannot be matched to a
    // model element (an id-scheme collision between same-named units).
    let mut seen_ids: HashMap<String, usize> = HashMap::new();
    for e in &elements {
        *seen_ids.entry(r.element_id(*e).to_string()).or_default() += 1;
    }
    for e in elements {
        let id = r.element_id(e).to_string();
        if seen_ids[&id] > 1 {
            skipped_duplicates += 1;
            continue;
        }
        let Some(el) = by_id.get(id.as_str()) else {
            missing_elements += 1;
            continue;
        };
        let ty = r.element_type(e).to_string();
        for &name in &names {
            let el = if CLOSURE_NAMES.contains(&name) {
                closed_by_id.get(id.as_str()).copied().unwrap_or(el)
            } else {
                *el
            };
            let t0 = std::time::Instant::now();
            let d = r.derived(e, name);
            *per_name.entry(name).or_default() += t0.elapsed();
            let entry =
                report
                    .entry((ty.clone(), name.to_string()))
                    .or_insert((0, 0, String::new()));
            let Derived::Value(v) = d else {
                // The emitter writing a key the read API calls undeclared
                // is a catalog / derived-name table regression — unless the
                // compact form spells the property, or it is one of the
                // three owned properties the emitter completes from what the
                // compact form spells (a relationship's `source`/`target`
                // from its ends, a ConjugatedPortTyping's
                // `conjugatedPortDefinition` from its `type`).
                let owned_here = owned_keys
                    .get(id.as_str())
                    .is_some_and(|c| c.get(name).is_some())
                    || (matches!(name, "source" | "target" | "conjugatedPortDefinition")
                        && is_owned_property(&ty, name));
                if el.get(name).is_some() && !owned_here && matches!(d, Derived::NotDeclared) {
                    entry.1 += 1;
                    entry.0 += 1;
                    if entry.2.is_empty() {
                        entry.2 = format!("{id}: api=NotDeclared, emitter writes the key");
                    }
                }
                continue;
            };
            let got = to_json(&r, &v);
            entry.1 += 1;
            let Some(expected) = el.get(name).cloned() else {
                // A value the emitter never writes cannot silently equal
                // an API `Null`.
                entry.0 += 1;
                if entry.2.is_empty() {
                    entry.2 = format!("{id}: api={got}, emitter does not write the key");
                }
                continue;
            };
            if got != expected {
                if ALLOWED.iter().any(|(n, _, pred)| {
                    (*n == name || (*n == "*" && MAY_BE_NULL.contains(&name)))
                        && pred(el, &ty, &got, &expected)
                }) {
                    continue;
                }
                entry.0 += 1;
                if entry.2.is_empty() {
                    entry.2 = format!(
                        "{id}: api={got} emitter={expected} (emitter value type: {})",
                        type_of(&expected)
                    );
                }
            }
        }
    }
    assert_eq!(missing_elements, 0, "every user element is emitted");
    eprintln!(
        "emit {emitted:?}, build {built:?}; {duplicate_ids} duplicate payload ids, {skipped_duplicates} model elements skipped for them"
    );
    let mut slow: Vec<(&str, std::time::Duration)> = per_name.into_iter().collect();
    slow.sort_by_key(|(_, d)| std::cmp::Reverse(*d));
    eprintln!(
        "read-API time by name (top 6): {:?}",
        slow.iter().take(6).collect::<Vec<_>>()
    );
    let bad: Vec<String> = report
        .iter()
        .filter(|(_, (m, _, _))| *m > 0)
        .map(|((ty, name), (m, n, ex))| format!("  {ty}.{name}: {m}/{n} differ, e.g. {ex}"))
        .collect();
    let compared: usize = report.values().map(|(_, n, _)| n).sum();
    eprintln!(
        "compared {compared} (element, name) values over {} (metaclass, name) pairs",
        report.len()
    );
    assert!(
        bad.is_empty(),
        "read API and full-form emitter disagree on {} (metaclass, name) pairs:\n{}",
        bad.len(),
        bad.join("\n")
    );
}
