//! The derived names a feature-reference expression answers without the
//! implied relationships — its names and the chain of its owners — read on
//! a freshly built model leave them unmade and answer as on a model where
//! they were made first; a later read of another name makes them first, as
//! a read of the expression always did.

use super::derived::{NAMES_AND_OWNERS, derives};
use super::{Builder, ClosurePolicy, Derived, DerivedValue, Derives, ElementRef, ResolvedModel};
use crate::model::{GraphFormat, Model};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// A reference expression held as a value, and one held as a trigger's
/// argument: the value of the trigger invocation's parameter.
const REFERENCES: &str = "package P {
    attribute n;
    attribute v = n;
    state def S {
        attribute deadline;
        entry; then a;
        state a;
        state b;
        transition first a accept at deadline then b;
    }
}";

/// The answers to every name of [`NAMES_AND_OWNERS`] the element's
/// metaclass computes.
fn names_and_owners(r: &mut ResolvedModel, e: ElementRef) -> Vec<(&'static str, Derived)> {
    let ty = r.element_type(e);
    NAMES_AND_OWNERS
        .iter()
        .copied()
        .filter(|name| matches!(derives(ty, name), Derives::Exact | Derives::Passthrough))
        .map(|name| (name, r.derived(e, name)))
        .collect()
}

fn reference_expressions(r: &ResolvedModel) -> Vec<ElementRef> {
    r.user_elements()
        .filter(|&e| r.element_type(e) == "FeatureReferenceExpression")
        .collect()
}

/// Two models of one build: one fresh, one whose implied relationships are
/// made before any read.
fn fresh_and_made(model: &Model) -> (ResolvedModel, ResolvedModel) {
    let mut b = Builder::default();
    b.build_model(model);
    let mut made = ResolvedModel::from_builder(b.clone(), model);
    made.ensure_implied();
    (ResolvedModel::from_builder(b, model), made)
}

#[test]
fn a_reference_expressions_names_and_owners_defer_the_implied_relationships() {
    let mut model = Model::new();
    let parsed = model.add_source("references.sysml", REFERENCES);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (mut r, mut made) = fresh_and_made(&model);
    let expressions = reference_expressions(&r);
    let held_by: Vec<&str> = expressions
        .iter()
        .map(|&e| r.b.elements[r.b.elements[e.0].owning_relationship.unwrap()].ty)
        .collect();
    assert_eq!(held_by, ["FeatureValue", "FeatureValue"]);
    let v = r.resolve_qualified("P::v").unwrap();
    for &e in &expressions {
        let before = names_and_owners(&mut r, e);
        assert_eq!(before.len(), NAMES_AND_OWNERS.len());
        assert_eq!(before, names_and_owners(&mut made, e));
    }
    assert!(r.b.implied.is_none(), "a name or owner read made them");
    let value = names_and_owners(&mut r, expressions[0]);
    let answer = |name: &str| &value.iter().find(|(n, _)| *n == name).unwrap().1;
    assert_eq!(answer("name"), &Derived::Value(DerivedValue::Null));
    assert_eq!(answer("owner"), &Derived::Value(DerivedValue::Element(v)));
    assert_eq!(answer("owningNamespace"), answer("owner"));
    // The names of other elements leave them unmade too; a read of another
    // name, here of the attribute, makes them first.
    assert_eq!(names_and_owners(&mut r, v), names_and_owners(&mut made, v));
    assert!(r.b.implied.is_none());
    assert_eq!(r.derived(v, "ownedMember"), made.derived(v, "ownedMember"));
    assert!(r.b.implied.is_some(), "the deferred demand was not met");

    // Without a reference expression read first, that read leaves them
    // unmade, as it always did.
    let (mut fresh, _) = fresh_and_made(&model);
    let _ = fresh.derived(v, "ownedMember");
    assert!(fresh.b.implied.is_none());

    // What the expression owns comes with its generated result.
    let (mut fresh, _) = fresh_and_made(&model);
    let Derived::Value(DerivedValue::Element(result)) = fresh.derived(expressions[0], "result")
    else {
        panic!("the value's reference expression has a result");
    };
    assert!(fresh.b.implied.is_some());
    assert!(result.0 >= fresh.b.explicit_len(), "a generated result");
}

/// The operations that act on the implied relationships differently once
/// they exist — the library name table, explicit ids, the binding of
/// id-spelled references — meet a deferred demand first, and leave them
/// unmade when nothing deferred one.
#[test]
fn operations_on_the_implied_relationships_meet_a_deferred_demand_first() {
    let mut model = Model::new();
    let parsed = model.add_source("references.sysml", REFERENCES);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let operate = |r: &mut ResolvedModel, operation: usize| {
        let n = r.resolve_qualified("P::n").unwrap();
        match operation {
            0 => r.set_library_names(&HashMap::new()),
            1 => {
                let renamed = HashMap::from([(r.element_id(n), uuid::Uuid::from_u128(7))]);
                assert_eq!(r.override_ids(&renamed).len(), 1);
            }
            _ => {
                let _ = r.bind_id_spelled_references();
            }
        }
    };
    for operation in 0..3 {
        let (mut r, _) = fresh_and_made(&model);
        let _ = r.derived(reference_expressions(&r)[0], "name");
        assert!(r.b.implied.is_none());
        operate(&mut r, operation);
        assert!(r.b.implied.is_some(), "operation {operation}");
        let (mut fresh, _) = fresh_and_made(&model);
        operate(&mut fresh, operation);
        assert!(fresh.b.implied.is_none(), "operation {operation}");
    }
}

fn standard_library(format: GraphFormat) -> Option<Arc<crate::prepared::PreparedLibrary>> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../spec-refs/SysML-v2-Release/sysml.library");
    if !path.exists() {
        return None;
    }
    let mut model = Model::with_graph_format(format);
    model.load_library_dir(&path).unwrap();
    Some(model.prepare_library().unwrap())
}

/// Under the canonical graph format a constructor's result owns the
/// bindings of the defaults its arguments leave, which the implied
/// relationships generate: a read of the result's members after a names
/// walk answers as on a model where they were made first, as it did when
/// the walk's first reference expression made them.
#[test]
fn a_read_after_a_names_walk_answers_as_if_the_walk_had_made_them() {
    let Some(library) = standard_library(GraphFormat::CanonicalV3) else {
        return;
    };
    let mut model = Model::with_graph_format(GraphFormat::CanonicalV3);
    Arc::clone(&library).install(&mut model).unwrap();
    let parsed = model.add_source(
        "constructed.sysml",
        "package P {
            private import ScalarValues::*;
            attribute n : Integer;
            part def Q { attribute k : Integer; }
            attribute z = new Q(k = n);
        }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let (mut r, mut made) = fresh_and_made(&model);
    let users: Vec<ElementRef> = r.user_elements().collect();
    for &e in &users {
        assert_eq!(names_and_owners(&mut r, e), names_and_owners(&mut made, e));
    }
    assert!(r.b.implied.is_none(), "a name or owner read made them");
    let constructor = users
        .iter()
        .copied()
        .find(|&e| r.element_type(e) == "ConstructorExpression")
        .unwrap();
    let result = r.b.elements[constructor.0]
        .owned_relationships
        .iter()
        .find(|&&m| r.b.elements[m].ty == "ReturnParameterMembership")
        .map(|&m| ElementRef(r.b.elements[m].children[0]))
        .unwrap();
    let members = made.derived(result, "ownedMember");
    let Derived::Value(DerivedValue::Elements(listed)) = &members else {
        panic!("{members:?}");
    };
    assert!(
        listed.iter().any(|m| m.0 >= made.b.explicit_len()),
        "the result owns generated default bindings: {listed:?}"
    );
    assert_eq!(r.derived(result, "ownedMember"), members);
}

/// The checked reads meet a deferred demand too: under the closure policy
/// with the implied heritage an accept action's `mayTimeVary` reads the
/// implied specializations without making them, and after a walk over the
/// reference expressions' names answers as on a model where they were made
/// first.
#[test]
fn checked_reads_after_a_names_walk_answer_as_if_the_walk_had_made_them() {
    let Some(library) = standard_library(GraphFormat::LegacyV2) else {
        return;
    };
    let mut model = Model::new();
    Arc::clone(&library).install(&mut model).unwrap();
    let parsed = model.add_source("references.sysml", REFERENCES);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let policy = ClosurePolicy::Closure {
        include_implied: true,
    };
    let accept = |r: &ResolvedModel| {
        r.user_elements()
            .find(|&e| r.element_type(e) == "AcceptActionUsage")
            .unwrap()
    };
    let walked = |model: &Model| {
        let (mut r, mut made) = fresh_and_made(model);
        r.set_closure_policy(policy);
        made.set_closure_policy(policy);
        for e in reference_expressions(&r) {
            let _ = names_and_owners(&mut r, e);
        }
        assert!(r.b.implied.is_none());
        (r, made)
    };
    let (mut r, mut made) = walked(&model);
    let e = accept(&r);
    let expected = made.property(e, "mayTimeVary");
    assert_eq!(expected, Ok(serde_json::json!(false)));
    assert_eq!(r.property(e, "mayTimeVary"), expected);
    assert!(r.b.implied.is_some());
    let (mut r, mut made) = walked(&model);
    assert_eq!(
        r.derived_exact(e, "mayTimeVary"),
        made.derived_exact(e, "mayTimeVary")
    );
    // An owned property read from the row meets no demand.
    let (mut r, _) = walked(&model);
    let _ = r.property(reference_expressions(&r)[1], "owningRelationship");
    assert!(r.b.implied.is_none());
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
/// models as one workspace and the external corpus model when present, on
/// the prepared standard library: the names and owners of every element of
/// the build (the library's own in the first workspace) leave the implied
/// relationships unmade; in every fourth workspace and the external model
/// they equal the answers of the same build whose implied relationships
/// were made first.
#[test]
fn corpus_names_and_owners_read_alike_before_the_implied_relationships() {
    let Some(library) = standard_library(GraphFormat::LegacyV2) else {
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
    let (mut compared, mut answers, mut expressions) = (0, 0, 0);
    for (k, (label, mut files)) in workspaces.into_iter().enumerate() {
        files.sort();
        let mut model = Model::new();
        Arc::clone(&library).install(&mut model).unwrap();
        for file in &files {
            let text = std::fs::read_to_string(file).unwrap();
            model.add_source(
                file.file_name().unwrap().to_string_lossy().into_owned(),
                &text,
            );
        }
        let compare = k % 4 == 0 || label == "external";
        let (mut r, mut made) = if compare {
            let (r, made) = fresh_and_made(&model);
            (r, Some(made))
        } else {
            (ResolvedModel::build(&model), None)
        };
        // The library's rows are the same in every build: read them once.
        let from = if k == 0 { 0 } else { r.b.lib_boundary };
        for e in (from..r.b.explicit_len()).map(ElementRef) {
            let before = names_and_owners(&mut r, e);
            answers += before.len();
            if let Some(made) = &mut made {
                assert_eq!(
                    before,
                    names_and_owners(made, e),
                    "{label}: element {}",
                    e.0
                );
            }
        }
        assert!(
            r.b.implied.is_none(),
            "{label}: a name or owner read made them"
        );
        compared += usize::from(compare);
        expressions += reference_expressions(&r).len();
    }
    eprintln!(
        "{answers} answers ({compared} workspaces compared), {expressions} reference expressions"
    );
    assert!(compared > 20, "{compared} workspaces compared");
    assert!(expressions > 1_000, "{expressions} reference expressions");
}
