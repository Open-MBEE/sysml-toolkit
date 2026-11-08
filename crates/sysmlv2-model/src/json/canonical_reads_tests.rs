//! The checked reader answers under the canonical graph format what it
//! answers under the legacy one, before and after the model's implied
//! relationships are materialized (#61): a quantity attribute's `type`, the
//! `feature` list of a definition with an attribute of an unresolved type,
//! and its attributes' `isVariable`.

use super::{ClosurePolicy, ResolvedModel};
use crate::model::{GraphFormat, Model};
use std::path::Path;
use std::sync::Arc;

const LEVELS: &str = "package Levels {
    attribute def Status {
        attribute speed :> ISQ::speed;
    }
    attribute def Resolved {
        attribute code : ScalarValues::String;
        attribute color : ScalarValues::String;
    }
    attribute def Unresolved {
        attribute code : ScalarValues::String;
        attribute color : Missing;
    }
}";

const READS: [(&str, &str); 5] = [
    ("Levels::Status::speed", "type"),
    ("Levels::Resolved", "feature"),
    ("Levels::Resolved::code", "isVariable"),
    ("Levels::Unresolved", "feature"),
    ("Levels::Unresolved::code", "isVariable"),
];

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

fn levels(format: GraphFormat) -> Option<ResolvedModel> {
    let library = standard_library(format)?;
    let mut model = Model::with_graph_format(format);
    library.install(&mut model).unwrap();
    let parsed = model.add_source("levels.sysml", LEVELS);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    Some(r)
}

/// Each read's answer, an array by its length, a refusal by its message.
fn answers(r: &mut ResolvedModel) -> Vec<String> {
    READS
        .iter()
        .map(|(name, property)| {
            let e = r.resolve_qualified(name).unwrap();
            match r.property(e, property) {
                Ok(serde_json::Value::Array(items)) => {
                    format!("{name}.{property} = {} items", items.len())
                }
                Ok(value) => format!("{name}.{property} = {value}"),
                Err(error) => format!("{name}.{property} refused: {error}"),
            }
        })
        .collect()
}

#[test]
fn canonical_checked_reads_answer_as_legacy_before_and_after_materialization() {
    let Some(mut legacy) = levels(GraphFormat::LegacyV2) else {
        return;
    };
    let mut canonical = levels(GraphFormat::CanonicalV3).unwrap();
    let before = answers(&mut legacy);
    assert_eq!(answers(&mut canonical), before, "before materialization");
    assert!(
        before.iter().all(|answer| !answer.contains("refused")),
        "{before:?}"
    );
    for r in [&mut legacy, &mut canonical] {
        let root = r.user_elements().next().unwrap();
        let _ = r.property(root, "isImpliedIncluded");
        assert!(r.b.implied.is_some());
    }
    assert_eq!(answers(&mut legacy), before, "legacy after materialization");
    assert_eq!(
        answers(&mut canonical),
        before,
        "canonical after materialization"
    );
}
