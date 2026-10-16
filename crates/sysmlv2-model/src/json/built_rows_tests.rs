//! A resolved model reads its compact emission, its unit structure and its
//! library name tables off what its build made while nothing has been
//! written since, and those reads are what a fresh build of the same model
//! makes; once a row is written they read nothing, and the answers are made
//! from a fresh build again.

use super::{ElementRef, ResolvedModel, library_name_map, model_to_compact_json_with_units};
use crate::model::{GraphFormat, Model};
use std::collections::HashMap;

const LIBRARY: &str = "standard library package Lib { metadata def Mark; \
     part def Base { attribute mass; part wheel[4]; } }";
/// Unnamed features redefining library features, a metadata usage and an
/// annotation about a library element: identities and names that reach
/// through to the library's rows.
const USER: &str = "package U { private import Lib::*; \
     part def Car :> Base { attribute :>> mass; part :>> wheel; } \
     part car : Car { attribute :>> mass = 1; } \
     @Mark about Base; }";
const OTHER: &str = "package V { part truck : U::Car; }";

/// The two user units on the library, prepared or built together with them.
fn model(prepared: bool, format: GraphFormat) -> Model {
    let mut model = Model::with_graph_format(format);
    if prepared {
        let mut base = Model::with_graph_format(format);
        let parsed = base.add_library_source("lib.sysml", LIBRARY);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        base.prepare_library().unwrap().install(&mut model).unwrap();
    } else {
        model.add_library_source("lib.sysml", LIBRARY);
    }
    for (name, text) in [("u.sysml", USER), ("v.sysml", OTHER)] {
        let parsed = model.add_source(name, text);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    }
    model
}

/// The library name entries read off the model's own tables, collected as
/// [`library_name_map`] collects them.
fn built_names(r: &ResolvedModel) -> Option<HashMap<String, Vec<String>>> {
    Some(
        r.built_library_names()?
            .map(|(id, segments)| (id.to_string(), segments.to_vec()))
            .collect(),
    )
}

#[test]
fn the_built_rows_read_as_a_fresh_build_emits() {
    for prepared in [true, false] {
        let model = model(prepared, GraphFormat::LegacyV2);
        let r = ResolvedModel::build(&model);
        let fresh = model_to_compact_json_with_units(&model);
        assert_eq!(fresh.1.len(), 2, "both user units are laid out");
        assert!(r.emits_built_rows());
        assert_eq!(r.built_compact_json_with_units(), Some(fresh.clone()));
        assert_eq!(r.built_unit_structure(), Some(fresh.1.clone()));
        // The checks and the reads that complete the model fill memos and
        // may append implied relationships; the rows the build made stay as
        // they were.
        let mut r = r;
        let _ = crate::check::validate_model_with(&mut r, &model);
        let _ = crate::check::validate_semantics_with(&mut r, &model);
        let _ = r.to_full_json_strict();
        for i in r.built.as_ref().unwrap().user.clone() {
            let _ = r.implied_relationships(ElementRef(i));
        }
        assert_eq!(r.built_compact_json_with_units(), Some(fresh.clone()));
        // A row appended past them is not read.
        let appended = r.b.elements[0].clone();
        r.b.elements.push(appended);
        assert_eq!(r.built_compact_json_with_units(), Some(fresh));

        let full = library_name_map(&model);
        assert!(!full.is_empty());
        assert_eq!(built_names(&r), Some(full));
    }
}

#[test]
fn a_written_row_sends_the_reads_back_to_a_fresh_build() {
    let model = model(true, GraphFormat::LegacyV2);
    let mut r = ResolvedModel::build(&model);
    let user = r.built.as_ref().unwrap().user.clone();
    assert!(r.built_compact_json_with_units().is_some());
    // Any write, even one that leaves the row as it was, retires the read.
    let row = &mut r.b.elements[user.start];
    row.set_ty(row.ty);
    assert!(!r.emits_built_rows());
    assert_eq!(r.built_compact_json_with_units(), None);
    assert_eq!(r.built_unit_structure(), None);
    // The name tables are held apart from the rows.
    assert!(built_names(&r).is_some());
    let entry = &mut r.b.lib_qnames[0];
    entry.1 = entry.1.clone();
    assert_eq!(built_names(&r), None);
}

#[test]
fn a_build_whose_emission_completes_rows_reads_only_its_units_and_names() {
    let model = model(true, GraphFormat::CanonicalV3);
    let r = ResolvedModel::build(&model);
    assert!(!r.emits_built_rows());
    assert_eq!(r.built_compact_json_with_units(), None);
    assert_eq!(
        r.built_unit_structure(),
        Some(model_to_compact_json_with_units(&model).1)
    );
    assert_eq!(built_names(&r), Some(library_name_map(&model)));
}
