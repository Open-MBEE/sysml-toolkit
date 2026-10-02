//! A build on a prepared library assigns its rows the identities a joint
//! build assigns while tabling only its own rows: the frozen rows' ids are
//! read through the table their freeze kept and their names on demand.

use super::{ResolvedModel, id_index_tabled, library_names_built, prefix_ids_served};
use crate::model::Model;
use std::sync::Arc;
use uuid::Uuid;

const LIBRARY: &str = "package Lib { part def Base { attribute mass; } }";
/// An unnamed feature redefining a library feature, and one redefining
/// that: identity names reached through this build's rows and the frozen
/// ones alike.
const USER: &str = "package U { part def Car :> Lib::Base { attribute :>> mass; } part car : Car { attribute :>> mass = 1; } }";

/// The model built on the library prepared, or built together with it.
fn build(prepared: bool) -> ResolvedModel {
    let mut model = Model::new();
    if prepared {
        let mut base = Model::new();
        let parsed = base.add_library_source("lib.sysml", LIBRARY);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        base.prepare_library().unwrap().install(&mut model).unwrap();
    } else {
        model.add_library_source("lib.sysml", LIBRARY);
    }
    let parsed = model.add_source("user.sysml", USER);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let r = ResolvedModel::build(&model);
    assert_eq!(r.b.library_facts.is_some(), prepared);
    r
}

/// The user rows' ids, with the metaclass each row has.
fn user_ids(r: &ResolvedModel) -> Vec<(&'static str, Uuid)> {
    r.b.elements
        .iter()
        .skip(r.b.lib_boundary)
        .map(|e| (e.ty, e.id))
        .collect()
}

#[test]
fn a_build_on_a_prepared_library_assigns_the_ids_a_joint_build_assigns() {
    let served = prefix_ids_served();
    let mut prepared = build(true);
    assert_eq!(prefix_ids_served(), served + 1, "the kept table served");
    let mut joint = build(false);
    assert_eq!(
        prefix_ids_served(),
        served + 1,
        "a joint build tables every row"
    );
    assert_eq!(prepared.b.lib_boundary, joint.b.lib_boundary);
    assert_eq!(user_ids(&prepared), user_ids(&joint));

    // The identities are named through the library feature, not positional:
    // each redefining feature chains past its membership under its owner as
    // `::mass`, the name read from the frozen row.
    for r in [&mut prepared, &mut joint] {
        let car = r.resolve_qualified("U::car").unwrap().0;
        let mass = r.resolve_qualified("U::car::mass").unwrap().0;
        let def = r.resolve_qualified("U::Car").unwrap().0;
        let def_mass = r.resolve_qualified("U::Car::mass").unwrap().0;
        assert!(def_mass >= r.b.lib_boundary && mass >= r.b.lib_boundary);
        assert_eq!(
            r.b.elements[def_mass].id,
            Uuid::new_v5(&r.b.elements[def].id, b"::mass")
        );
        assert_eq!(
            r.b.elements[mass].id,
            Uuid::new_v5(&r.b.elements[car].id, b"::mass")
        );
    }
}

/// The element index tables only the build's own rows on a prepared
/// library, reading the frozen rows through the table their freeze kept,
/// and is kept across the lookup-cache resets between resolution passes.
#[test]
fn the_id_index_tables_only_a_prepared_builds_own_rows_once() {
    let mut r = build(true);
    let own = r.b.elements.len() - r.b.lib_boundary;
    let car = r.resolve_qualified("U::car").unwrap().0;
    let base = r.resolve_qualified("Lib::Base").unwrap().0;
    let (car_id, base_id) = (r.b.elements[car].id, r.b.elements[base].id);
    r.b.id_index = None;
    let tabled = id_index_tabled();
    assert_eq!(r.b.element_index_of_uuid(car_id), Some(car));
    assert_eq!(
        id_index_tabled() - tabled,
        own,
        "the build's own rows, once"
    );
    assert_eq!(
        r.b.element_index_of_uuid(base_id),
        Some(base),
        "a frozen row, through the kept table"
    );
    r.b.reset_lookup_caches();
    assert_eq!(r.b.element_index_of_uuid(car_id), Some(car));
    assert_eq!(
        id_index_tabled() - tabled,
        own,
        "kept across the lookup-cache reset"
    );

    // joint: every row, as before
    let mut r = build(false);
    let car = r.resolve_qualified("U::car").unwrap().0;
    let car_id = r.b.elements[car].id;
    r.b.id_index = None;
    let tabled = id_index_tabled();
    assert_eq!(r.b.element_index_of_uuid(car_id), Some(car));
    assert_eq!(id_index_tabled() - tabled, r.b.elements.len());
}

/// The library name tables by id are made once per prepared library and
/// shared by every build on it; a joint build makes its own.
#[test]
fn library_name_tables_are_made_once_per_prepared_library() {
    let mut base = Model::new();
    base.add_library_source("lib.sysml", LIBRARY);
    let library = base.prepare_library().unwrap();
    let before = library_names_built();
    for _ in 0..3 {
        let mut model = Model::new();
        Arc::clone(&library).install(&mut model).unwrap();
        model.add_source("user.sysml", USER);
        let r = ResolvedModel::build(&model);
        // read the shared cell as the identity assignment would
        let mut tables = r.b.identity_tables_for_test();
        assert!(tables.table_name(&r.b, Uuid::nil()).is_none());
    }
    assert_eq!(library_names_built() - before, 1, "made once, shared");
}

/// An identity override of a library row writes a frozen row in place:
/// the kept frozen table no longer serves, and the index tables every
/// row again, the new id found and the old one gone.
#[test]
fn an_overridden_library_id_retires_the_kept_table() {
    let mut r = build(true);
    let mass = r.resolve_qualified("Lib::Base::mass").unwrap();
    assert!(mass.0 < r.b.lib_boundary);
    let old = r.element_id(mass);
    let fresh = Uuid::from_u128(0x0f0f_0f0f_0f0f_4f0f_8f0f_0f0f_0f0f_0f0f);
    assert_eq!(
        r.override_ids(&std::collections::HashMap::from([(old, fresh)]))
            .len(),
        1
    );
    assert!(!r.b.elements.base_untouched(), "a frozen row written");
    let tabled = id_index_tabled();
    r.b.id_index = None;
    assert_eq!(r.b.element_index_of_uuid(fresh), Some(mass.0));
    assert_eq!(r.b.element_index_of_uuid(old), None);
    assert_eq!(
        id_index_tabled() - tabled,
        r.b.elements.len(),
        "every row tabled"
    );
}
