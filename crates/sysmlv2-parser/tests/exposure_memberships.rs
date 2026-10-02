//! Compatibility view exposures retain import operation order and identity.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};

fn models(library: &str, user: &str) -> Vec<(Model, ResolvedModel)> {
    let mut base = Model::new();
    base.add_library_source("views.sysml", library);
    assert!(!base.has_errors());
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(67).unwrap(), 67).unwrap());
    (0..4)
        .map(|mode| {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("views.sysml", library);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            m.add_source("view-use.sysml", user);
            assert!(!m.has_errors());
            let r = ResolvedModel::build(&m);
            (m, r)
        })
        .collect()
}

fn check(library: &str, user: &str, cases: &[(&str, &[&str])]) {
    for (mode, (model, mut resolved)) in models(library, user).into_iter().enumerate() {
        let loaded = model.loaded_library_unit_count();
        for _ in 0..2 {
            for &(view, expected) in cases {
                let view = resolved
                    .resolve_qualified(view)
                    .unwrap_or_else(|| panic!("missing view {view}, mode={mode}"));
                let names: Vec<_> = resolved
                    .view_exposed_elements(view)
                    .into_iter()
                    .map(|element| resolved.element_qualified_name(element).unwrap_or_else(|| panic!("unnamed element {element:?}, view={view:?}, mode={mode}, json={:?}", (resolved.element_type(element), resolved.element_properties(element)))))
                    .collect();
                assert_eq!(names, expected, "mode={mode}");
            }
        }
        assert_eq!(model.loaded_library_unit_count(), loaded);
        if mode == 3 {
            assert_eq!(loaded, 0);
        }
    }
}

#[test]
fn ordinary_imports_do_not_expose_and_mixed_expose_order_is_retained() {
    check(
        "package A {part a;} package B {part b;}",
        "view onlyB {import A::*; expose B::*;} view inOrder {expose A::*; expose B::b; expose A::a;}",
        &[("onlyB", &["B::b"]), ("inOrder", &["A::a", "B::b"])],
    );
}

#[test]
fn repeated_namespaces_keep_distinct_filter_and_recursive_paths() {
    check(
        "package A {part a; package N {part child;}}",
        "view paths {expose A::*[false]; expose A::*[true];}
         view deep {expose A::*[false]; expose A::**;}",
        &[
            ("paths", &["A::a", "A::N"]),
            ("deep", &["A", "A::a", "A::N", "A::N::child"]),
        ],
    );
}

#[test]
fn inherited_view_conditions_are_applied_but_private_conditions_do_not_inherit() {
    check(
        "package A {part a;} view def Reject {filter false;} view def Private {private filter false;}",
        "view rejected:Reject {expose A::*;} view admitted:Private {expose A::*;}",
        &[("rejected", &[]), ("admitted", &["A::a"])],
    );
}

#[test]
fn aliases_and_reexports_are_memberships_before_final_element_dedup() {
    check(
        "package B {part b;} package A {public import B::*; alias other for B::b;}",
        "view onlyA {expose A::*;} view v {expose A::*; expose B::b;}",
        &[("onlyA", &["B::b"]), ("v", &["B::b"])],
    );
}

#[test]
fn expose_ignores_visibility_but_filter_package_inner_import_keeps_its_policy() {
    check(
        "package A {private part hidden; part visible;}",
        "view allExposure {expose A::*;} view exact {expose A::hidden;} view wrapped {expose A::*[true];}",
        &[
            ("allExposure", &["A::hidden", "A::visible"]),
            ("exact", &["A::hidden"]),
            ("wrapped", &["A::visible"]),
        ],
    );
}

#[test]
fn recursive_import_cycles_terminate_without_losing_later_direct_exposures() {
    check(
        "package A {part a; public import B::*;} package B {part b; public import A::*;}",
        "view onlyA {expose A::*;} view v {expose A::*; expose B::b;}",
        &[("onlyA", &["A::a", "B::b"]), ("v", &["A::a", "B::b"])],
    );
}

#[test]
fn unknown_conditions_retain_compatibility_admission() {
    check(
        "package A {part a;}",
        "view v {expose A::*; filter missing;}",
        &[("v", &["A::a"])],
    );
}

#[test]
fn self_exposure_uses_an_empty_operation_exclusion_set() {
    check("", "view v {part a; expose v::*;}", &[("v", &["v::a"])]);
}

#[test]
fn imported_view_conditions_apply_including_private_imports() {
    check(
        "package A {part a;} package F {filter false;} view def RejectImported {public import F::*;}",
        "view rejected {import F::*; expose A::*;}
         view privateRejected {private import F::*; expose A::*;}
         view inherited:RejectImported {expose A::*;}",
        &[
            ("rejected", &[]),
            ("privateRejected", &[]),
            ("inherited", &[]),
        ],
    );
}

#[test]
fn exposed_type_inheritance_keeps_only_surviving_memberships() {
    check(
        "part def B {part x;} part def D :> B {part redefines x;} package P {public import all D::*;}",
        "view direct {expose D::*;} view indirect {expose P::*;}",
        &[("direct", &["D::x"]), ("indirect", &["D::x"])],
    );
}

#[test]
fn separate_exposes_preserve_distinct_same_named_elements() {
    check(
        "package A {part x;} package B {part x;}",
        "view v {expose A::*; expose B::*;}",
        &[("v", &["A::x", "B::x"])],
    );
}

#[test]
fn rejected_containers_do_not_block_matching_recursive_children() {
    check(
        "metadata def M; package A {package N {#M part child;}}",
        "view v {expose A::**; filter @M;}",
        &[("v", &["A::N::child"])],
    );
}

#[test]
fn inherited_back_imports_do_not_escape_current_namespace_exclusions() {
    check(
        "package P {package N {part child;} public import D::*;}
         part def C {public import P::**;} part def D :> C;",
        "view v {expose P::*;}",
        &[("v", &["P::N", "P"])],
    );
}

#[test]
fn import_all_preserves_private_members_admitted_by_inherited_imports() {
    check(
        "package P {private part hidden;}
         part def B {protected import all P::*;} part def D :> B;",
        "view v {expose D::*;} view wrapped {expose D::*[true];}",
        &[("v", &["P::hidden"]), ("wrapped", &[])],
    );
}

#[test]
fn qualified_metadata_attributes_require_the_cast_types_member_identity() {
    check(
        "metadata def Flag {attribute enabled; alias toggle for enabled;} metadata def Other {attribute enabled;}
         package Parts {part yes {@Flag {enabled=true;}} part no {@Flag {enabled=false;}}}",
        "view bare {expose Parts::*[@Flag and (as Flag).enabled];}
         view qualified {expose Parts::*[@Flag and (as Flag).$::Flag::enabled];}
         view aliased {expose Parts::*[@Flag and (as Flag).$::Flag::toggle];}
         view unrelated {expose Parts::*[@Flag and (as Flag).$::Other::enabled];}",
        &[
            ("bare", &["Parts::yes"]),
            ("qualified", &["Parts::yes"]),
            ("aliased", &["Parts::yes"]),
            // An unrelated declaration cannot select a same-named value.
            // Unknown conditions retain compatibility admission.
            ("unrelated", &["Parts::yes", "Parts::no"]),
        ],
    );
}

#[test]
fn ambiguous_metadata_attribute_values_remain_unknown() {
    check(
        "metadata def Flag {attribute enabled;}
         package Parts {part item1 {@Flag {enabled=false; enabled=true;}}}",
        "view bare {expose Parts::*[@Flag and (as Flag).enabled];}
         view qualified {expose Parts::*[@Flag and (as Flag).$::Flag::enabled];}",
        &[
            ("bare", &["Parts::item1"]),
            ("qualified", &["Parts::item1"]),
        ],
    );
}
