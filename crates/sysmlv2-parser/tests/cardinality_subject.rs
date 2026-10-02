//! Subject parameters preserve inherited subject identity through intermediate types.
#![cfg(feature = "json")]

use std::sync::Arc;
use sysmlv2_parser::{
    json::ResolvedModel, libcache::LibraryCache, model::Model, prepared::PreparedLibrary,
};

fn models(library: &str, user: &str) -> Vec<ResolvedModel> {
    let mut base = Model::new();
    base.add_library_source("subjects.sysml", library);
    assert!(!base.has_errors());
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(32).unwrap(), 32).unwrap());
    (0..4)
        .map(|mode| {
            let mut m = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut m).unwrap(),
                3 => Arc::clone(&decoded).install(&mut m).unwrap(),
                _ => {
                    m.add_library_source("subjects.sysml", library);
                    if mode == 1 {
                        m.set_library_cache(cache.clone());
                    }
                }
            }
            m.add_source("user.sysml", user);
            assert!(!m.has_errors());
            ResolvedModel::build(&m)
        })
        .collect()
}

fn card(r: &mut ResolvedModel, name: &str) -> Option<(i128, Option<i128>)> {
    let e = r.resolve_qualified(name).unwrap();
    r.effective_cardinality(e)
}

#[test]
fn subjects_redefine_inherited_subjects_through_requirement_and_case_bases() {
    for mut r in models(
        "package L {
            requirement def R { subject original[1]; }
            requirement def RM :> R;
            case def C { subject original[2..4]; }
            case def CM :> C;
        }",
        "package P {
            requirement def Child :> L::RM { subject renamed; }
            requirement reqUse : Child { subject subjectAgain; }
            analysis def CaseChild :> L::CM { subject renamed; }
            analysis caseUse : CaseChild { subject subjectAgain; }
        }",
    ) {
        let child = r.resolve_qualified("P::Child").unwrap();
        let renamed = r.resolve_qualified("P::Child::renamed").unwrap();
        let original = r.resolve_qualified("L::R::original").unwrap();
        let inherited = r.inherited_features(child, true);
        assert!(!inherited.contains(&original));
        assert!(r.effective_features(child, true).contains(&renamed));
        let edges: Vec<_> = r
            .implied_relationships(renamed)
            .into_iter()
            .filter(|&edge| r.element_type(edge) == "Redefinition")
            .collect();
        assert_eq!(edges.len(), 1);
        assert_eq!(
            r.element_properties(edges[0])["redefinedFeature"]["@id"],
            r.element_id(original).to_string()
        );
        assert_eq!(
            r.element_properties(edges[0])["redefiningFeature"]["@id"],
            r.element_id(renamed).to_string()
        );
        assert!(!r.inherited_features(child, true).contains(&original));
        for _ in 0..2 {
            assert_eq!(card(&mut r, "P::Child::renamed"), Some((1, Some(1))));
            assert_eq!(card(&mut r, "P::reqUse::subjectAgain"), Some((1, Some(1))));
            assert_eq!(card(&mut r, "P::CaseChild::renamed"), Some((2, Some(4))));
            assert_eq!(card(&mut r, "P::caseUse::subjectAgain"), Some((2, Some(4))));
        }
    }
}

#[test]
fn cross_family_subjects_pair_by_position_only() {
    // No subject-family edge across families; the ordinary positional
    // pairing still reaches the parameter `Mid` inherits at that place.
    for mut r in models(
        "package L {
            requirement def R { subject original[1]; }
            requirement def Mid :> R;
        }",
        "package P { case def Child :> L::Mid { subject renamed; } }",
    ) {
        assert_eq!(card(&mut r, "P::Child::renamed"), Some((1, Some(1))));
        let e = r.resolve_qualified("P::Child::renamed").unwrap();
        let original = r.resolve_qualified("L::R::original").unwrap();
        let edges: Vec<_> = r
            .implied_relationships(e)
            .into_iter()
            .filter(|&edge| r.element_type(edge) == "Redefinition")
            .collect();
        assert_eq!(edges.len(), 1);
        assert_eq!(
            r.element_properties(edges[0])["redefinedFeature"]["@id"],
            r.element_id(original).to_string()
        );
    }
}

#[test]
fn explicit_subject_bounds_override_inheritance_and_distinct_bases_intersect() {
    for mut r in models(
        "package L {
            requirement def R { subject original[1..5]; }
            requirement def S { subject another[2..4]; }
        }",
        "package P {
            requirement def Child :> L::R, L::S { subject renamed; }
            requirement def Local :> L::R { subject renamed[3]; }
        }",
    ) {
        assert_eq!(card(&mut r, "P::Child::renamed"), Some((2, Some(4))));
        assert_eq!(card(&mut r, "P::Local::renamed"), Some((3, Some(3))));
    }
}

#[test]
fn ambiguous_or_incomplete_subject_heritage_does_not_guess() {
    for mut r in models(
        "package L {
            requirement def R { subject subjectA[1]; }
            requirement def S { subject subjectB[2]; }
            requirement def Ambiguous :> R, S;
        }",
        "package P {
            requirement def Child :> L::Ambiguous { subject renamed; }
            requirement def Missing :> NotFound { subject renamed; }
        }",
    ) {
        assert_eq!(card(&mut r, "P::Child::renamed"), None);
        assert_eq!(card(&mut r, "P::Missing::renamed"), None);
    }
}

#[test]
fn ordinary_behavior_parameters_pair_through_an_inheriting_general() {
    // `Mid`'s parameters are the ones it inherits after its own (none), so
    // `renamed` takes over `original` and its bounds.
    for mut r in models(
        "package L { action def A { in original[1]; } action def Mid :> A; }",
        "package P { action def Child :> L::Mid { in renamed; } }",
    ) {
        assert_eq!(card(&mut r, "P::Child::renamed"), Some((1, Some(1))));
    }
}
