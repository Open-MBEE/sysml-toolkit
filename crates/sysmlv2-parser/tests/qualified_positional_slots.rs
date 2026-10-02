//! A qualified redefinition removes only the selected inherited slot.
use std::sync::Arc;
use sysmlv2_parser::{
    json::{Reference, ResolvedModel},
    model::{GraphFormat, Model},
    prepared::PreparedLibrary,
};

fn assert_slots(mut r: ResolvedModel, signature_first: bool, remaining: &str) {
    let c = r.resolve_qualified("P::C").unwrap();
    let cr = r.resolve_qualified("P::C::r").unwrap();
    let bq = r.resolve_qualified(remaining).unwrap();
    let d = r.resolve_qualified("D").unwrap();
    let dx = r.resolve_qualified("D::x").unwrap();
    let dy = r.resolve_qualified("D::y").unwrap();
    if signature_first {
        assert_eq!(
            r.callable_parameters(c)
                .unwrap()
                .iter()
                .map(|p| p.element)
                .collect::<Vec<_>>(),
            [cr, bq]
        );
    }
    assert_eq!(r.positional_redefinition_targets(dx), [cr]);
    assert_eq!(r.positional_redefinition_targets(dy), [bq]);
    assert_eq!(
        r.callable_parameters(c)
            .unwrap()
            .iter()
            .map(|p| p.element)
            .collect::<Vec<_>>(),
        [cr, bq]
    );
    assert_eq!(
        r.callable_parameters(d)
            .unwrap()
            .iter()
            .map(|p| p.element)
            .collect::<Vec<_>>(),
        [dx, dy]
    );
    let implied = r.implied_relationships(dy);
    assert!(
        implied
            .into_iter()
            .any(|rel| r.element_type(rel) == "Redefinition"
                && r.relationship_ends(rel).1.contains(&Reference::Element(bq)))
    );
    assert_eq!(r.positional_redefinition_targets(dy), [bq]);
}

#[test]
fn qualified_redefinitions_keep_unselected_same_named_slots_across_order_and_replay() {
    for generals in ["A, B", "B, A"] {
        for selected in [
            "A::q",
            "$::P::A::q",
            "Chosen::q",
            "A::shortQ",
            "q",
            "shortQ",
        ] {
            for forward in [false, true] {
                let definitions = if forward {
                    "calc def B { in b; in q; } calc def A { in a; in <shortQ> q; } alias Chosen for A;"
                } else {
                    "calc def A { in a; in <shortQ> q; } calc def B { in b; in q; } alias Chosen for A;"
                };
                let child = format!("calc def C :> {generals} {{ in r :>> {selected}; }}");
                let source = if forward {
                    format!("package P {{ {child} {definitions} }}")
                } else {
                    format!("package P {{ {definitions} {child} }}")
                };
                let mut base = Model::new();
                let unit = base.add_library_source("slots.sysml", &source);
                assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
                let prepared = base.prepare_library().unwrap();
                let decoded = Arc::new(
                    PreparedLibrary::from_bytes(&prepared.to_bytes(219).unwrap(), 219).unwrap(),
                );
                for mode in 0..3 {
                    for signature_first in [false, true] {
                        let mut model = Model::new();
                        if mode == 0 {
                            model.add_library_source("slots.sysml", &source);
                        } else {
                            Arc::clone(if mode == 1 { &prepared } else { &decoded })
                                .install(&mut model)
                                .unwrap();
                        }
                        let unit =
                            model.add_source("user.sysml", "calc def D :> P::C { in x; in y; }");
                        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
                        assert_slots(
                            ResolvedModel::build(&model),
                            signature_first,
                            if selected == "q" && generals == "B, A" {
                                "P::A::q"
                            } else {
                                "P::B::q"
                            },
                        );
                    }
                }
            }
        }
    }
}

#[test]
fn qualified_redefinition_imported_qualifier_keeps_unselected_slot() {
    for generals in ["A, B", "B, A"] {
        let mut model = Model::new();
        let source = format!(
            "package Types {{ calc def A {{ in a; in q; }} }} package P {{ private import Types::A; calc def B {{ in b; in q; }} calc def C :> {generals} {{ in r :>> A::q; }} }} calc def D :> P::C {{ in x; in y; }}"
        );
        let unit = model.add_source("imported.sysml", &source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        assert_slots(ResolvedModel::build(&model), false, "P::B::q");
    }
}

#[test]
fn an_unresolved_qualified_redefinition_does_not_hide_namesakes() {
    let mut model = Model::new();
    model.add_source("missing.sysml", "calc def A { in a; in q; } calc def B { in b; in q; } calc def C :> A, B { in r :>> Missing::q; } calc def D :> C { in x; in y; in z; }");
    let mut r = ResolvedModel::build(&model);
    for (path, target) in [("D::y", "A::q"), ("D::z", "B::q")] {
        let slot = r.resolve_qualified(path).unwrap();
        let target = r.resolve_qualified(target).unwrap();
        assert_eq!(r.positional_redefinition_targets(slot), [target]);
    }
}

#[test]
fn cold_descendant_queries_preserve_header_selection_across_recorded_replay() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        for spelling in ["A::q", "q"] {
            let source = format!(
                "package P {{ calc def A {{ in a; in q; }} calc def B {{ in b; in q; }} calc def C :> A, B {{ in r :>> {spelling}; }} }}"
            );
            let mut base = Model::with_graph_format(format);
            assert!(
                base.add_library_source("cold-slots.sysml", &source)
                    .diagnostics
                    .is_empty()
            );
            base.record_library_cache();
            let prepared = base.prepare_library().unwrap();
            let decoded = Arc::new(
                PreparedLibrary::from_bytes(&prepared.to_bytes(223).unwrap(), 223).unwrap(),
            );
            for mode in 0..3 {
                for complete_root in [false, true] {
                    for signature_first in [false, true] {
                        let mut model = Model::with_graph_format(format);
                        if mode == 0 {
                            model.add_library_source("cold-slots.sysml", &source);
                        } else {
                            Arc::clone(if mode == 1 { &prepared } else { &decoded })
                                .install(&mut model)
                                .unwrap();
                        }
                        // Supplying an implied root can invalidate prepared lookup
                        // evidence; test the resulting cold graph as well.
                        let root = if complete_root {
                            "package Calculations;"
                        } else {
                            ""
                        };
                        assert!(
                            model
                                .add_source(
                                    "descendant.sysml",
                                    &format!("{root} calc def D :> P::C {{ in x; in y; }}")
                                )
                                .diagnostics
                                .is_empty()
                        );
                        let mut r = ResolvedModel::build(&model);
                        let d = r.resolve_qualified("D").unwrap();
                        // Capture these results before querying any general or
                        // expected target, which would warm the relevant scopes.
                        let first_signature =
                            signature_first.then(|| r.callable_parameters(d).unwrap());
                        let dy = r.resolve_qualified("D::y").unwrap();
                        let first_targets = r.positional_redefinition_targets(dy);
                        let remaining = r.resolve_qualified("P::B::q").unwrap();
                        assert_eq!(
                            first_targets,
                            [remaining],
                            "{format:?} {spelling} mode {mode} root {complete_root} signature {signature_first}"
                        );
                        let dx = r.resolve_qualified("D::x").unwrap();
                        if let Some(signature) = first_signature {
                            assert_eq!(
                                signature.into_iter().map(|p| p.element).collect::<Vec<_>>(),
                                [dx, dy]
                            );
                        }
                        assert_eq!(
                            r.callable_parameters(d)
                                .unwrap()
                                .into_iter()
                                .map(|p| p.element)
                                .collect::<Vec<_>>(),
                            [dx, dy]
                        );
                        assert_eq!(r.positional_redefinition_targets(dy), first_targets);
                    }
                }
            }
        }
    }
}
