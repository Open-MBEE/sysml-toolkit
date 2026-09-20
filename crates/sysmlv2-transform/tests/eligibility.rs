//! Eligibility gates: the per-kind matrix, the named
//! header refusals, the destination-context probe (view `expose`,
//! enumeration strictness), and the provenance classification of a
//! definition's incoming references (`engine.mass` vs `Engine::mass`).

use sysmlv2_transform::eligibility::{
    ExtractRefusal, InlineRefusal, PlainTyping, probe_body_in_definition_context,
};
use sysmlv2_transform::{ElementRef, Library, Session};

fn session(src: &str) -> Session {
    Session::from_sources(vec![("m.sysml".into(), src.into())]).expect("parses")
}

fn elem(s: &mut Session, qn: &str) -> ElementRef {
    s.resolved()
        .resolve_qualified(qn)
        .unwrap_or_else(|| panic!("`{qn}` resolves"))
}

// ---------------------------------------------------------------------------
// Extract direction
// ---------------------------------------------------------------------------

#[test]
fn an_eligible_part_usage_reports_its_moved_region_and_typings() {
    let src = "package P {
    part def A;
    part engine : A {
        attribute mass = 100;
        part turbo {
            attribute boost;
        }
    }
}";
    let mut s = session(src);
    let engine = elem(&mut s, "P::engine");
    let e = s
        .extract_definition_eligibility(engine)
        .expect("part usages are in the v1 set");
    assert_eq!(e.keyword, "part");
    assert_eq!(
        e.plain_typings,
        vec![PlainTyping {
            spelling: "A".into(),
            target_qn: "P::A".into(),
        }]
    );
    let interior = &src[e.body_interior.start as usize..e.body_interior.end as usize];
    assert!(interior.contains("attribute mass = 100"), "{interior}");
    assert!(interior.contains("part turbo"), "{interior}");
    assert!(!interior.contains("engine"), "header stays out: {interior}");
    assert!(!interior.trim_start().starts_with('{'), "{interior}");
}

#[test]
fn nested_usages_are_extractable_too() {
    let src = "package P {
    part outer {
        part inner {
            attribute a;
        }
    }
}";
    let mut s = session(src);
    let inner = elem(&mut s, "P::outer::inner");
    let e = s.extract_definition_eligibility(inner).expect("eligible");
    let interior = &src[e.body_interior.start as usize..e.body_interior.end as usize];
    assert!(interior.contains("attribute a"), "{interior}");
    assert!(e.plain_typings.is_empty());
}

#[test]
fn conjugated_typing_refuses_by_name() {
    let src = "package P {
    port def Pt { attribute v; }
    part def V {
        port q : ~Pt { attribute w; }
    }
}";
    let mut s = session(src);
    let q = elem(&mut s, "P::V::q");
    assert_eq!(
        s.extract_definition_eligibility(q).unwrap_err(),
        ExtractRefusal::ConjugatedTyping
    );
}

#[test]
fn unresolved_typing_refuses_before_composition() {
    let src = "package P {
    part engine : Missing { attribute mass; }
}";
    let mut s = session(src);
    let engine = elem(&mut s, "P::engine");
    assert_eq!(
        s.extract_definition_eligibility(engine).unwrap_err(),
        ExtractRefusal::UnresolvedTyping {
            spelling: "Missing".into(),
        }
    );
}

#[test]
fn qualified_multiple_typings_carry_resolved_expectations() {
    let src = "package P {
    package Q { part def A; part def B; }
    part engine : Q::A, Q::B { attribute mass; }
}";
    let mut s = session(src);
    let engine = elem(&mut s, "P::engine");
    let eligibility = s.extract_definition_eligibility(engine).expect("eligible");
    assert_eq!(
        eligibility.plain_typings,
        vec![
            PlainTyping {
                spelling: "Q::A".into(),
                target_qn: "P::Q::A".into(),
            },
            PlainTyping {
                spelling: "Q::B".into(),
                target_qn: "P::Q::B".into(),
            },
        ]
    );
}

#[test]
fn variation_and_variant_forms_refuse() {
    let src = "package P {
    variation part choice {
        variant part optA { attribute z; }
    }
}";
    let mut s = session(src);
    let choice = elem(&mut s, "P::choice");
    assert_eq!(
        s.extract_definition_eligibility(choice).unwrap_err(),
        ExtractRefusal::VariationOrVariant
    );
    let opt_a = elem(&mut s, "P::choice::optA");
    assert_eq!(
        s.extract_definition_eligibility(opt_a).unwrap_err(),
        ExtractRefusal::VariationOrVariant
    );
}

#[test]
fn occurrence_forms_refuse() {
    let src = "package P {
    individual part ind { attribute a; }
    snapshot part snap { attribute b; }
}";
    let mut s = session(src);
    let ind = elem(&mut s, "P::ind");
    assert_eq!(
        s.extract_definition_eligibility(ind).unwrap_err(),
        ExtractRefusal::OccurrenceForm
    );
    let snap = elem(&mut s, "P::snap");
    assert_eq!(
        s.extract_definition_eligibility(snap).unwrap_err(),
        ExtractRefusal::OccurrenceForm
    );
}

#[test]
fn a_leading_succession_refuses() {
    let src = "package P {
    part def Assembly {
        part anchor;
        then part tool { attribute t; }
    }
}";
    let mut s = session(src);
    let tool = elem(&mut s, "P::Assembly::tool");
    assert_eq!(
        s.extract_definition_eligibility(tool).unwrap_err(),
        ExtractRefusal::LeadingSuccession
    );
}

#[test]
fn prefix_metadata_refuses() {
    let src = "package P {
    metadata def Safety;
    #Safety part x { attribute a; }
}";
    let mut s = session(src);
    let x = elem(&mut s, "P::x");
    assert_eq!(
        s.extract_definition_eligibility(x).unwrap_err(),
        ExtractRefusal::PrefixMetadata
    );
}

#[test]
fn view_and_enum_kinds_are_matrix_gated_not_assumed() {
    let src = "package P {
    part def Scope;
    view v { expose Scope; }
    enum def Level { high; low; }
    part def C {
        enum lv : Level { }
    }
}";
    let mut s = session(src);
    let v = elem(&mut s, "P::v");
    match s.extract_definition_eligibility(v).unwrap_err() {
        ExtractRefusal::UnsupportedKind { keyword, reason } => {
            assert_eq!(keyword, "view");
            assert!(reason.contains("expose"), "{reason}");
        }
        other => panic!("wrong refusal: {other}"),
    }
    let lv = elem(&mut s, "P::C::lv");
    match s.extract_definition_eligibility(lv).unwrap_err() {
        ExtractRefusal::UnsupportedKind { keyword, reason } => {
            assert_eq!(keyword, "enum");
            assert!(reason.contains("literals"), "{reason}");
        }
        other => panic!("wrong refusal: {other}"),
    }
}

#[test]
fn kinds_without_a_definition_counterpart_refuse() {
    let src = "package P {
    part def A;
    ref x : A { attribute a; }
}";
    let mut s = session(src);
    let x = elem(&mut s, "P::x");
    match s.extract_definition_eligibility(x).unwrap_err() {
        ExtractRefusal::UnsupportedKind { reason, .. } => {
            assert!(
                reason.contains("no textual definition counterpart"),
                "{reason}"
            );
        }
        other => panic!("wrong refusal: {other}"),
    }
}

#[test]
fn behavior_family_kinds_are_gated_until_proven() {
    let src = "package P {
    action a { attribute x; }
}";
    let mut s = session(src);
    let a = elem(&mut s, "P::a");
    match s.extract_definition_eligibility(a).unwrap_err() {
        ExtractRefusal::UnsupportedKind { keyword, .. } => assert_eq!(keyword, "action"),
        other => panic!("wrong refusal: {other}"),
    }
}

#[test]
fn a_bodyless_usage_has_nothing_to_extract() {
    let src = "package P {
    part def A;
    part x;
    part y : A;
}";
    let mut s = session(src);
    for qn in ["P::x", "P::y"] {
        let e = elem(&mut s, qn);
        assert_eq!(
            s.extract_definition_eligibility(e).unwrap_err(),
            ExtractRefusal::NoInlineBody
        );
    }
}

#[test]
fn kerml_units_are_out_of_scope() {
    let mut s = Session::from_sources(vec![(
        "m.kerml".into(),
        "package K { feature f { feature g; } }".into(),
    )])
    .expect("parses");
    let f = elem(&mut s, "K::f");
    assert_eq!(
        s.extract_definition_eligibility(f).unwrap_err(),
        ExtractRefusal::UnsupportedDialect
    );
}

#[test]
fn a_unit_named_in_upper_case_is_the_same_dialect() {
    // Unit names come from file systems that do not distinguish case,
    // so the dialect a name spells is read without it: this text parses
    // (it is KerML, which SysML would reject) and the gate refuses it
    // for the same dialect the parse chose.
    let mut s = Session::from_sources(vec![(
        "m.KerML".into(),
        "package K { feature f { feature g; } }".into(),
    )])
    .expect("parses");
    let f = elem(&mut s, "K::f");
    assert_eq!(
        s.extract_definition_eligibility(f).unwrap_err(),
        ExtractRefusal::UnsupportedDialect
    );
}

#[test]
fn a_definition_is_not_an_extractable_usage() {
    let src = "package P { part def A { attribute a; } }";
    let mut s = session(src);
    let a = elem(&mut s, "P::A");
    match s.extract_definition_eligibility(a).unwrap_err() {
        ExtractRefusal::NotAUsage { metaclass } => assert_eq!(metaclass, "PartDefinition"),
        other => panic!("wrong refusal: {other}"),
    }
}

// ---------------------------------------------------------------------------
// The destination-context probe proves the matrix
// ---------------------------------------------------------------------------

#[test]
fn the_probe_runs_the_real_body_context_checker() {
    // A view usage body admits `expose`; a view definition body must
    // reject it — the exact divergence that keeps `view` out of v1.
    assert!(
        !probe_body_in_definition_context("view", " expose Scope; ").is_empty(),
        "expose must be illegal in a view definition body"
    );
    // An enumeration definition body admits only literals/annotations.
    assert!(
        !probe_body_in_definition_context("enum", " part p; ").is_empty(),
        "a part member must be illegal in an enumeration definition body"
    );
    // The v1 pairs share their body context: what a part usage owns is
    // legal in a part definition.
    assert!(
        probe_body_in_definition_context("part", " attribute mass = 100; part turbo; ").is_empty()
    );
    assert!(probe_body_in_definition_context("attribute", " attribute sub; ").is_empty());
    assert!(probe_body_in_definition_context("port", " attribute v; ").is_empty());
    assert!(probe_body_in_definition_context("item", " item nested; ").is_empty());
}

// ---------------------------------------------------------------------------
// Inline direction: provenance classification
// ---------------------------------------------------------------------------

const INLINE_OK: &str = "package P {
    part def Engine {
        attribute mass;
        attribute margin = mass * 2;
    }
    part engine : Engine;
    attribute total = engine.mass;
}";

#[test]
fn a_sole_usage_definition_classifies_internal_and_through_usage_sites() {
    let mut s = session(INLINE_OK);
    let def = elem(&mut s, "P::Engine");
    let usage = elem(&mut s, "P::engine");
    let ok = s
        .inline_definition_eligibility(def)
        .expect("sole usage, no outside references");
    assert_eq!(ok.usage, usage);
    // (a) `mass` inside `margin`'s value moves with the body.
    assert_eq!(ok.internal_sites.len(), 1, "{:?}", ok.internal_sites);
    // (b) `engine.mass` re-anchors through the usage.
    assert_eq!(
        ok.through_usage_sites.len(),
        1,
        "{:?}",
        ok.through_usage_sites
    );
    assert_eq!(ok.through_usage_sites[0].chain_root, Some(usage));
}

#[test]
fn a_redefinition_in_the_usage_body_is_a_member_collision() {
    // `:>> mass` carries the effective name `mass`: post-inline it
    // would sit beside an *owned* sibling `mass` — a merge v1 refuses
    // by name rather than attempting a collision policy (merge
    // semantics are deferred; the projection would refuse the
    // commit anyway).
    let src = "package P {
    part def Engine {
        attribute mass;
    }
    part engine : Engine {
        attribute :>> mass = 5;
    }
}";
    let mut s = session(src);
    let def = elem(&mut s, "P::Engine");
    assert_eq!(
        s.inline_definition_eligibility(def).unwrap_err(),
        InlineRefusal::MemberCollision {
            names: vec!["mass".into()],
        }
    );
}

#[test]
fn an_unqualified_inherited_reference_inside_the_usage_remains_eligible() {
    let src = "package P {
    part def Engine { attribute mass; }
    part engine : Engine {
        attribute copy = mass;
    }
}";
    let mut s = session(src);
    let def = elem(&mut s, "P::Engine");
    let ok = s.inline_definition_eligibility(def).expect("eligible");
    assert_eq!(ok.through_usage_sites.len(), 1, "{ok:?}");
}

#[test]
fn a_definition_qualified_reference_inside_the_usage_refuses() {
    let src = "package P {
    part def Engine { attribute mass; }
    part engine : Engine {
        attribute copy = Engine::mass;
    }
}";
    let mut s = session(src);
    let def = elem(&mut s, "P::Engine");
    match s.inline_definition_eligibility(def).unwrap_err() {
        InlineRefusal::OutsideReferences { sites } => {
            assert!(!sites.is_empty(), "{sites:?}");
            assert!(
                sites.iter().all(|site| site.contains("`Engine::mass`")),
                "{sites:?}"
            );
        }
        other => panic!("wrong refusal: {other}"),
    }
}

#[test]
fn an_outside_reference_through_the_definition_refuses_and_names_the_site() {
    let src = "package P {
    part def Engine {
        attribute mass;
    }
    part engine : Engine;
    attribute direct = Engine::mass;
}";
    let mut s = session(src);
    let def = elem(&mut s, "P::Engine");
    match s.inline_definition_eligibility(def).unwrap_err() {
        InlineRefusal::OutsideReferences { sites } => {
            // Both the member reference and its qualifier segment point
            // into the subtree from outside.
            assert_eq!(sites.len(), 2, "{sites:?}");
            assert!(
                sites.iter().all(|m| m.contains("`Engine::mass`")),
                "{sites:?}"
            );
            assert!(sites.iter().all(|m| m.contains("m.sysml")), "{sites:?}");
        }
        other => panic!("wrong refusal: {other}"),
    }
}

#[test]
fn a_specialization_from_another_definition_refuses() {
    let src = "package P {
    part def Engine { attribute mass; }
    part engine : Engine;
    part def Better :> Engine;
}";
    let mut s = session(src);
    let def = elem(&mut s, "P::Engine");
    match s.inline_definition_eligibility(def).unwrap_err() {
        InlineRefusal::OutsideReferences { sites } => {
            assert_eq!(sites.len(), 1, "{sites:?}");
            assert!(sites[0].contains("`Engine`"), "{sites:?}");
        }
        other => panic!("wrong refusal: {other}"),
    }
}

#[test]
fn usage_count_gates() {
    let none = "package P { part def Engine { attribute mass; } }";
    let mut s = session(none);
    let def = elem(&mut s, "P::Engine");
    assert_eq!(
        s.inline_definition_eligibility(def).unwrap_err(),
        InlineRefusal::NoTypingUsage
    );

    let two = "package P {
    part def Engine { attribute mass; }
    part e1 : Engine;
    part e2 : Engine;
}";
    let mut s = session(two);
    let def = elem(&mut s, "P::Engine");
    assert_eq!(
        s.inline_definition_eligibility(def).unwrap_err(),
        InlineRefusal::MultipleTypingUsages { count: 2 }
    );
}

#[test]
fn a_conjugated_sole_typing_is_not_plain() {
    let src = "package P {
    port def Pt { attribute v; }
    part def V {
        port q : ~Pt;
    }
}";
    let mut s = session(src);
    let def = elem(&mut s, "P::Pt");
    match s.inline_definition_eligibility(def).unwrap_err() {
        InlineRefusal::NonPlainTyping { relationship } => {
            assert_eq!(relationship, "ConjugatedPortTyping");
        }
        other => panic!("wrong refusal: {other}"),
    }
}

#[test]
fn gated_definition_kinds_refuse_inline_too() {
    let src = "package P {
    action def Act { attribute x; }
    action a : Act;
}";
    let mut s = session(src);
    let def = elem(&mut s, "P::Act");
    match s.inline_definition_eligibility(def).unwrap_err() {
        InlineRefusal::UnsupportedKind { keyword, .. } => assert_eq!(keyword, "action"),
        other => panic!("wrong refusal: {other}"),
    }
}

#[test]
fn unsupported_definition_headers_refuse_inline() {
    let src = "package P {
    abstract part def Engine { attribute mass; }
    part engine : Engine;
}";
    let mut s = session(src);
    let def = elem(&mut s, "P::Engine");
    match s.inline_definition_eligibility(def).unwrap_err() {
        InlineRefusal::UnsupportedHeader { reason } => {
            assert!(reason.contains("abstract"), "{reason}");
        }
        other => panic!("wrong refusal: {other}"),
    }
}

#[test]
fn library_definitions_refuse_inline() {
    let mut s = session("package P { part engine : L::Engine; }");
    s.load_library_from(Library::sources(vec![(
        "library.sysml".into(),
        "package L { part def Engine { attribute mass; } }".into(),
    )]))
    .expect("library loads");
    let def = elem(&mut s, "L::Engine");
    assert_eq!(
        s.inline_definition_eligibility(def).unwrap_err(),
        InlineRefusal::NotAUserElement
    );
}

#[test]
fn kerml_types_refuse_inline_by_dialect() {
    let mut s = Session::from_sources(vec![(
        "m.kerml".into(),
        "package K { class Engine { feature mass; } feature engine : Engine; }".into(),
    )])
    .expect("parses");
    let def = elem(&mut s, "K::Engine");
    assert_eq!(
        s.inline_definition_eligibility(def).unwrap_err(),
        InlineRefusal::UnsupportedDialect
    );
}

#[test]
fn a_usage_is_not_an_inlinable_definition() {
    let mut s = session(INLINE_OK);
    let usage = elem(&mut s, "P::engine");
    match s.inline_definition_eligibility(usage).unwrap_err() {
        InlineRefusal::NotADefinition { metaclass } => assert_eq!(metaclass, "PartUsage"),
        other => panic!("wrong refusal: {other}"),
    }
}
