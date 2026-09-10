//! `extract_definition` gates: splice-minimal fixtures
//! (moved body byte-identical, only header/placement text synthesized),
//! name-conflict and shadow-capture refusals, header preservation, and
//! the corpus sweep over matrix-eligible inline-bodied usages.

use sysmlv2_transform::{ElementRef, Session, TransformError};

fn session(src: &str) -> Session {
    Session::from_sources(vec![("m.sysml".into(), src.into())]).expect("parses")
}

fn elem(s: &mut Session, qn: &str) -> ElementRef {
    s.resolved()
        .resolve_qualified(qn)
        .unwrap_or_else(|| panic!("`{qn}` resolves"))
}

fn text(s: &Session) -> String {
    s.units().next().unwrap().2.to_string()
}

fn extract(s: &mut Session, qn: &str, name: Option<&str>) -> Result<(), TransformError> {
    let e = elem(s, qn);
    let mut edit = s.edit();
    edit.extract_definition(e, name);
    edit.commit().map(|_| ())
}

// ---------------------------------------------------------------------------
// Splice-minimal fixtures: exact output, notes preserved byte-for-byte
// ---------------------------------------------------------------------------

#[test]
fn typed_usage_extracts_byte_exactly() {
    let src = "package P {
    part def A;
    part engine : A {
        attribute mass = 100; // stays byte-identical
        part turbo;
    }
}
";
    let mut s = session(src);
    extract(&mut s, "P::engine", None).expect("extracts");
    assert_eq!(
        text(&s),
        "package P {
    part def A;
    part def Engine :> A {
        attribute mass = 100; // stays byte-identical
        part turbo;
    }
    part engine : Engine;
}
"
    );
    // The relocated members are addressable at their new home.
    assert!(s.resolved().resolve_qualified("P::Engine::mass").is_some());
    assert!(s.resolved().resolve_qualified("P::engine").is_some());
}

#[test]
fn quoted_typing_segments_containing_colons_generalize() {
    let src = "package P {
    part def 'Base::Type';
    part engine : 'Base::Type' {
        attribute x;
    }
}
";
    let mut s = session(src);
    extract(&mut s, "P::engine", None).expect("extracts");
    assert_eq!(
        text(&s),
        "package P {
    part def 'Base::Type';
    part def Engine :> 'Base::Type' {
        attribute x;
    }
    part engine : Engine;
}
"
    );
}

#[test]
fn untyped_usage_extracts_with_a_fresh_typing() {
    let src = "package P {
    part box {
        attribute w = 1;
    }
}
";
    let mut s = session(src);
    extract(&mut s, "P::box", None).expect("extracts");
    assert_eq!(
        text(&s),
        "package P {
    part def Box {
        attribute w = 1;
    }
    part box : Box;
}
"
    );
}

#[test]
fn comments_with_braces_do_not_fool_the_body_scan() {
    let src = "package P {
    part u {
        /* { a stray opening brace in a comment element */
        attribute a;
    }
}
";
    let mut s = session(src);
    extract(&mut s, "P::u", None).expect("extracts");
    let out = text(&s);
    assert!(
        out.contains("/* { a stray opening brace in a comment element */"),
        "{out}"
    );
    assert!(out.contains("part u : U;"), "{out}");
}

#[test]
fn header_facts_stay_on_the_usage() {
    // Multiplicity and value are usage-level facts; only the typing is
    // replaced and the body moves.
    let src = "package P {
    attribute def A;
    attribute cfg : A [2] = 42 {
        attribute nested;
    }
}
";
    let mut s = session(src);
    extract(&mut s, "P::cfg", None).expect("extracts");
    assert_eq!(
        text(&s),
        "package P {
    attribute def A;
    attribute def Cfg :> A {
        attribute nested;
    }
    attribute cfg : Cfg [2] = 42;
}
"
    );
}

#[test]
fn multiple_qualified_typings_generalize_in_order() {
    let src = "package P {
    package Q { part def A; part def B; }
    part e : Q::A, Q::B {
        attribute x;
    }
}
";
    let mut s = session(src);
    extract(&mut s, "P::e", None).expect("extracts");
    let out = text(&s);
    assert!(out.contains("part def E :> Q::A, Q::B {"), "{out}");
    assert!(out.contains("part e : E;"), "{out}");
}

#[test]
fn nested_usage_extracts_into_its_owner_scope() {
    // The moved body references a sibling of the usage (`k`), which stays
    // lexically visible from the sibling definition's body.
    let src = "package P {
    part def Ctx {
        attribute k;
        part u {
            attribute copy = k;
        }
    }
}
";
    let mut s = session(src);
    extract(&mut s, "P::Ctx::u", None).expect("extracts");
    assert_eq!(
        text(&s),
        "package P {
    part def Ctx {
        attribute k;
        part def U {
            attribute copy = k;
        }
        part u : U;
    }
}
"
    );
    assert!(s.resolved().resolve_qualified("P::Ctx::U::copy").is_some());
}

#[test]
fn chain_references_through_the_usage_survive() {
    let src = "package P {
    part engine {
        attribute mass = 100;
    }
    attribute total = engine.mass;
}
";
    let mut s = session(src);
    extract(&mut s, "P::engine", None).expect("extracts");
    let out = text(&s);
    assert!(out.contains("part def Engine {"), "{out}");
    assert!(out.contains("attribute total = engine.mass;"), "{out}");
    // The chain now reaches the relocated member.
    assert!(s.resolved().resolve_qualified("P::Engine::mass").is_some());
}

#[test]
fn correspondence_preserves_quoted_segments_containing_colons() {
    let src = "package P {
    part u {
        attribute 'a::b' = 1;
        attribute copy = 'a::b';
    }
}
";
    let mut s = session(src);
    let member = elem(&mut s, "P::u::'a::b'");
    let old_id = s.resolved().element_id(member);
    let usage = elem(&mut s, "P::u");
    let mut edit = s.edit();
    edit.extract_definition(usage, None);
    let report = edit.commit().expect("extracts");
    let moved = elem(&mut s, "P::U::'a::b'");
    let new_id = s.resolved().element_id(moved);
    assert!(report.id_map.contains(&(old_id, new_id)), "{report:?}");
    assert!(text(&s).contains("attribute copy = 'a::b';"));
}

// ---------------------------------------------------------------------------
// Naming
// ---------------------------------------------------------------------------

#[test]
fn name_synthesis_is_upper_camel_and_explicit_names_win() {
    let src = "package P {
    part fuel_tank { attribute v; }
}
";
    let mut s = session(src);
    extract(&mut s, "P::fuel_tank", None).expect("extracts");
    assert!(text(&s).contains("part def FuelTank {"), "{}", text(&s));

    let mut s = session(src);
    extract(&mut s, "P::fuel_tank", Some("Reservoir")).expect("extracts");
    let out = text(&s);
    assert!(out.contains("part def Reservoir {"), "{out}");
    assert!(out.contains("part fuel_tank : Reservoir;"), "{out}");
}

#[test]
fn a_sibling_holding_the_name_refuses() {
    let src = "package P {
    part def Engine;
    part engine { attribute mass; }
}
";
    let mut s = session(src);
    match extract(&mut s, "P::engine", None).unwrap_err() {
        TransformError::NameTaken { name, existing } => {
            assert_eq!(name, "Engine");
            assert_eq!(existing, "P::Engine");
        }
        other => panic!("wrong refusal: {other}"),
    }
    assert_eq!(text(&s), src, "nothing applied");
}

#[test]
fn a_name_visible_through_an_import_refuses() {
    let src = "package L { part def Engine; }
package P {
    private import L::Engine;
    part engine { attribute mass; }
}
";
    let mut s = session(src);
    match extract(&mut s, "P::engine", None).unwrap_err() {
        TransformError::NameTaken { name, existing } => {
            assert_eq!(name, "Engine");
            assert!(existing.contains("visible `Engine`"), "{existing}");
        }
        other => panic!("wrong refusal: {other}"),
    }
    assert_eq!(text(&s), src, "nothing applied");
}

#[test]
fn a_name_visible_from_an_enclosing_scope_refuses_early() {
    // No sibling is named `Engine`, but inserting `part def Engine`
    // inside Assembly shadows the outer definition for `legacy`'s
    // typing — the semantic-identity check must reject and roll back.
    let src = "package P {
    part def Engine;
    part def Assembly {
        part motor { attribute torque; }
        part legacy : Engine;
    }
}
";
    let mut s = session(src);
    match extract(&mut s, "P::Assembly::motor", Some("Engine")).unwrap_err() {
        TransformError::NameTaken { name, existing } => {
            assert_eq!(name, "Engine");
            assert!(existing.contains("visible `Engine`"), "{existing}");
        }
        other => panic!("wrong refusal: {other}"),
    }
    assert_eq!(text(&s), src, "rolled back");
}

#[test]
fn ineligible_usages_carry_their_named_reason() {
    let src = "package P {
    part bare;
}
";
    let mut s = session(src);
    match extract(&mut s, "P::bare", None).unwrap_err() {
        TransformError::ExtractIneligible { reason } => {
            assert_eq!(
                reason,
                sysmlv2_transform::eligibility::ExtractRefusal::NoInlineBody
            );
        }
        other => panic!("wrong refusal: {other}"),
    }
}

// ---------------------------------------------------------------------------
// Pipeline behavior
// ---------------------------------------------------------------------------

#[test]
fn dry_run_reports_without_touching_the_session() {
    let src = "package P {
    part engine { attribute mass; }
}
";
    let mut s = session(src);
    let e = elem(&mut s, "P::engine");
    let mut edit = s.edit();
    edit.extract_definition(e, None);
    let report = edit.check().expect("dry-run succeeds");
    assert!(!report.splices.is_empty());
    assert_eq!(text(&s), src, "session untouched");
}

#[test]
fn extracting_into_a_body_that_rejects_definitions_refuses() {
    // A part usage nested in an action body is legal, but a synthesized
    // `part def` in that body may not be — the relocation validation net
    // must hold the checker's verdict constant rather than commit a
    // file that no longer validates.
    let src = "package P {
    action def Act {
        part tool { attribute t; }
    }
}
";
    let mut s = session(src);
    match extract(&mut s, "P::Act::tool", None) {
        // Either the checker forbids it (net refusal, rolled back) …
        Err(TransformError::NewValidationFindings { .. }) => {
            assert_eq!(text(&s), src, "rolled back");
        }
        // … or this context legally admits definitions, in which case
        // the commit must have kept the checker's verdict constant.
        Ok(()) => {
            let parse = sysmlv2_syntax::parser::parse_source(&text(&s));
            assert!(parse.diagnostics.is_empty());
            assert!(sysmlv2_syntax::check::validate(&parse.unit).is_empty());
        }
        Err(other) => panic!("unexpected refusal: {other}"),
    }
}

#[test]
fn the_validation_net_refuses_a_definition_the_owner_body_rejects() {
    // Superset parsing admits a part usage inside an enumeration body
    // (the checker flags it; the session still builds). Extracting it
    // would add a `part def` to that body — a NEW finding beyond the
    // pre-existing tolerated one — so the net must refuse and roll back.
    let src = "package P {
    enum def E {
        part tool { attribute t; }
    }
}
";
    let mut s = session(src);
    match extract(&mut s, "P::E::tool", None).unwrap_err() {
        TransformError::NewValidationFindings { findings } => {
            assert_eq!(findings.len(), 1, "{findings:?}");
        }
        other => panic!("wrong refusal: {other}"),
    }
    assert_eq!(text(&s), src, "rolled back");
}

#[test]
fn identical_validation_messages_at_distinct_sites_do_not_cancel() {
    let src = "package P {
    enum def OldSite {
        part def Invalid;
    }
    enum def NewSite {
        part tool { attribute t; }
    }
}
";
    let mut s = session(src);
    let old = elem(&mut s, "P::OldSite::Invalid");
    let tool = elem(&mut s, "P::NewSite::tool");
    let mut edit = s.edit();
    edit.remove(old);
    edit.extract_definition(tool, None);
    match edit.commit().unwrap_err() {
        TransformError::NewValidationFindings { findings } => {
            assert!(
                findings.iter().any(|f| f.contains("definition")),
                "{findings:?}"
            );
            assert!(
                findings.iter().any(|f| f.contains("m.sysml:")),
                "{findings:?}"
            );
        }
        other => panic!("wrong refusal: {other}"),
    }
    assert_eq!(text(&s), src, "rolled back");
}

// ---------------------------------------------------------------------------
// Corpus sweep: every matrix-eligible inline-bodied non-library usage
// ---------------------------------------------------------------------------

#[test]
fn corpus_extract_gate() {
    let files = sysmlv2_testkit::user_files();
    assert!(files.len() > 100, "expected the corpus checkout");
    let mut eligible = 0usize;
    let mut extracted = 0usize;
    let mut refused = 0usize;
    for path in files {
        let original = std::fs::read_to_string(&path).unwrap();
        let name = path.display().to_string();
        let Ok(mut s) = Session::from_sources(vec![(name.clone(), original.clone())]) else {
            continue; // files that don't parse are out of scope
        };
        // Matrix-kind, named, eligibility-approved usages (typed usages
        // whose types need the library refuse via UnresolvedTyping and
        // are skipped — this sweep runs library-less).
        let mut qns: Vec<String> = Vec::new();
        for meta in ["PartUsage", "ItemUsage", "AttributeUsage", "PortUsage"] {
            for e in s.resolved().elements_of_metaclass(meta) {
                if s.resolved().is_library_element(e) || s.resolved().element_name(e).is_none() {
                    continue;
                }
                if s.extract_definition_eligibility(e).is_ok() {
                    if let Some(qn) = s.resolved().element_qualified_name(e) {
                        qns.push(qn);
                    }
                }
            }
        }
        qns.truncate(3);
        for qn in qns {
            eligible += 1;
            let Ok(mut s2) = Session::from_sources(vec![(name.clone(), original.clone())]) else {
                break;
            };
            let e = s2
                .resolved()
                .resolve_qualified(&qn)
                .expect("candidate resolves");
            let interior = {
                let el = s2
                    .extract_definition_eligibility(e)
                    .expect("still eligible");
                let src = s2.source(el.unit).expect("user unit");
                src[el.body_interior.start as usize..el.body_interior.end as usize].to_string()
            };
            let mut edit = s2.edit();
            edit.extract_definition(e, Some("Zz9ExtractGateZz9"));
            match edit.commit() {
                Ok(_) => {
                    extracted += 1;
                    let out = s2.units().next().unwrap().2.to_string();
                    assert!(
                        out.contains(&interior),
                        "moved body must stay byte-identical [{name}] {qn}"
                    );
                    assert!(out.contains("def Zz9ExtractGateZz9"), "[{name}] {qn}");
                }
                Err(
                    TransformError::SemanticIdentity { .. }
                    | TransformError::NewUnresolvedReferences { .. }
                    | TransformError::NewValidationFindings { .. }
                    | TransformError::StructuralIdentity { .. },
                ) => {
                    assert_eq!(
                        s2.units().next().unwrap().2,
                        original,
                        "refusal must roll back [{name}] {qn}"
                    );
                    refused += 1;
                }
                Err(other) => panic!("extract failed [{name}] {qn}: {other}"),
            }
        }
    }
    eprintln!("corpus extract: {eligible} eligible, {extracted} extracted, {refused} refused");
    // Ratchet floors from the landing run (305 eligible / 253 extracted /
    // 52 refused, library-less) — raise when coverage grows, never lower.
    assert!(
        eligible >= 290,
        "eligibility ratchet slipped: only {eligible} candidates"
    );
    assert!(
        extracted >= 240,
        "extract ratchet slipped: only {extracted} extracts succeeded"
    );
}
