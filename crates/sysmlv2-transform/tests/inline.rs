//! `inline_definition` gates: specialization
//! retargeting, typing drop, verified body merge (definition members
//! first), definition removal, newly-unused-import findings — plus the
//! one-sided inverse: `inline(extract(usage))` is byte-identical,
//! fixture-level and across every successful extract-sweep subject.

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

fn inline(s: &mut Session, qn: &str) -> Result<Vec<String>, TransformError> {
    let d = elem(s, qn);
    let mut edit = s.edit();
    edit.inline_definition(d);
    edit.commit().map(|r| r.findings)
}

// ---------------------------------------------------------------------------
// General inline fixtures (no reverse-placement promise)
// ---------------------------------------------------------------------------

#[test]
fn body_merge_puts_definition_members_first() {
    let src = "package P {
    part def A;
    part def Engine :> A {
        attribute mass = 100;
    }
    part engine : Engine {
        attribute serial;
    }
}
";
    let mut s = session(src);
    inline(&mut s, "P::Engine").expect("inlines");
    assert_eq!(
        text(&s),
        "package P {
    part def A;
    part engine : A {
        attribute mass = 100;
        attribute serial;
    }
}
"
    );
    assert!(s.resolved().resolve_qualified("P::engine::mass").is_some());
}

#[test]
fn quoted_specialization_segments_containing_colons_retarget() {
    let src = "package P {
    part def 'Base::Type';
    part def Engine :> 'Base::Type' {
        attribute x;
    }
    part engine : Engine;
}
";
    let mut s = session(src);
    inline(&mut s, "P::Engine").expect("inlines");
    assert_eq!(
        text(&s),
        "package P {
    part def 'Base::Type';
    part engine : 'Base::Type' {
        attribute x;
    }
}
"
    );
}

#[test]
fn a_specless_definition_drops_the_typing_entry() {
    let src = "package P {
    part def Tool;
    part tool : Tool;
}
";
    let mut s = session(src);
    inline(&mut s, "P::Tool").expect("inlines");
    assert_eq!(text(&s), "package P {\n    part tool;\n}\n");
}

#[test]
fn other_typing_entries_are_retained() {
    let src = "package P {
    part def Other;
    part def E {
        attribute x;
    }
    part e : E, Other;
}
";
    let mut s = session(src);
    inline(&mut s, "P::E").expect("inlines");
    assert_eq!(
        text(&s),
        "package P {
    part def Other;
    part e : Other {
        attribute x;
    }
}
"
    );
}

#[test]
fn placement_is_not_reconstructed() {
    // The definition lives *after* its usage — inline still lands the
    // body at the usage and deletes the definition where it was; no
    // attempt is made to remember that arrangement (extract would put
    // a fresh definition before the usage).
    let src = "package P {
    part engine : Engine {
        attribute serial;
    }
    part def Engine {
        attribute mass;
    }
}
";
    let mut s = session(src);
    inline(&mut s, "P::Engine").expect("inlines");
    assert_eq!(
        text(&s),
        "package P {
    part engine {
        attribute mass;
        attribute serial;
    }
}
"
    );
}

#[test]
fn member_collisions_refuse_with_names() {
    let src = "package P {
    part def Engine {
        attribute mass;
        attribute rpm;
    }
    part engine : Engine {
        attribute mass = 5;
    }
}
";
    let mut s = session(src);
    match inline(&mut s, "P::Engine").unwrap_err() {
        TransformError::InlineIneligible { reason } => {
            assert!(reason.to_string().contains("mass"), "{reason}");
        }
        other => panic!("wrong refusal: {other}"),
    }
    assert_eq!(text(&s), src, "nothing applied");
}

#[test]
fn imports_left_unused_by_the_deletion_are_findings_not_edits() {
    // Cross-unit inline: the definition lives in defs.sysml, its sole
    // usage in use.sysml behind a wildcard import that serves only the
    // typing. Post-inline nothing resolves through the import — it is
    // reported, not removed. (The unused-import textual condition scans the
    // import's own unit, so the surviving `Kit` in defs.sysml does not
    // suppress it.)
    let defs = "package Defs {
    part def Kit;
    part def Tool;
}
";
    let uses = "package Use {
    private import Defs::*;
    part tool : Tool;
}
";
    let mut s = Session::from_sources(vec![
        ("defs.sysml".into(), defs.into()),
        ("use.sysml".into(), uses.into()),
    ])
    .expect("parses");
    let findings = inline(&mut s, "Defs::Tool").expect("inlines");
    assert!(
        findings
            .iter()
            .any(|f| f.contains("import now unused") && f.contains("Defs::*")),
        "{findings:?}"
    );
    let unit = |s: &Session, name: &str| -> String {
        s.units()
            .find(|(_, n, _)| *n == name)
            .unwrap()
            .2
            .to_string()
    };
    // The import itself is untouched — removal is the quick fix's job.
    assert_eq!(
        unit(&s, "use.sysml"),
        "package Use {\n    private import Defs::*;\n    part tool;\n}\n"
    );
    assert_eq!(
        unit(&s, "defs.sysml"),
        "package Defs {\n    part def Kit;\n}\n"
    );
}

#[test]
fn carried_body_references_reanchor_at_the_usage() {
    // `margin`'s `mass` moves with the body; `total`'s `engine.mass`
    // chain re-anchors through the usage — both verified by the commit.
    let src = "package P {
    part def Engine {
        attribute mass = 100;
        attribute margin = mass * 2;
    }
    part engine : Engine;
    attribute total = engine.mass;
}
";
    let mut s = session(src);
    inline(&mut s, "P::Engine").expect("inlines");
    let out = text(&s);
    assert!(out.contains("attribute margin = mass * 2;"), "{out}");
    assert!(out.contains("attribute total = engine.mass;"), "{out}");
    assert!(s.resolved().resolve_qualified("P::engine::mass").is_some());
}

#[test]
fn dry_run_reports_without_touching_the_session() {
    let src = "package P {
    part def Tool { attribute t; }
    part tool : Tool;
}
";
    let mut s = session(src);
    let d = elem(&mut s, "P::Tool");
    let mut edit = s.edit();
    edit.inline_definition(d);
    let report = edit.check().expect("dry-run succeeds");
    assert!(!report.splices.is_empty());
    assert_eq!(text(&s), src, "session untouched");
}

// ---------------------------------------------------------------------------
// The one-sided inverse: inline(extract(usage)) == usage, byte for byte
// ---------------------------------------------------------------------------

fn upper_first(name: &str) -> String {
    let mut cs = name.chars();
    match cs.next() {
        Some(f) => f.to_uppercase().collect::<String>() + cs.as_str(),
        None => String::new(),
    }
}

fn assert_inverse(src: &str, usage_qn: &str) {
    let mut s = session(src);
    let e = elem(&mut s, usage_qn);
    let mut edit = s.edit();
    edit.extract_definition(e, None);
    edit.commit().expect("extract");
    let def_qn = match usage_qn.rfind("::") {
        Some(i) => format!(
            "{}{}",
            &usage_qn[..i + 2],
            upper_first(
                usage_qn[i + 2..]
                    .split('_')
                    .map(upper_first)
                    .collect::<String>()
                    .as_str()
            )
        ),
        None => upper_first(usage_qn),
    };
    let d = elem(&mut s, &def_qn);
    let mut edit = s.edit();
    edit.inline_definition(d);
    edit.commit()
        .unwrap_or_else(|e| panic!("inline of just-extracted `{def_qn}` failed: {e}"));
    assert_eq!(
        text(&s),
        src,
        "inline(extract({usage_qn})) must be identity"
    );
}

#[test]
fn inline_of_a_just_extracted_definition_is_byte_identical() {
    assert_inverse(
        "package P {
    part def A;
    part engine : A {
        attribute mass = 100; // note rides both moves
        part turbo;
    }
}
",
        "P::engine",
    );
    assert_inverse(
        "package P {
    part box {
        attribute w = 1;
    }
}
",
        "P::box",
    );
    assert_inverse(
        "package P {
    part def Ctx {
        attribute k;
        part u {
            attribute copy = k;
        }
    }
}
",
        "P::Ctx::u",
    );
    assert_inverse(
        "package P {
    package Q { part def A; part def B; }
    part e : Q::A, Q::B {
        attribute x;
    }
}
",
        "P::e",
    );
    assert_inverse(
        "package P {
    attribute def A;
    attribute cfg : A [2] = 42 {
        attribute nested;
    }
}
",
        "P::cfg",
    );
    assert_inverse(
        "package P {
    part engine {
        attribute mass = 100;
    }
    attribute total = engine.mass;
}
",
        "P::engine",
    );
    assert_inverse(
        "package P {
    part fuel_tank { attribute v; }
}
",
        "P::fuel_tank",
    );
}

// ---------------------------------------------------------------------------
// Corpus inverse gate: every successful extract subject round-trips
// ---------------------------------------------------------------------------

#[test]
fn corpus_inverse_gate() {
    let files = sysmlv2_testkit::user_files();
    assert!(files.len() > 100, "expected the corpus checkout");
    let mut round_tripped = 0usize;
    let mut extract_refused = 0usize;
    for path in files {
        let original = std::fs::read_to_string(&path).unwrap();
        let name = path.display().to_string();
        let Ok(mut s) = Session::from_sources(vec![(name.clone(), original.clone())]) else {
            continue;
        };
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
            let Ok(mut s2) = Session::from_sources(vec![(name.clone(), original.clone())]) else {
                break;
            };
            let e = s2
                .resolved()
                .resolve_qualified(&qn)
                .expect("candidate resolves");
            let mut edit = s2.edit();
            edit.extract_definition(e, Some("Zz9InverseGateZz9"));
            if edit.commit().is_err() {
                extract_refused += 1;
                continue; // extract refusals are the extract gate's story
            }
            let def_qn = match qn.rfind("::") {
                Some(i) => format!("{}Zz9InverseGateZz9", &qn[..i + 2]),
                None => "Zz9InverseGateZz9".to_string(),
            };
            let d = s2
                .resolved()
                .resolve_qualified(&def_qn)
                .unwrap_or_else(|| panic!("extracted definition resolves [{name}] {def_qn}"));
            let mut edit = s2.edit();
            edit.inline_definition(d);
            edit.commit()
                .unwrap_or_else(|e| panic!("inverse inline failed [{name}] {qn}: {e}"));
            assert_eq!(
                s2.units().next().unwrap().2,
                original,
                "inline(extract(..)) must be byte-identical [{name}] {qn}"
            );
            round_tripped += 1;
        }
    }
    eprintln!("corpus inverse: {round_tripped} round-tripped, {extract_refused} extract-refused");
    // Ratchet floor from the landing run — every successful extract
    // subject must round-trip; the floor tracks the extract gate's.
    assert!(
        round_tripped >= 240,
        "gate went vacuous: only {round_tripped} inverses succeeded"
    );
}
