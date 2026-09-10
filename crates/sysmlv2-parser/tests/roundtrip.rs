//! JSON round-trip gate: for every corpus file,
//! `emit(parse(print(lift(emit(parse(x)))))) == emit(parse(x))` —
//! i.e. lifting interchange JSON back to an AST and printing it as textual
//! notation preserves the model *exactly* (same elements, same deterministic
//! IDs) through a full re-parse and re-emit.

#![cfg(feature = "json")]

use std::fs;
use sysmlv2_parser::ast::Dialect;
use sysmlv2_parser::json::to_compact_json;
use sysmlv2_parser::lift::from_compact_json;
use sysmlv2_parser::parser::{Parse, parse_kerml_source, parse_source};
use sysmlv2_parser::print::print_source;

fn parse(src: &str, dialect: Dialect) -> Parse {
    match dialect {
        Dialect::Sysml => parse_source(src),
        Dialect::Kerml => parse_kerml_source(src),
    }
}

#[test]
fn corpus_json_roundtrip() {
    let files = sysmlv2_testkit::corpus_files();
    assert!(files.len() > 340, "expected the full corpus checkout");

    let mut failures = Vec::new();
    for path in files {
        let src = fs::read_to_string(&path).unwrap();
        let dialect = if path.extension().and_then(|e| e.to_str()) == Some("kerml") {
            Dialect::Kerml
        } else {
            Dialect::Sysml
        };
        let display = path.display();

        let original = parse(&src, dialect);
        let json1 = to_compact_json(&original.unit);
        let lifted = match from_compact_json(&json1) {
            Ok(l) => l,
            Err(e) => {
                failures.push(format!("{display}: lift failed: {e}"));
                continue;
            }
        };
        if !lifted.errors.is_empty() {
            failures.push(format!("{display}: lift error: {}", lifted.errors[0]));
            continue;
        }
        assert_eq!(lifted.unit.dialect, dialect, "{display}: dialect detection");
        let text = print_source(&lifted.unit);
        let reparsed = parse(&text, dialect);
        if !reparsed.diagnostics.is_empty() {
            failures.push(format!(
                "{display}: lifted text does not parse: {}",
                reparsed.diagnostics[0].message
            ));
            continue;
        }
        if to_compact_json(&reparsed.unit) != json1 {
            failures.push(format!("{display}: JSON changed across the round-trip"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} corpus files failed the JSON round-trip:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Full-form leg of the round-trip gate: lifting a model's *full* JSON
/// must print exactly what the compact leg prints. The full form
/// materializes derived properties (`memberElement`, `memberName`, …)
/// that the lift must ignore — 2026-07-17: view `filter` clauses and
/// positional invocation arguments regressed exactly there.
///
/// One measured loss is normalized away: associations are `isSufficient`
/// at the model level whatever the text spells (INTEROP.md adjudication,
/// 2026-07-16), so the full form cannot recover a KerML `assoc all`
/// keyword — the lift canonicalizes it off, and the comparison drops it
/// from the reference too.
fn drop_assoc_all(text: &str) -> String {
    text.replace("assoc all ", "assoc ")
        .replace("assoc struct all ", "assoc struct ")
}

#[test]
fn corpus_full_json_lift_matches_compact() {
    let files = sysmlv2_testkit::corpus_files();
    let mut failures = Vec::new();
    for path in files {
        let src = fs::read_to_string(&path).unwrap();
        let dialect = if path.extension().and_then(|e| e.to_str()) == Some("kerml") {
            Dialect::Kerml
        } else {
            Dialect::Sysml
        };
        let display = path.display();

        let original = parse(&src, dialect);
        // The compact leg is `corpus_json_roundtrip`'s subject — here it
        // is only the reference text; skip files it cannot produce.
        let compact = to_compact_json(&original.unit);
        let reference = match from_compact_json(&compact) {
            Ok(l) if l.errors.is_empty() => drop_assoc_all(&print_source(&l.unit)),
            _ => continue,
        };

        // The full leg emits independently — emission is deterministic
        // (ambiguous names resolve by declaration order; see
        // tests/determinism.rs), so a divergence between the legs is a
        // real defect, not resolution jitter.
        let full = sysmlv2_parser::full::from_compact_value(
            to_compact_json(&original.unit),
            &std::collections::HashMap::new(),
            true,
        );
        let lifted = match from_compact_json(&full) {
            Ok(l) => l,
            Err(e) => {
                failures.push(format!("{display}: full-form lift failed: {e}"));
                continue;
            }
        };
        if !lifted.errors.is_empty() {
            failures.push(format!(
                "{display}: full-form lift error: {}",
                lifted.errors[0]
            ));
            continue;
        }
        let text = drop_assoc_all(&print_source(&lifted.unit));
        if text != reference {
            let diff = text
                .lines()
                .zip(reference.lines())
                .enumerate()
                .find(|(_, (a, b))| a != b)
                .map(|(i, (a, b))| format!("line {}: {a:?} != {b:?}", i + 1))
                .unwrap_or_else(|| "texts differ in length".to_string());
            failures.push(format!("{display}: full leg diverges — {diff}"));
        }
    }
    assert!(
        failures.is_empty(),
        "{} corpus files failed the full-form round-trip:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// One-source round-trip: emit → lift → print → parse → emit must
/// reproduce the first JSON exactly.
fn assert_roundtrips(src: &str) {
    let original = parse(src, Dialect::Sysml);
    assert!(original.diagnostics.is_empty(), "source parses: {src}");
    let json1 = to_compact_json(&original.unit);
    let lifted = from_compact_json(&json1).expect("lift");
    assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
    let printed = print_source(&lifted.unit);
    let reparsed = parse(&printed, Dialect::Sysml);
    assert!(
        reparsed.diagnostics.is_empty(),
        "regenerated text must re-parse:\n{printed}"
    );
    let json2 = to_compact_json(&reparsed.unit);
    assert_eq!(
        json1, json2,
        "round-trip diverged for:\n{src}\n→\n{printed}"
    );
}

#[test]
fn grammar_round_two_structural_additions_roundtrip() {
    assert_roundtrips(
        "package P {
             item def T;
             flow f of [1] ordered nonunique : T;
             action def A { then [0..1] action next; }
         }",
    );
}

/// Airbus Apollo 11 regressions (external-model study): a
/// name literally `$` must not collide with the `$::` global-root marker,
/// and `Dependency` ends with restricted names must not double-escape.
#[test]
fn dollar_name_is_not_the_root_marker() {
    assert_roundtrips(
        "package P {
             attribute '$';
             attribute cost = 5000000000.0 ['$'];
         }",
    );
}

#[test]
fn recursive_rollup_chain_roundtrips() {
    // The chain member names the very feature being defined (a recursive
    // rollup over children) — it must resolve in the chain context and in
    // its `$::`-rooted round-tripped spelling alike.
    assert_roundtrips(
        "package P {
             part def M {
                 attribute mass = 1;
                 part subs : M;
                 attribute totalMass = mass + sum(subs.totalMass);
             }
         }",
    );
}

/// `import P::*[expr]` bracket filters lower as the implicit anonymous
/// FilterPackage (SysML.xtext `FilterPackage`) owned by the namespace-kind
/// import relationship, and lift back to the bracket spelling — including
/// the cast-member filter idiom `(as T).attr`, whose member resolves in
/// the cast type's scope.
#[test]
fn bracket_filter_import_roundtrips() {
    assert_roundtrips(
        "package P {
             metadata def Safety {
                 attribute isMandatory;
             }
             part vehicle {
                 part seatBelt {
                     @Safety {
                         isMandatory = true;
                     }
                 }
             }
             package Q {
                 public import vehicle::**[@Safety];
             }
             package R {
                 public import all vehicle::*[@Safety and (as Safety).isMandatory];
             }
         }",
    );
}

/// `expose P::**[expr]` uses the same FilterPackage shape under a
/// NamespaceExpose — the nested import is a plain MembershipImport even
/// under an expose (`FilterPackageImport`).
#[test]
fn bracket_filter_expose_roundtrips() {
    assert_roundtrips(
        "package P {
             metadata def Safety;
             part vehicle {
                 part seatBelt {
                     @Safety;
                 }
             }
             view v {
                 expose vehicle::**[@Safety];
             }
         }",
    );
}

#[test]
fn dependency_restricted_names_roundtrip() {
    assert_roundtrips(
        "package P {
             part def 'HLR-R001';
             part def 'FLR-R008';
             dependency 'FLR-R008' to 'HLR-R001';
             dependency from 'SHN-N003' to Missing::'HLR-R002';
         }",
    );
}

/// References through the implied `source`/`target` ends of a binary
/// connect resolve to the connect's own end features, which are unnamed —
/// lift must print them positionally (`source`/`target`) so the reparse
/// lands on the same elements (the Flexo multi_namespace shape).
#[test]
fn binary_connect_implied_end_chains_roundtrip() {
    assert_roundtrips(
        "package C {
             attribute def Cmd;
             part def P {
                 port pout { out attribute cmd : Cmd; }
                 port pin { in attribute cmd : Cmd; }
             }
             part a : P;
             part b : P;
             connect a.pout to b.pin {
                 flow of Cmd from source.cmd to target.cmd;
             }
         }",
    );
}

/// Bare end members canonicalize into connect-part ends, so the implied
/// `source`/`target` names apply to that spelling too.
#[test]
fn bare_end_connection_implied_end_chains_roundtrip() {
    assert_roundtrips(
        "package C {
             attribute def Cmd;
             part def P {
                 port pout { out attribute cmd : Cmd; }
                 port pin { in attribute cmd : Cmd; }
             }
             part a : P;
             part b : P;
             connection c {
                 end ::> a.pout;
                 end ::> b.pin;
                 flow of Cmd from source.cmd to target.cmd;
             }
         }",
    );
}

#[test]
fn full_form_input_normalizes() {
    // Elements flagged isImplied are skipped; derived properties ignored.
    let src = "package P { part def V; part v : V; }";
    let parse = parse_source(src);
    let mut json = to_compact_json(&parse.unit);
    // Simulate a full-form emitter: add derived props and an implied
    // relationship element referencing outside content.
    let arr = json.as_array_mut().unwrap();
    for el in arr.iter_mut() {
        let obj = el.as_object_mut().unwrap();
        obj.insert("qualifiedName".into(), serde_json::json!("Derived::Junk"));
        obj.insert("owner".into(), serde_json::json!({"@id": "0000"}));
    }
    arr.push(serde_json::json!({
        "@id": "11111111-1111-5111-8111-111111111111",
        "@type": "Subclassification",
        "isImplied": true,
        "owningRelatedElement": {"@id": arr[0]["@id"]},
        "ownedRelationship": []
    }));
    let lifted = from_compact_json(&json).unwrap();
    assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
    let text = sysmlv2_parser::print::print_source(&lifted.unit);
    assert!(text.contains("part def V"), "{text}");
    assert!(!text.contains("Junk"));
}

#[test]
fn ownership_closure_slices_lift() {
    // Element-scoped payloads (API query results, element exports) are
    // ownership-closure slices: no root Namespace, the outermost element's
    // owner references point outside the document. They must lift as
    // roots — with or without the dangling member relationship — instead
    // of vanishing behind the missing owner.
    let src = "package Pkg {
        part def Wheel;
        part w : Wheel {
            part hub;
        }
    }
    package Other {
        part def X;
    }";
    let parse = parse_source(src);
    let json = to_compact_json(&parse.unit);
    let arr = json.as_array().unwrap();
    let id_of = |e: &serde_json::Value| e["@id"].as_str().unwrap().to_string();
    let owner_of = |e: &serde_json::Value| {
        ["owningRelationship", "owningRelatedElement"]
            .iter()
            .find_map(|k| {
                e.get(*k)
                    .and_then(|v| v.get("@id"))
                    .and_then(|v| v.as_str())
                    .map(str::to_owned)
            })
    };
    let pkg = arr
        .iter()
        .find(|e| e["@type"] == "Package" && e["declaredName"] == "Pkg")
        .unwrap();
    // Downward ownership closure of Pkg, to fixpoint.
    let mut in_slice: std::collections::HashSet<String> = [id_of(pkg)].into();
    loop {
        let before = in_slice.len();
        for e in arr {
            if owner_of(e).is_some_and(|o| in_slice.contains(&o)) {
                in_slice.insert(id_of(e));
            }
        }
        if in_slice.len() == before {
            break;
        }
    }

    let check = |ids: &std::collections::HashSet<String>, label: &str| {
        let slice: Vec<serde_json::Value> = arr
            .iter()
            .filter(|e| ids.contains(&id_of(e)))
            .cloned()
            .collect();
        let lifted = from_compact_json(&serde_json::Value::Array(slice)).unwrap();
        assert!(lifted.errors.is_empty(), "{label}: {:?}", lifted.errors);
        let text = sysmlv2_parser::print::print_source(&lifted.unit);
        let reparsed = parse_source(&text);
        assert!(
            reparsed.diagnostics.is_empty(),
            "{label}: lifted text does not parse: {text}"
        );
        for expect in ["package Pkg", "part def Wheel", "part w", "part hub"] {
            assert!(
                text.contains(expect),
                "{label}: missing {expect:?} in {text}"
            );
        }
        assert!(!text.contains("Other"), "{label}: slice leaked: {text}");
    };

    // Bare slice: the package's owningRelationship dangles.
    check(&in_slice, "bare slice");
    // Slice carrying its member relationship: the membership's
    // owningRelatedElement (the root namespace) dangles instead.
    let mut with_membership = in_slice.clone();
    if let Some(m) = pkg
        .get("owningRelationship")
        .and_then(|v| v.get("@id"))
        .and_then(|v| v.as_str())
    {
        with_membership.insert(m.to_string());
    }
    check(&with_membership, "slice with member relationship");
}

/// Split-document lift of a cross-document expression chain landing on an
/// *anonymous redefining feature* (`attribute :>> y = 1;`): the feature is
/// findable only by its effective name (KerML 8.2.3.5), which
/// `document_name_map` must derive the same way an in-document lift would.
/// Regression: the chain link was unnameable, so the whole invocation
/// argument chaining through it silently vanished from the lifted text
/// (`f(x.y)` re-emitted as `f()`).
#[test]
fn split_lift_names_anonymous_redefining_chain_targets() {
    use sysmlv2_parser::json::model_to_compact_json;
    use sysmlv2_parser::lift::{
        document_reference_name_map, from_compact_json_with_names, split_documents,
    };
    use sysmlv2_parser::model::Model;

    let sources = [
        (
            "a.sysml",
            "package A {
                part def Base { attribute y; }
                part def X :> Base { attribute :>> y = 1; }
                part x : X;
            }",
        ),
        (
            "b.sysml",
            "package B {
                import A::*;
                calc def f { in a; return a; }
                attribute r = f(x.y);
            }",
        ),
    ];
    let mut model = Model::new();
    for (name, text) in sources {
        model.add_source(name, text);
    }
    assert!(!model.has_errors());
    let json = model_to_compact_json(&model);

    let docs = split_documents(&json).expect("two root namespaces split");
    assert_eq!(docs.len(), 2);
    let names = document_reference_name_map(&json);
    let mut units = Vec::new();
    for (i, (_root, doc)) in docs.iter().enumerate() {
        let lifted = from_compact_json_with_names(doc, &names).expect("lift");
        assert!(
            lifted.errors.is_empty(),
            "document {i} lift errors: {:?}",
            lifted.errors
        );
        units.push(print_source(&lifted.unit));
    }
    // The argument chains through the anonymous redefining attribute,
    // spelled by its effective name.
    assert!(
        units[1].contains("f($::A::x.$::A::X::y)"),
        "invocation argument must survive the split lift: {}",
        units[1]
    );

    // Reparsing the lifted units under the original unit names re-emits
    // the identical element array (same deterministic ids).
    let mut model2 = Model::new();
    for ((name, _), text) in sources.iter().zip(&units) {
        model2.add_source(*name, text);
    }
    assert!(!model2.has_errors());
    assert_eq!(
        model_to_compact_json(&model2),
        json,
        "JSON changed across the split round-trip"
    );
}

/// A reference to a lambda-local parameter (`s` inside
/// `xs->select { in s : T; s istype U }`) is reachable by no global
/// path — the lambda body Expression is anonymous. Lifting with a
/// document name map must not substitute a collapsed `$::`-rooted path
/// that skips the anonymous level: the reparse cannot resolve it, and
/// the reference's membership re-emits as an unresolved `@ref` instead
/// of the resolved `@id` (emit-to-emit drift with identical text).
#[test]
fn lift_with_names_keeps_lambda_parameter_references_relative() {
    use sysmlv2_parser::lift::{document_reference_name_map, from_compact_json_with_names};

    let src = "package P {
        part def T;
        part def U :> T;
        calc def roll {
            in xs : T[0..*];
            return r = xs->select { in s : T; s istype U };
        }
    }";
    let parsed = parse(src, Dialect::Sysml);
    assert!(parsed.diagnostics.is_empty());
    let json = to_compact_json(&parsed.unit);

    let names = document_reference_name_map(&json);
    let lifted = from_compact_json_with_names(&json, &names).expect("lift");
    assert!(lifted.errors.is_empty(), "lift errors: {:?}", lifted.errors);
    let text = print_source(&lifted.unit);
    let reparsed = parse(&text, Dialect::Sysml);
    assert!(
        reparsed.diagnostics.is_empty(),
        "lifted text does not parse: {text}"
    );
    assert_eq!(
        to_compact_json(&reparsed.unit),
        json,
        "JSON changed across the named lift: {text}"
    );
}
