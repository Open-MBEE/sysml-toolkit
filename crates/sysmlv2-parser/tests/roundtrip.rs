//! JSON round-trip gate: for every corpus file,
//! `emit(parse(print(lift(emit(parse(x)))))) == emit(parse(x))` —
//! i.e. lifting interchange JSON back to an AST and printing it as textual
//! notation preserves the model *exactly* (same elements, same deterministic
//! IDs) through a full re-parse and re-emit.

#![cfg(feature = "json")]

use std::fs;
use sysmlv2_parser::ast::{Dialect, MemberKind, UsageDetail, UsageKind};
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
/// that the lift must ignore — view `filter` clauses and
/// positional invocation arguments regressed exactly there.
///
/// One measured loss is normalized away: associations are `isSufficient`
/// at the model level whatever the text spells (see INTEROP.md), so the
/// full form cannot recover a KerML `assoc all` keyword — the lift
/// canonicalizes it off, and the comparison drops it from the reference too.
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

/// A payload whose ownership pointers loop (`A` owns `B`, whose membership
/// owns `A` again) is refused instead of returning a partial model;
/// an expression element that nests itself is caught the same way.
#[test]
fn cyclic_ownership_payload_lifts_with_an_error() {
    use serde_json::json;
    let cyclic = json!([
        {"@id": "root", "@type": "Namespace", "ownedRelationship": [{"@id": "m0"}]},
        {"@id": "m0", "@type": "OwningMembership", "owningRelatedElement": {"@id": "root"},
         "ownedRelatedElement": [{"@id": "a"}]},
        {"@id": "a", "@type": "Package", "declaredName": "A", "owningRelationship": {"@id": "m0"},
         "ownedRelationship": [{"@id": "m1"}]},
        {"@id": "m1", "@type": "OwningMembership", "owningRelatedElement": {"@id": "a"},
         "ownedRelatedElement": [{"@id": "b"}]},
        {"@id": "b", "@type": "Package", "declaredName": "B", "owningRelationship": {"@id": "m1"},
         "ownedRelationship": [{"@id": "m2"}]},
        {"@id": "m2", "@type": "OwningMembership", "owningRelatedElement": {"@id": "b"},
         "ownedRelatedElement": [{"@id": "a"}]},
    ]);
    let Err(sysmlv2_parser::lift::LiftError::Incomplete { errors }) = from_compact_json(&cyclic)
    else {
        panic!("a cycle must refuse the document")
    };
    assert!(errors.iter().any(|e| e.contains("cycle")), "{errors:?}");

    let self_nested = json!([
        {"@id": "root", "@type": "Namespace", "ownedRelationship": [{"@id": "m0"}]},
        {"@id": "m0", "@type": "OwningMembership", "owningRelatedElement": {"@id": "root"},
         "ownedRelatedElement": [{"@id": "x"}]},
        {"@id": "x", "@type": "AttributeUsage", "declaredName": "x", "owningRelationship": {"@id": "m0"},
         "ownedRelationship": [{"@id": "fv"}]},
        {"@id": "fv", "@type": "FeatureValue", "owningRelatedElement": {"@id": "x"},
         "ownedRelatedElement": [{"@id": "e"}]},
        {"@id": "e", "@type": "FeatureReferenceExpression", "owningRelationship": {"@id": "fv"},
         "ownedRelationship": [{"@id": "em"}]},
        {"@id": "em", "@type": "Membership", "owningRelatedElement": {"@id": "e"},
         "ownedRelatedElement": [{"@id": "e"}]},
    ]);
    let Err(sysmlv2_parser::lift::LiftError::Incomplete { errors }) =
        from_compact_json(&self_nested)
    else {
        panic!("a cycle must refuse the document")
    };
    assert!(errors.iter().any(|e| e.contains("cycle")), "{errors:?}");
}

/// Nested packages `depth` levels deep, as compact interchange JSON.
fn nested_packages(depth: usize) -> serde_json::Value {
    use serde_json::json;
    let mut elements = vec![json!({
        "@id": "root", "@type": "Namespace", "ownedRelationship": [{"@id": "m0"}]
    })];
    let mut owner = "root".to_string();
    for i in 0..depth {
        let membership = format!("m{i}");
        let package = format!("p{i}");
        let mut element = json!({
            "@id": package, "@type": "Package", "declaredName": format!("P{i}"),
            "owningRelationship": {"@id": membership}
        });
        if i + 1 < depth {
            element["ownedRelationship"] = json!([{"@id": format!("m{}", i + 1)}]);
        }
        elements.push(json!({
            "@id": membership, "@type": "OwningMembership",
            "owningRelatedElement": {"@id": owner}, "ownedRelatedElement": [{"@id": package}]
        }));
        elements.push(element);
        owner = package;
    }
    serde_json::Value::Array(elements)
}

/// The names of the nested-package chain a lift produced, outermost
/// first — read without recursion, so the reader never costs more stack
/// than the chain it is checking.
fn package_chain(unit: &sysmlv2_parser::ast::SourceUnit) -> Vec<&str> {
    use sysmlv2_parser::ast::{Member, MemberKind, Package};
    fn sole_package(members: &[Member]) -> Option<&Package> {
        match members {
            [only] => match &only.kind {
                MemberKind::Package(package) => Some(package),
                _ => None,
            },
            _ => None,
        }
    }
    let mut names = Vec::new();
    let mut level = sole_package(&unit.members);
    while let Some(package) = level {
        names.push(package.id.name.as_ref().map_or("", |n| n.value.as_str()));
        level = package.body.as_deref().and_then(sole_package);
    }
    names
}

/// Ownership nesting is bounded: a chain far past the limit is refused
/// without exhausting the caller's stack; a chain within the limit lifts
/// completely.
#[test]
fn deep_ownership_chain_lifts_without_overflowing() {
    use sysmlv2_parser::lift::MAX_LIFT_DEPTH;
    // Each package level costs two lift steps: its membership and the
    // package itself.
    let levels = MAX_LIFT_DEPTH / 2;
    let Err(sysmlv2_parser::lift::LiftError::Incomplete { errors }) =
        from_compact_json(&nested_packages(10_000))
    else {
        panic!("an over-budget document must not return a partial AST")
    };
    assert!(
        errors.iter().any(|e| e.contains("deeper than")),
        "{errors:?}"
    );

    // A chain that fits lifts completely, and the whole-list name map
    // walks it too.
    let within = nested_packages(levels - 1);
    let lifted = from_compact_json(&within).expect("well-formed");
    assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
    assert_eq!(package_chain(&lifted.unit).len(), levels - 1);
    let names = sysmlv2_parser::lift::document_name_map(&within);
    assert_eq!(
        names.get("p3").map(Vec::len),
        Some(4),
        "P3 sits four segments below the root"
    );
}

/// One naming rule, several representations: an unnamed feature is named
/// by the feature it redefines, references, or chains to. The lift reads
/// that rule off payload JSON (for the qualified names a cross-document
/// reference prints), the full form derives it over its own element maps
/// (for `name` and `memberName`), and the id derivation runs it as a
/// fixpoint (for named id segments). Feed the same shapes through all
/// three and they must answer the same.
#[test]
fn the_effective_name_rule_agrees_across_its_implementations() {
    let source = "package P {
             part def D { attribute mass; attribute count; }
             part p : D {
                 attribute :>> mass = 1;
                 attribute :>> count = 2;
             }
             part q : D {
                 attribute :>> mass = 3;
             }
         }";
    let compact = to_compact_json(&parse(source, Dialect::Sysml).unit);
    let elements = compact.as_array().expect("a flat element array");

    // The anonymous redefining attributes, by the id the payload gives
    // them, with the name each is expected to be findable by.
    let anonymous: Vec<(&str, String)> = elements
        .iter()
        .filter(|e| e["@type"] == "AttributeUsage" && e["declaredName"].as_str().is_none())
        .map(|e| {
            let redefined = e["ownedRelationship"]
                .as_array()
                .expect("owned relationships")
                .iter()
                .filter_map(|r| elements.iter().find(|x| x["@id"] == r["@id"]))
                .find(|r| r["@type"] == "Redefinition")
                .expect("a redefinition");
            let target = redefined["redefinedFeature"]["@id"]
                .as_str()
                .expect("an in-document target");
            let name = elements
                .iter()
                .find(|x| x["@id"] == target)
                .expect("the redefined attribute")["declaredName"]
                .as_str()
                .expect("a declared name")
                .to_string();
            (e["@id"].as_str().expect("an id"), name)
        })
        .collect();
    assert_eq!(anonymous.len(), 3, "three anonymous redefiners");

    // The lift's reading: the last segment of the whole-list name map.
    let lifted_names = sysmlv2_parser::lift::document_name_map(&compact);
    // The full form's reading: the materialized `name` property.
    let full = sysmlv2_parser::full::from_compact_value(
        compact.clone(),
        &std::collections::HashMap::new(),
        true,
    );
    let full_elements = full.as_array().expect("a flat element array");
    // The id derivation's reading: the named segment of the path.
    let paths = sysmlv2_parser::ids::segment_paths(&compact, &|_| None).expect("well-formed");

    for (id, expected) in anonymous {
        assert_eq!(
            lifted_names.get(id).and_then(|segments| segments.last()),
            Some(&expected),
            "the lift names {id}"
        );
        let full_element = full_elements
            .iter()
            .find(|e| e["@id"] == id)
            .expect("the same element in the full form");
        assert_eq!(
            full_element["name"].as_str(),
            Some(expected.as_str()),
            "the full form names {id}"
        );
        let index = elements
            .iter()
            .position(|e| e["@id"] == id)
            .expect("payload order");
        let (_, path) = paths[index].as_ref().expect("a reachable element");
        assert_eq!(
            path.rsplit('/').next(),
            Some(format!("::{expected}").as_str()),
            "the id derivation names {id} — {path}"
        );
    }
}

/// Remove the element `id` and everything it owns from a compact-form
/// element array.
fn remove_subtree(arr: &mut Vec<serde_json::Value>, id: &str) {
    let mut pending = vec![id.to_string()];
    while let Some(id) = pending.pop() {
        let Some(i) = arr.iter().position(|e| e["@id"] == id.as_str()) else {
            continue;
        };
        let el = arr.remove(i);
        for key in ["ownedRelationship", "ownedRelatedElement"] {
            if let Some(children) = el[key].as_array() {
                pending.extend(
                    children
                        .iter()
                        .filter_map(|c| c["@id"].as_str().map(str::to_owned)),
                );
            }
        }
    }
}

/// A binding connector with a single end (a partial document: the other
/// end's membership is missing) lifts with an error entry, and prints text
/// that parses: the notation spells a binding's ends as a pair and has no
/// form for one, so the end is left unspelled rather than printed as
/// `bind a;`, which does not parse.
///
/// What is lost, pinned below so it is not lost silently: the SysML
/// grammar requires the `bind` clause after the `binding` keyword, so
/// nothing in that dialect spells a binding whose ends are not a pair —
/// the binding does not survive, and re-lifting the printed text gives an
/// ordinary usage rather than a connector. What does survive is the
/// member, as its declaration alone, so the name, the short name and the
/// typing come through; the end comes with it, spelled as an `end ::> …;`
/// body member; and a connector with nothing declared at all prints `ref`
/// rather than a bare terminator.
#[test]
fn one_ended_binding_keeps_the_member_it_cannot_spell() {
    let src = "package P { part def B; part a; part b; binding <b1> bd : B bind a = b; }";
    let text = print_one_ended_binding(src);
    let member = text
        .lines()
        .map(str::trim)
        .find(|l| l.contains("bd"))
        .unwrap_or_else(|| panic!("{text}"));
    assert!(member.starts_with("<b1> bd : "), "{text}");
    assert!(
        !member.contains("binding") && !member.contains("bind "),
        "{text}"
    );
    let reparsed = parse_source(&text);
    assert!(
        reparsed.diagnostics.is_empty(),
        "{text}: {:#?}",
        reparsed.diagnostics
    );
    let MemberKind::Package(p) = &reparsed.unit.members[0].kind else {
        panic!("{:?}", reparsed.unit.members[0].kind)
    };
    let kept = p
        .body
        .as_ref()
        .unwrap()
        .iter()
        .find_map(|m| match &m.kind {
            MemberKind::Usage(u)
                if u.declaration.id.name.as_ref().map(|n| n.value.as_str()) == Some("bd") =>
            {
                Some(u)
            }
            _ => None,
        })
        .expect("the member survives");
    assert_eq!(
        kept.kind,
        UsageKind::Default,
        "the binding is not spelled, the member is"
    );
    assert_eq!(end_members(kept), 1, "the end survives: {text}");

    // With nothing declared there is no head, and a member whose whole
    // text is a body does not parse, so the keyword-less usage spells
    // itself out — indented where it belongs, with its end kept.
    let text = print_one_ended_binding("package P { part a; part b; bind a = b; part z; }");
    assert!(text.contains("\n    ref {\n"), "{text}");
    let reparsed = parse_source(&text);
    assert!(
        reparsed.diagnostics.is_empty(),
        "{text}: {:#?}",
        reparsed.diagnostics
    );
    let MemberKind::Package(p) = &reparsed.unit.members[0].kind else {
        panic!("{:?}", reparsed.unit.members[0].kind)
    };
    let kept = p
        .body
        .as_ref()
        .unwrap()
        .iter()
        .find_map(|m| match &m.kind {
            MemberKind::Usage(u) if u.kind == UsageKind::Ref => Some(u),
            _ => None,
        })
        .expect("the member survives");
    assert_eq!(end_members(kept), 1, "the end survives: {text}");
}

/// How many of a usage's body members are ends.
fn end_members(u: &sysmlv2_parser::ast::Usage) -> usize {
    u.body
        .iter()
        .flatten()
        .filter(|m| matches!(&m.kind, MemberKind::Usage(e) if e.prefix.is_end))
        .count()
}

/// Lift `src`, drop one of its binding's two ends, and print what is left.
fn print_one_ended_binding(src: &str) -> String {
    let mut json = to_compact_json(&parse_source(src).unit);
    let arr = json.as_array_mut().unwrap();
    let types: std::collections::HashMap<String, String> = arr
        .iter()
        .map(|e| {
            (
                e["@id"].as_str().unwrap().to_owned(),
                e["@type"].as_str().unwrap().to_owned(),
            )
        })
        .collect();
    let binding = arr
        .iter()
        .position(|e| e["@type"] == "BindingConnectorAsUsage")
        .expect("binding element");
    let rels = arr[binding]["ownedRelationship"].as_array_mut().unwrap();
    let ends: Vec<String> = rels
        .iter()
        .filter_map(|r| r["@id"].as_str())
        .filter(|id| types[*id] == "EndFeatureMembership")
        .map(str::to_owned)
        .collect();
    assert_eq!(ends.len(), 2, "{types:#?}");
    let dropped = ends[1].clone();
    rels.retain(|r| r["@id"] != dropped.as_str());
    remove_subtree(arr, &dropped);

    let lifted = from_compact_json(&json).unwrap();
    assert!(
        lifted
            .errors
            .iter()
            .any(|e| e.contains("binding connector") && e.contains("1 end(s)")),
        "{:?}",
        lifted.errors
    );
    let text = print_source(&lifted.unit);
    // The `bind` clause, wherever it sits: a declared binding spells the
    // keyword and the declaration before it.
    let bind_line = |text: &str| {
        text.lines()
            .map(str::trim)
            .find(|l| l.starts_with("bind ") || l.contains(" bind "))
            .map(str::to_owned)
    };
    assert!(bind_line(&text).is_none(), "{text}");
    // The one-ended usage is no longer a binding detail: the invariant
    // that a binding detail has two ends holds for lifted trees.
    let MemberKind::Package(p) = &lifted.unit.members[0].kind else {
        panic!("{:?}", lifted.unit.members[0].kind)
    };
    let usage = p
        .body
        .as_ref()
        .unwrap()
        .iter()
        .find_map(|m| match &m.kind {
            MemberKind::Usage(u) if u.kind == UsageKind::Binding => Some(u),
            _ => None,
        })
        .expect("binding usage");
    assert!(matches!(&usage.detail, UsageDetail::Connector { ends } if ends.len() == 1));
    // Lifting the intact document still yields the two-ended binding.
    let intact = from_compact_json(&to_compact_json(&parse_source(src).unit)).unwrap();
    assert!(intact.errors.is_empty(), "{:?}", intact.errors);
    let intact_text = print_source(&intact.unit);
    let line = bind_line(&intact_text).unwrap_or_else(|| panic!("{intact_text}"));
    assert!(
        line.contains(" = ") && line.ends_with("b;"),
        "{intact_text}"
    );
    text
}

/// Long expressions use the parser's expression budget independently of
/// structural nesting. Compact and full form must retain every operand.
#[test]
fn expression_budget_roundtrips_without_changing_operands() {
    sysmlv2_parser::parser::on_parsing_stack(
        "expression-roundtrip",
        |e| panic!("cannot reserve parsing stack: {e}"),
        || {
            for operators in [399, sysmlv2_parser::parser::MAX_EXPR_OPERATORS as usize] {
                let expression = vec!["1"; operators + 1].join(" + ");
                let source = format!("attribute a = {expression};\n");
                let parsed = parse_source(&source);
                assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                let compact = to_compact_json(&parsed.unit);
                let full = sysmlv2_parser::full::to_full_json(&parsed.unit);
                assert_eq!(
                    compact.as_array().unwrap().len(),
                    full.as_array().unwrap().len()
                );
                for json in [&compact, &full] {
                    let lifted = from_compact_json(json).unwrap_or_else(|e| panic!("{e}"));
                    assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
                    let reparsed = parse_source(&print_source(&lifted.unit));
                    assert!(
                        reparsed.diagnostics.is_empty(),
                        "{:?}",
                        reparsed.diagnostics
                    );
                    assert_eq!(to_compact_json(&reparsed.unit), compact);
                }
            }
        },
    );
}

/// Full-form enrichment retains owned elements even when no source model
/// can represent them. The array-level fallback must not delete a payload.
#[test]
fn full_form_preserves_elements_the_lifter_cannot_reconstruct() {
    let parsed = parse_source("attribute a = 1 + 2;");
    let mut compact = to_compact_json(&parsed.unit);
    for element in compact.as_array_mut().unwrap() {
        if element["@type"] == "LiteralInteger" && element["value"] == 1 {
            element["@type"] = "Expression".into();
            element["declaredName"] = "foreignExpression".into();
            element.as_object_mut().unwrap().remove("value");
        }
    }
    let full = sysmlv2_parser::full::from_compact_value(compact.clone(), &Default::default(), true);
    for element in compact.as_array().unwrap() {
        let output = full
            .as_array()
            .unwrap()
            .iter()
            .find(|e| e["@id"] == element["@id"])
            .expect("every input element survives full-form enrichment");
        assert_eq!(output["@type"], element["@type"]);
        assert_eq!(output["declaredName"], element["declaredName"]);
        assert_eq!(output["ownedRelationship"], element["ownedRelationship"]);
    }
}
