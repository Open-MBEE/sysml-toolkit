//! Multi-file model tests: cross-file and standard-library resolution.

use sysmlv2_parser::model::Model;

#[cfg(feature = "json")]
use serde_json::Value;
#[cfg(feature = "json")]
use sysmlv2_parser::json::model_to_compact_json;

#[cfg(feature = "json")]
fn emit(model: &Model) -> Vec<Value> {
    let Value::Array(elements) = model_to_compact_json(model) else {
        panic!("expected a flat element array")
    };
    elements
}

#[cfg(feature = "json")]
fn count_refs(elements: &[Value]) -> (usize, usize) {
    let text = serde_json::to_string(elements).unwrap();
    (
        text.matches("\"@id\"").count(),
        text.matches("\"@ref\"").count(),
    )
}

#[cfg(feature = "json")]
#[test]
fn cross_file_resolution() {
    let mut model = Model::new();
    model.add_source("lib.sysml", "package Parts { part def Wheel; }");
    model.add_source(
        "car.sysml",
        "package Car {
            import Parts::*;
            part w : Wheel;
         }",
    );
    assert!(!model.has_errors());
    let elements = emit(&model);
    let (_, unresolved) = count_refs(&elements);
    assert_eq!(unresolved, 0, "cross-file reference must resolve");
    // Both files' elements are present (neither is a library).
    let names: Vec<_> = elements
        .iter()
        .filter_map(|e| e["declaredName"].as_str())
        .collect();
    assert!(names.contains(&"Wheel") && names.contains(&"Car"));
}

#[cfg(feature = "json")]
#[test]
fn namespace_visibility_controls_qualified_and_imported_lookup() {
    let mut model = Model::new();
    model.add_source(
        "visibility.sysml",
        "package A {
            private part def Hidden;
            protected part def Protected;
            public part def Shown;
        }
        package Qualified {
            part hidden : A::Hidden;
            part prot : A::Protected;
            part shown : A::Shown;
        }
        package Imported {
            private import A::*;
            part hidden : Hidden;
            part prot : Protected;
            part shown : Shown;
        }
        package ImportedAll {
            private import all A::*;
            part hidden : Hidden;
            part prot : Protected;
            part shown : Shown;
        }",
    );
    assert!(!model.has_errors());
    let report = sysmlv2_parser::json::model_resolution_report(&model);
    let mut unresolved: Vec<String> = report
        .unresolved
        .iter()
        .map(|(_, qn)| qn.to_display_string())
        .collect();
    unresolved.sort();
    assert_eq!(
        unresolved,
        ["A::Hidden", "A::Protected", "Hidden", "Protected"],
        "ordinary external access/imports expose only public memberships"
    );
    assert!(report.ambiguous.is_empty(), "{:#?}", report.ambiguous);
}

#[cfg(feature = "json")]
#[test]
fn protected_members_are_visible_to_specializers_but_private_members_are_not() {
    let mut model = Model::new();
    model.add_source(
        "protected.kerml",
        "package P {
            class Base {
                private feature secret;
                protected feature inherited;
            }
            class Derived specializes Base {
                feature redefines inherited;
                feature redefines secret;
            }
            feature outsideProtected : Base::inherited;
            feature outsidePrivate : Base::secret;
        }",
    );
    assert!(!model.has_errors());
    let report = sysmlv2_parser::json::model_resolution_report(&model);
    let mut unresolved: Vec<String> = report
        .unresolved
        .iter()
        .map(|(_, qn)| qn.to_display_string())
        .collect();
    unresolved.sort();
    assert_eq!(
        unresolved,
        ["Base::inherited", "Base::secret", "secret"],
        "a specializer inherits protected, never private; external qualified access sees neither"
    );
    let mut resolved = sysmlv2_parser::json::ResolvedModel::build(&model);
    assert!(
        resolved.resolve_qualified("P::Base::secret").is_some(),
        "absolute tooling paths can still address private model elements"
    );
}

#[cfg(feature = "json")]
#[test]
fn same_precedence_import_candidates_are_ambiguous() {
    let mut model = Model::new();
    model.add_source(
        "ambiguous.sysml",
        "package A { part def X; }
         package B { part def X; }
         package C {
             private import A::*;
             private import B::*;
             part value : X;
         }",
    );
    assert!(!model.has_errors());
    let report = sysmlv2_parser::json::model_resolution_report(&model);
    assert!(
        report.unresolved.is_empty(),
        "ambiguity must not be downgraded to unresolved: {:#?}",
        report.unresolved
    );
    assert_eq!(report.ambiguous.len(), 1, "{:#?}", report.ambiguous);
    assert_eq!(report.ambiguous[0].1.to_display_string(), "X");

    let diagnostics = sysmlv2_parser::check::validate_model(&model);
    assert_eq!(diagnostics.len(), 1, "{diagnostics:#?}");
    assert!(
        diagnostics[0].1.message.contains("ambiguous reference `X`"),
        "{diagnostics:#?}"
    );
}

/// The two ends of a binary connector-family usage implicitly redefine
/// `source`/`target` (the `Connections::BinaryConnection` ends), so those
/// names resolve in the usage's body to the usage's own end features, and
/// chain members resolve through the connected feature — no library needed
/// (the Flexo example `connect a.p to b.p { flow … from source.x to target.y; }`).
#[cfg(feature = "json")]
#[test]
fn binary_connect_implied_source_target_ends() {
    let mut model = Model::new();
    model.add_source(
        "connect.sysml",
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
    assert!(!model.has_errors());
    let elements = emit(&model);
    let (_, unresolved) = count_refs(&elements);
    assert_eq!(unresolved, 0, "source/target chains must resolve");

    // The flow-end chains root at the connect's *own* end features.
    let connection = elements
        .iter()
        .find(|e| e["@type"] == "ConnectionUsage")
        .expect("a ConnectionUsage");
    let end_ids: Vec<&str> = elements
        .iter()
        .filter(|e| {
            e["@type"] == "EndFeatureMembership"
                && e["owningRelatedElement"]["@id"] == connection["@id"]
        })
        .map(|e| e["ownedRelatedElement"][0]["@id"].as_str().unwrap())
        .collect();
    assert_eq!(end_ids.len(), 2, "two connect ends");
    // Pilot FlowEnd shape: each flow end's prefix ReferenceSubsetting
    // references one of the connect's own end features.
    let prefix_targets: Vec<&str> = elements
        .iter()
        .filter(|e| e["@type"] == "ReferenceSubsetting")
        .filter_map(|e| e["referencedFeature"]["@id"].as_str())
        .filter(|id| end_ids.contains(id))
        .collect();
    assert_eq!(
        prefix_targets.len(),
        2,
        "one flow-end prefix per implied end (source and target)"
    );
}

/// A specialization target written as a feature chain contributes the
/// chain's *last* link as an inherited-member base: `part m :> a.b { … }`
/// finds `b`'s members inside `m`'s body exactly as a plain-name target
/// would. Both the sibling-scope spelling and a package-level subsetting
/// whose chain starts with a qualified name must work — chain targets
/// were once skipped entirely, leaving redefinitions of the landed
/// feature's members unresolved.
#[test]
fn chain_specialization_target_contributes_inherited_members() {
    let mut model = Model::new();
    model.add_source(
        "chain.sysml",
        "package Q {
            part def Housing {
                part slot : Frame;
            }
            part def Frame {
                part cell {
                    attribute rating;
                }
            }
            part def Assembly :> Housing {
                part merged :> slot.cell {
                    attribute :>> rating = 2;
                }
            }
            part standalone :> Housing::slot.cell : Housing {
                attribute :>> rating = 3;
            }
        }",
    );
    assert!(!model.has_errors());
    let unresolved: Vec<String> = sysmlv2_parser::check::validate_model(&model)
        .into_iter()
        .filter(|(_, d)| d.message.starts_with("unresolved"))
        .map(|(_, d)| d.message)
        .collect();
    assert!(
        unresolved.is_empty(),
        "members of a chain-written specialization target must be inherited: {unresolved:?}"
    );
}

/// A transition's trigger payload parameter is a feature of the
/// transition itself: chains rooted at the transition (`hop.pay.level`)
/// resolve through it, with the payload's typing supplying the member
/// lookup.
#[test]
fn transition_payload_is_a_transition_member() {
    let mut model = Model::new();
    model.add_source(
        "tp.sysml",
        "package TP {
            attribute def Msg { attribute level; }
            part hub;
            state def Machine {
                state idle;
                state busy {
                    do send new Msg(hop.pay.level) to hub;
                }
                transition hop
                    first idle
                    accept pay : Msg
                    then busy;
            }
        }",
    );
    assert!(!model.has_errors());
    let unresolved: Vec<String> = sysmlv2_parser::check::validate_model(&model)
        .into_iter()
        .filter(|(_, d)| d.message.starts_with("unresolved"))
        .map(|(_, d)| d.message)
        .collect();
    assert!(
        unresolved.is_empty(),
        "the payload must be reachable as a transition member: {unresolved:?}"
    );
}

/// A chain member the chain target does *not* reach must stay unresolved
/// even when an unrelated same-named element is lexically visible from
/// the expression — the lexical fallback once silently captured such
/// decoys (a payload name landed on a sibling state), rebinding the
/// chain to an element it cannot legally denote.
#[test]
fn chain_member_fallback_must_agree_with_the_chain() {
    let mut model = Model::new();
    model.add_source(
        "decoy.sysml",
        "package TQ {
            attribute def Msg { attribute level; }
            part hub;
            state def Machine {
                state idle;
                state busy {
                    do send new Msg(hop.pay.level) to hub;
                }
                transition hop
                    first idle
                    accept go : Msg
                    then busy;
                state pay;
            }
        }",
    );
    assert!(!model.has_errors());
    let unresolved: Vec<String> = sysmlv2_parser::check::validate_model(&model)
        .into_iter()
        .filter(|(_, d)| d.message.starts_with("unresolved"))
        .map(|(_, d)| d.message)
        .collect();
    // The step itself warns, plus the cascading member behind it — but
    // never a silent hit on the decoy.
    assert!(
        unresolved.iter().any(|m| m.contains("`pay`")),
        "`hop.pay` must not capture the sibling state `pay`: {unresolved:?}"
    );
}

/// Implied library bases are `$::`-rooted: a user package that shares a
/// library package's name must not shadow it (a nested `package Actions`
/// once hid `Actions::actions`, losing every inherited action member such
/// as `start`).
#[test]
fn implied_library_bases_survive_user_shadowing() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "shadow.sysml",
        "package Top {
            package Actions {
                action a {
                    action b;
                    first start then b;
                }
            }
         }",
    );
    assert!(!model.has_errors());
    let unresolved: Vec<String> = sysmlv2_parser::check::validate_model(&model)
        .into_iter()
        .filter(|(_, d)| d.message.starts_with("unresolved"))
        .map(|(_, d)| d.message)
        .collect();
    assert!(
        unresolved.is_empty(),
        "`start` must resolve through the implied Actions::actions base: {unresolved:?}"
    );
}

#[cfg(feature = "json")]
#[test]
fn library_units_resolve_but_are_not_emitted() {
    let mut model = Model::new();
    model.add_library_source(
        "ScalarValues.kerml",
        "standard library package ScalarValues {
            abstract datatype Real;
            abstract datatype Integer specializes Real;
         }",
    );
    model.add_source(
        "m.sysml",
        "package M {
            import ScalarValues::*;
            attribute mass : Real = 10;
         }",
    );
    let elements = emit(&model);
    // Library elements are not serialized...
    assert!(
        elements
            .iter()
            .all(|e| e["declaredName"] != "ScalarValues" && e["@type"] != "LibraryPackage")
    );
    // ...but the typing reference resolved to an @id, not an @ref.
    let typing = elements
        .iter()
        .find(|e| e["@type"] == "FeatureTyping")
        .expect("typing");
    assert!(
        typing["type"].get("@id").is_some(),
        "library reference must resolve to an @id: {typing}"
    );
    let (_, unresolved) = count_refs(&elements);
    assert_eq!(unresolved, 0);
}

#[cfg(feature = "json")]
#[test]
fn vendored_standard_library_resolution() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    let loaded = model.load_library_dir(&lib).unwrap();
    assert!(loaded > 90, "expected the full library, got {loaded} files");

    model.add_source(
        "vehicle.sysml",
        "package Demo {
            import ScalarValues::*;
            import SI::*;
            part def Vehicle {
                attribute mass : Real = 1500.0;
                attribute speed : Real;
            }
            part car : Vehicle;
         }",
    );
    assert!(!model.has_errors());
    let elements = emit(&model);
    let (ids, unresolved) = count_refs(&elements);
    assert!(ids > 10);
    assert_eq!(
        unresolved, 0,
        "all standard-library references should resolve"
    );

    // The typing of `mass` points at ScalarValues::Real — a stable ID that
    // any other model built against the same library also gets.
    let typings: Vec<_> = elements
        .iter()
        .filter(|e| e["@type"] == "FeatureTyping" && e["type"].get("@id").is_some())
        .collect();
    assert!(!typings.is_empty());
}

/// References into standard-library packages must carry the *normative*
/// name-based UUIDs of KerML clause 9.1. Expected values below are the
/// published elementIds from the OMG XMI serializations
/// (SysML-v2-Release `sysml.library.xmi`).
#[cfg(feature = "json")]
#[test]
fn normative_library_element_ids() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "m.sysml",
        "package M {
            import ScalarValues::*;
            attribute m1 : Real;
            part p1 : Parts::Part;
         }",
    );
    let elements = emit(&model);

    // import ScalarValues::* → uuid5(NameSpace_URL,
    //   "https://www.omg.org/spec/KerML/ScalarValues")
    let ns_import = elements
        .iter()
        .find(|e| e["@type"] == "NamespaceImport")
        .unwrap();
    assert_eq!(
        ns_import["importedNamespace"]["@id"], "40bb440c-5036-58e1-8675-5afccb8b8f1d",
        "ScalarValues package must have its normative ID"
    );

    // m1 : Real → uuid5(ScalarValues-pkg-uuid, "ScalarValues::Real")
    // p1 : Parts::Part → uuid5(Parts-pkg-uuid, "Parts::Part")
    let typing_ids: Vec<&str> = elements
        .iter()
        .filter(|e| e["@type"] == "FeatureTyping")
        .filter_map(|e| e["type"]["@id"].as_str())
        .collect();
    assert!(
        typing_ids.contains(&"14c0aa22-5489-59b5-b438-ded26e83ba31"),
        "ScalarValues::Real must have its normative ID: {typing_ids:?}"
    );
    assert!(
        typing_ids.contains(&"0774a545-39e3-5bc1-9607-63beabc6bf65"),
        "Parts::Part must have its normative ID: {typing_ids:?}"
    );
}

#[test]
fn model_collects_diagnostics_per_unit() {
    let mut model = Model::new();
    model.add_source("good.sysml", "package P;");
    model.add_source("bad.sysml", "package Q { part x : ; }");
    assert!(model.has_errors());
    assert!(model.units()[0].diagnostics.is_empty());
    assert!(!model.units()[1].diagnostics.is_empty());
}

/// Import filters restrict what an import makes visible: `import
/// P::*[@Safety]` exposes only members satisfying the filter (metadata
/// classification), and a package's `filter @Safety;` members apply to
/// every import of that package (SysML 7.2.5, ElementFilterMembership).
#[cfg(feature = "json")]
#[test]
fn import_filters_restrict_visibility() {
    let mut model = Model::new();
    model.add_source(
        "filtered.sysml",
        "package Example {
            metadata def Safety;
            package Lib {
                part def SafePart { @Safety; }
                part def PlainPart;
            }
            package User {
                private import Lib::*[@Safety];
                part matching : SafePart;
                part hidden : PlainPart;
            }
         }",
    );
    assert!(!model.has_errors());
    let elements = emit(&model);
    let text = serde_json::to_string(&elements).unwrap();
    // The matching member resolves through the filtered import; the
    // non-matching one must not.
    assert!(
        !text.contains("\"@ref\": \"SafePart\"") && !text.contains("\"@ref\":\"SafePart\""),
        "@Safety-annotated member must stay visible through the filtered import"
    );
    let report = sysmlv2_parser::json::model_resolution_report(&model);
    let unresolved: Vec<String> = report
        .unresolved
        .iter()
        .map(|(_, qn)| qn.to_display_string())
        .collect();
    assert_eq!(
        unresolved,
        vec!["PlainPart"],
        "the non-matching member must not resolve through the filtered import"
    );
}

/// The `filter expr;` statement form (a package-owned
/// ElementFilterMembership) filters recursive imports the same way, and
/// `(as M).attr` conditions read boolean metadata attributes.
#[cfg(feature = "json")]
#[test]
fn filter_members_apply_to_package_imports() {
    let mut model = Model::new();
    model.add_source(
        "vehicle.sysml",
        "package Example {
            metadata def Safety { attribute isMandatory; }
            part vehicle {
                part seatBelt { @Safety { isMandatory = true; } }
                part driverAirBag { @Safety { isMandatory = false; } }
                part alarm;
            }
            package SafetyFeatures {
                public import vehicle::**;
                filter @Safety;
            }
            package MandatoryFeatures {
                public import vehicle::**[@Safety and (as Safety).isMandatory];
            }
         }",
    );
    assert!(!model.has_errors());
    let mut rm = sysmlv2_parser::json::ResolvedModel::build(&model);
    for (qn, expect) in [
        // `filter @Safety` keeps annotated members, hides the rest.
        ("Example::SafetyFeatures::seatBelt", true),
        ("Example::SafetyFeatures::driverAirBag", true),
        ("Example::SafetyFeatures::alarm", false),
        // The conjunction with `(as Safety).isMandatory` also reads the
        // annotation's boolean attribute.
        ("Example::MandatoryFeatures::seatBelt", true),
        ("Example::MandatoryFeatures::driverAirBag", false),
        ("Example::MandatoryFeatures::alarm", false),
    ] {
        assert_eq!(
            rm.resolve_qualified(qn).is_some(),
            expect,
            "{qn} should{} resolve",
            if expect { "" } else { " not" }
        );
    }
}

/// `@M` against a `metaclass` target is a reflection test on the
/// candidate's own metaclass — decidable when the metaclass package names
/// the candidate's metaclass.
#[cfg(feature = "json")]
#[test]
fn metaclass_filters_test_the_candidates_metaclass() {
    let mut model = Model::new();
    model.add_source(
        "reflect.kerml",
        "package Reflect {
            metaclass PartUsage;
            metaclass PartDefinition;
         }",
    );
    model.add_source(
        "user.sysml",
        "package Example {
            package Stuff {
                part def D;
                part p;
            }
            package PartsOnly {
                public import Stuff::*[@Reflect::PartUsage];
            }
         }",
    );
    assert!(!model.has_errors());
    let mut rm = sysmlv2_parser::json::ResolvedModel::build(&model);
    assert!(
        rm.resolve_qualified("Example::PartsOnly::p").is_some(),
        "a part usage must pass the @PartUsage metaclass filter"
    );
    assert!(
        rm.resolve_qualified("Example::PartsOnly::D").is_none(),
        "a part definition must be hidden by the @PartUsage metaclass filter"
    );
}

/// `import vehicle::**` — a recursive *membership* import must make the
/// target's nested members visible through the importing package.
/// (Regression: resolving the entry's own target through the entry
/// recursed to the depth guard and permanently cached an empty
/// import-scope set for the package.)
#[cfg(feature = "json")]
#[test]
fn recursive_membership_import_visible_from_outside() {
    let mut model = Model::new();
    model.add_source(
        "rec.sysml",
        "package Example {
            package vehicle { part seatBelt; }
            package SF { public import vehicle::**; }
            part s1 : SF::seatBelt;
         }",
    );
    assert!(!model.has_errors());
    let elements = emit(&model);
    let (_, unresolved) = count_refs(&elements);
    assert_eq!(
        unresolved, 0,
        "SF::seatBelt must resolve through the recursive import"
    );
}

/// A namespace import's own target must not resolve through the import
/// itself: with `import Domain::*;` where package `Domain` owns a member
/// also named `Domain`, the fixpoint's second pass once captured the member
/// through the import's first-pass result — importing the part def's body
/// instead of the package's. The serialized `importedNamespace` must stay
/// the package, while a plain *reference* to the imported name prefers the
/// imported member (imported memberships shadow outer namespaces).
/// Found via GfSE/SysML-v2-Models (`package Domain`
/// owning `part def Domain`, EveOnlineMiningFrigate).
#[cfg(feature = "json")]
#[test]
fn namespace_import_does_not_capture_its_own_target() {
    let mut model = Model::new();
    model.add_source(
        "shadow.sysml",
        "package Domain {
            part def Domain {
                part def Inner;
            }
        }
        package User {
            private import Domain::*;
            part q : Domain;
            part r : Domain::Inner;
        }",
    );
    assert!(!model.has_errors());
    let elements = emit(&model);
    let (_, unresolved) = count_refs(&elements);
    assert_eq!(unresolved, 0, "q and r must resolve");
    let id_of = |ty: &str| {
        elements
            .iter()
            .find(|e| e["@type"] == ty && e["declaredName"] == "Domain")
            .and_then(|e| e["@id"].as_str())
            .unwrap()
            .to_owned()
    };
    let (package, part_def) = (id_of("Package"), id_of("PartDefinition"));
    let import = elements
        .iter()
        .find(|e| e["@type"] == "NamespaceImport")
        .expect("the import lowers");
    assert_eq!(
        import["importedNamespace"]["@id"].as_str(),
        Some(package.as_str()),
        "the import's own target is the package"
    );
    let typing = elements
        .iter()
        .find(|e| e["@type"] == "FeatureTyping" && e["type"]["@id"] == part_def.clone())
        .is_some();
    assert!(
        typing,
        "q's typing resolves to the imported part def (the nearer name)"
    );
}

/// The first segment of a qualified reference commits to the nearest
/// binding without backtracking: with `import Domain::*;` making the inner
/// `part def Domain` visible, `Domain::PilotPod` resolves `Domain` to the
/// part def and fails on `PilotPod` — even though the root package `Domain`
/// has that member (KerML resolution commits per segment; the GfSE Eve
/// corpus exercises exactly this shape).
#[cfg(feature = "json")]
#[test]
fn imported_member_shadows_package_for_qualified_refs() {
    let mut model = Model::new();
    model.add_source(
        "shadow.sysml",
        "package Domain {
            part def Domain;
            part def PilotPod;
        }
        package User {
            private import Domain::*;
            part p : Domain::PilotPod;
        }",
    );
    assert!(!model.has_errors());
    let elements = emit(&model);
    let (_, unresolved) = count_refs(&elements);
    assert_eq!(
        unresolved, 1,
        "Domain::PilotPod stays unresolved — the imported part def shadows the package"
    );
}

/// Import caches must not depend on the recursion depth of whichever lookup
/// first touches a scope. A reference that legitimately exhausts the depth
/// guard (here: a member 30 namespace-import hops away) used to compute the
/// intermediate scopes' import caches at that exhausted depth, permanently
/// poisoning them with empty import sets — so whether a *shallow* reference
/// through the same scopes resolved depended on pending-resolution order
/// (on the GfSE Eve corpus, on CLI file order). The deep probe stays
/// unresolved; the shallow one must resolve regardless of coming second.
#[cfg(feature = "json")]
#[test]
fn import_caches_are_depth_independent() {
    let n = 31;
    let mut src = String::new();
    for i in 0..n {
        src.push_str(&format!(
            "package P{i} {{ public import P{}::*; }}\n",
            i + 1
        ));
    }
    src.push_str(&format!("package P{n} {{ part def Deep; }}\n"));
    // The deep probe first: its walk touches every intermediate scope near
    // the depth limit. The shallow probes after it must still resolve —
    // they cover a band of start scopes so the test bites wherever the
    // guard's exact arithmetic lands the poisoned cache.
    src.push_str("package Probe {\n    part deep : P0::Deep;\n");
    for i in 18..=28 {
        src.push_str(&format!("    part ok{i} : P{i}::Deep;\n"));
    }
    src.push('}');
    let mut model = Model::new();
    model.add_source("chain.sysml", &src);
    assert!(!model.has_errors());
    let elements = emit(&model);
    let (_, unresolved) = count_refs(&elements);
    assert_eq!(
        unresolved, 1,
        "only the deliberately-too-deep probe stays unresolved"
    );
}

/// Lib-gated: an action-local redefinition of the library `this`
/// (`:>> this : Tally;`) is what a subsequent `assign this.count` chain
/// resolves through — the redefinition shadows the inherited library
/// feature inside the action's body, and the chain lands on the counted
/// attribute (a published textbook pattern).
#[test]
fn redefined_this_resolves_in_assignment_chains() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "tally.sysml",
        "package Counter {
            private import ScalarValues::*;
            part def Tally {
                attribute count : Integer := 0;
                action bump {
                    :>> this : Tally;
                    assign this.count := count + 1;
                }
            }
        }",
    );
    assert!(!model.has_errors());
    let unresolved: Vec<String> = sysmlv2_parser::check::validate_model(&model)
        .into_iter()
        .filter(|(_, d)| d.message.starts_with("unresolved"))
        .map(|(_, d)| d.message)
        .collect();
    assert!(
        unresolved.is_empty(),
        "the redefined `this` and its chain must resolve: {unresolved:?}"
    );
}

/// Lib-gated: a *qualified* reference to an inherited library feature
/// (`Cabin::self` — `self` is declared on a library supertype, not on
/// `Cabin` itself) resolves through the qualified walk exactly like an
/// owned member.
#[test]
fn qualified_reference_to_inherited_library_feature() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "lift.sysml",
        "package Lift {
            enum def Mode { IDLE; RISING; }
            action def Raise {
                in cab : Cabin;
                assign cab.mode := Mode::RISING;
            }
            part def Cabin {
                attribute mode : Mode;
                perform action raise[*] : Raise;
                perform action go[*] {
                    perform raise[1] { in cab = Cabin::self; }
                }
            }
        }",
    );
    assert!(!model.has_errors());
    let unresolved: Vec<String> = sysmlv2_parser::check::validate_model(&model)
        .into_iter()
        .filter(|(_, d)| d.message.starts_with("unresolved"))
        .map(|(_, d)| d.message)
        .collect();
    assert!(
        unresolved.is_empty(),
        "`Cabin::self` must reach the inherited library feature: {unresolved:?}"
    );
}

/// `expose P::**` is an import for name resolution like `import P::**`:
/// the target's contents come into scope recursively, so view-body
/// members (filters, renderings) can reference them — the recursive
/// expose once recorded only the membership import, leaving nested
/// names unresolvable and view exposure empty.
#[test]
fn recursive_expose_imports_contents() {
    let mut model = Model::new();
    model.add_source(
        "vx.sysml",
        "package VX {
            part def D { attribute size; }
            part rig {
                part left : D;
                part right : D;
            }
            view slice {
                expose rig::**;
                filter @Marker;
            }
            metadata def Marker;
         }",
    );
    assert!(!model.has_errors());
    let unresolved: Vec<String> = sysmlv2_parser::check::validate_model(&model)
        .into_iter()
        .filter(|(_, d)| d.message.starts_with("unresolved"))
        .map(|(_, d)| d.message)
        .collect();
    assert!(unresolved.is_empty(), "{unresolved:?}");

    // The exposure enumerates the target and its members, filter applied:
    // nothing carries @Marker, and a metadata test on an untagged element
    // is provably false — everything hides.
    let mut r = sysmlv2_parser::json::ResolvedModel::build(&model);
    let view = r.resolve_qualified("VX::slice").expect("view resolves");
    assert_eq!(r.element_type(view), "ViewUsage");
    let exposed = r.view_exposed_elements(view);
    assert!(exposed.is_empty(), "filter must hide every untagged member");
}

/// View exposure without a filter enumerates the exposed subtree; with a
/// metadata filter only tagged members (and untagged non-matching
/// members under `not`) remain — the three-valued import-filter
/// machinery drives both.
#[test]
fn view_exposure_honors_filters() {
    let mut model = Model::new();
    model.add_source(
        "vf.sysml",
        "package VF {
            metadata def HOT;
            part def D;
            part rig {
                #HOT part boiler : D;
                part radiator : D;
            }
            view hotOnly {
                expose rig::*;
                filter @HOT;
            }
            view coolOnly {
                expose rig::*;
                filter not (@HOT);
            }
         }",
    );
    assert!(!model.has_errors());
    let mut r = sysmlv2_parser::json::ResolvedModel::build(&model);
    let names = |r: &mut sysmlv2_parser::json::ResolvedModel, view: &str| -> Vec<String> {
        let v = r.resolve_qualified(view).expect("view resolves");
        r.view_exposed_elements(v)
            .into_iter()
            .filter_map(|e| r.element_qualified_name(e))
            .collect()
    };
    let hot = names(&mut r, "VF::hotOnly");
    assert_eq!(hot, vec!["VF::rig::boiler".to_string()], "{hot:?}");
    let cool = names(&mut r, "VF::coolOnly");
    assert!(
        cool.contains(&"VF::rig::radiator".to_string())
            && !cool.iter().any(|n| n.contains("boiler")),
        "{cool:?}"
    );
}
