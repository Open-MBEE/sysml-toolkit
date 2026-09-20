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

#[cfg(feature = "json")]
#[test]
fn anonymous_redefinition_fanout_targets_the_inherited_feature() {
    use sysmlv2_parser::{check, json::ResolvedModel};
    let lib = "package Lib { part def Item { attribute name; }
        part def Container { ref part items : Item[*]; } }";
    for count in 1..=4 {
        for reverse_files in [false, true] {
            let members = (0..count)
                .map(|i| format!("ref :>> items = a{i};"))
                .collect::<Vec<_>>()
                .join("\n");
            let values = (0..count)
                .map(|i| format!("part a{i} : Item;"))
                .collect::<Vec<_>>()
                .join("\n");
            let usage = format!(
                "package Usage {{ private import Lib::*; {values}
                part c : Container {{ {members} }} }}"
            );
            let mut model = Model::new();
            let mut sources = vec![("lib.sysml", lib), ("usage.sysml", usage.as_str())];
            if reverse_files {
                sources.reverse();
            }
            for (name, text) in sources {
                model.add_source(name, text);
            }
            assert!(!model.has_errors());
            let mut resolved = ResolvedModel::build(&model);
            let base = resolved.resolve_qualified("Lib::Container::items").unwrap();
            let target = resolved.element_id(base).to_string();
            let rows = emit(&model);
            let edges: Vec<_> = rows
                .iter()
                .filter(|e| e["@type"] == "Redefinition")
                .collect();
            assert_eq!(edges.len(), count);
            for edge in edges {
                assert_eq!(
                    edge["redefinedFeature"]["@id"].as_str(),
                    Some(target.as_str()),
                    "{count} siblings, reversed={reverse_files}: {edge}"
                );
            }
            assert!(check::validate_model(&model).is_empty());
            assert!(check::validate_semantics(&model).is_empty());
            let sites: Vec<_> = resolved
                .reference_sites()
                .iter()
                .filter(|site| site.kind == "redefinedFeature")
                .collect();
            assert_eq!(sites.len(), count);
            assert!(sites.iter().all(|site| site.target == base));
        }
    }
}

#[cfg(feature = "json")]
#[test]
fn redefinition_fanout_preserves_inherited_overrides_and_named_members() {
    use sysmlv2_parser::{check, json::ResolvedModel};
    for members in [
        "ref :>> items = a; ref :>> items = b;",
        "ref namedItem :>> items = a; ref :>> items = b;",
        "ref :>> items = b; ref namedItem :>> items = a;",
    ] {
        let source = format!(
            "package P {{
            part def Item {{ attribute marker = 7; }}
            part def Base {{ ref part items : Item[*]; }}
            part def Derived :> Base {{ ref :>> items; }}
            part a : Item; part b : Item;
            part c : Derived {{ {members} }}
        }}"
        );
        let mut model = Model::new();
        model.add_source("inherit.sysml", &source);
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let base = r.resolve_qualified("P::Base::items").unwrap();
        let inherited = r.resolve_qualified("P::Derived::items").unwrap();
        assert_ne!(base, inherited);
        let rows = emit(&model);
        let edges: Vec<_> = rows
            .iter()
            .filter(|e| e["@type"] == "Redefinition")
            .collect();
        assert_eq!(edges.len(), 3);
        assert_eq!(
            edges[0]["redefinedFeature"]["@id"],
            r.element_id(base).to_string()
        );
        for edge in &edges[1..] {
            assert_eq!(
                edge["redefinedFeature"]["@id"],
                r.element_id(inherited).to_string()
            );
        }
        assert!(check::validate_model(&model).is_empty());
    }
    // Declared local targets remain visible: the fix is not an
    // inherited-only lookup, nor a blanket removal of local members.
    let mut model = Model::new();
    model.add_source(
        "local.kerml",
        "class C { feature x; feature y redefines x; }",
    );
    let mut r = ResolvedModel::build(&model);
    let x = r.resolve_qualified("C::x").unwrap();
    let rows = emit(&model);
    let edge = rows.iter().find(|e| e["@type"] == "Redefinition").unwrap();
    assert_eq!(edge["redefinedFeature"]["@id"], r.element_id(x).to_string());
}

#[cfg(feature = "json")]
#[test]
fn redefinition_fanout_does_not_hide_missing_or_ambiguous_targets() {
    use sysmlv2_parser::check;
    for (definitions, typing, diagnostic) in [
        ("part def C;", "C", "unresolved reference `items`"),
        (
            "part def L { ref part items : Item[*]; }
          part def R { ref part items : Item[*]; }",
            "L, R",
            "ambiguous reference `items`",
        ),
    ] {
        let mut model = Model::new();
        model.add_source(
            "invalid.sysml",
            &format!(
                "package P {{
            part def Item; {definitions} part a : Item;
            part c : {typing} {{ ref :>> items = a; ref :>> items = a; }}
        }}"
            ),
        );
        assert!(!model.has_errors());
        let findings = check::validate_model(&model);
        assert_eq!(findings.len(), 2, "{findings:?}");
        assert!(
            findings.iter().all(|(_, d)| d.message.contains(diagnostic)),
            "{findings:?}"
        );
    }
    // Ordinary references to indistinguishable siblings remain ambiguous.
    let mut model = Model::new();
    model.add_source(
        "ordinary.sysml",
        "package P {
        part def Item; part def C { ref part items : Item[*]; }
        part a : Item;
        part c : C { ref :>> items = a; ref :>> items = a; }
        attribute probe = c::items;
    }",
    );
    let findings = check::validate_model(&model);
    assert_eq!(findings.len(), 1, "{findings:?}");
    assert!(findings[0].1.message.contains("ambiguous"), "{findings:?}");
}

#[cfg(feature = "json")]
#[test]
fn kerml_redefinition_fanout_keeps_inherited_member_lookup() {
    use sysmlv2_parser::{check, json::ResolvedModel};
    let mut model = Model::new();
    model.add_source(
        "fanout.kerml",
        "package P {
        class Item { feature marker = 7; }
        class C { feature items : Item[*]; }
        feature c : C {
            feature redefines items { feature result = marker; }
            feature redefines items { feature result = marker; }
            feature redefines items { feature result = marker; }
        }
    }",
    );
    assert!(!model.has_errors());
    assert!(check::validate_model(&model).is_empty());
    let mut r = ResolvedModel::build(&model);
    let base = r.resolve_qualified("P::C::items").unwrap();
    let marker = r.resolve_qualified("P::Item::marker").unwrap();
    let sites: Vec<_> = r
        .reference_sites()
        .iter()
        .filter(|site| site.kind == "redefinedFeature")
        .collect();
    assert_eq!(sites.len(), 3);
    assert!(sites.iter().all(|site| site.target == base));
    assert_eq!(r.references_to(marker).len(), 3);
}

/// `inherited_memberships` / `inherited_features` /
/// `effective_features` — the resolver's inheritance walk enumerated.
#[cfg(feature = "json")]
#[test]
fn inherited_members_enumeration() {
    use sysmlv2_parser::json::ResolvedModel;
    let mut model = Model::new();
    model.add_source(
        "m.sysml",
        "package P {
            part def Base {
                attribute mass;
                private attribute hidden;
            }
            part def Mid :> Base { attribute midOnly; }
            part def Sub :> Mid { attribute own; }
            part def Shadow :> Base { attribute mass; }
            part def Redef :> Base { attribute total :>> mass; }
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let by_name = |r: &mut ResolvedModel, qn: &str| r.resolve_qualified(qn).unwrap();

    // Transitive inheritance, private excluded; memberships returned,
    // declaring type = the membership's owner.
    let sub = by_name(&mut r, "P::Sub");
    let inherited = r.inherited_memberships(sub, false);
    let names: Vec<_> = inherited
        .iter()
        .map(|&m| r.membership_member_name(m).unwrap())
        .collect();
    assert_eq!(names, ["midOnly", "mass"], "BFS order: Mid's before Base's");
    let mid = by_name(&mut r, "P::Mid");
    let base = by_name(&mut r, "P::Base");
    assert_eq!(r.owner(inherited[0]), Some(mid), "midOnly declared by Mid");
    assert_eq!(r.owner(inherited[1]), Some(base), "mass declared by Base");
    for &m in &inherited {
        assert!(!r.membership_is_alias(m));
        assert!(r.membership_member(m).is_some());
    }

    // effective = owned then inherited.
    let eff: Vec<_> = r
        .effective_features(sub, true)
        .iter()
        .map(|&m| r.element_name(m).unwrap().to_string())
        .collect();
    assert_eq!(eff, ["own", "midOnly", "mass"]);

    // Same-name shadowing: an owned `mass` hides the inherited one.
    let shadow = by_name(&mut r, "P::Shadow");
    assert!(r.inherited_features(shadow, false).is_empty());

    // Redefinition shadowing under a *different* name: `total :>> mass`.
    let redef = by_name(&mut r, "P::Redef");
    assert!(r.inherited_features(redef, false).is_empty());

    // No heritage -> empty; and the definition itself is not a feature.
    assert!(r.inherited_memberships(base, false).is_empty());
}

/// `include_implied` walks the Tables 31/32 library bases —
/// an action usage inherits `Actions::Action`'s `start`/`done`.
#[cfg(feature = "json")]
#[test]
fn inherited_members_implied_library_bases() {
    use sysmlv2_parser::json::ResolvedModel;
    let lib = sysmlv2_testkit::library_dir();
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source("a.sysml", "package Q { action a { action step1; } }");
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let a = r.resolve_qualified("Q::a").unwrap();

    // Explicit-only: no written heritage, nothing inherited.
    assert!(r.inherited_features(a, false).is_empty());

    // Implied: Actions::Action's members arrive, `start`/`done` included.
    let implied: Vec<_> = r
        .inherited_features(a, true)
        .iter()
        .filter_map(|&m| r.element_lookup_name(m))
        .collect();
    assert!(
        implied.iter().any(|n| n == "start") && implied.iter().any(|n| n == "done"),
        "expected start/done among implied-inherited features, got: {implied:?}"
    );
    for m in r.inherited_features(a, true) {
        assert!(r.is_library_element(m));
    }
}

/// Conformance corner cases: imported memberships inherit, unrelated
/// same-name branches are both retained, and the OCL intersection
/// condition removes redefinition siblings.
#[cfg(feature = "json")]
#[test]
fn inherited_members_imports_and_redefinition_siblings() {
    use sysmlv2_parser::json::ResolvedModel;

    // (1) A public import in the base re-exports through heritage.
    let mut model = Model::new();
    model.add_source(
        "i.sysml",
        "package P {
            part def Imported { attribute fromImport; }
            part def Base { public import Imported::fromImport; }
            part def Sub :> Base;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let sub = r.resolve_qualified("P::Sub").unwrap();
    let names: Vec<_> = r
        .inherited_features(sub, false)
        .iter()
        .filter_map(|&m| r.element_name(m).map(str::to_string))
        .collect();
    assert_eq!(names, ["fromImport"], "public import must inherit");

    // (1b) A private import must NOT inherit.
    let mut model = Model::new();
    model.add_source(
        "ip.sysml",
        "package P {
            part def Imported { attribute fromImport; }
            part def Base { private import Imported::fromImport; }
            part def Sub :> Base;
         }",
    );
    let mut r = ResolvedModel::build(&model);
    let sub = r.resolve_qualified("P::Sub").unwrap();
    assert!(r.inherited_features(sub, false).is_empty());

    // (2) Same-name features of unrelated branches are both retained
    // (name lookup is ambiguous; the memberships still inherit).
    let mut model = Model::new();
    model.add_source(
        "u.sysml",
        "package P {
            part def A { attribute x; }
            part def B { attribute x; }
            part def D :> B;
            part def C :> A, D;
         }",
    );
    let mut r = ResolvedModel::build(&model);
    let c = r.resolve_qualified("P::C").unwrap();
    let xs: Vec<_> = r
        .inherited_features(c, false)
        .iter()
        .filter_map(|&m| r.element_name(m).map(str::to_string))
        .collect();
    assert_eq!(xs, ["x", "x"], "both unrelated x features inherit");

    // (3) Intersection condition: owned `z :>> A::x` removes both the
    // redefined `x` and the sibling `y :>> x` arriving from `B`.
    let mut model = Model::new();
    model.add_source(
        "s.sysml",
        "package P {
            part def A { attribute x; }
            part def B :> A { attribute y :>> x; }
            part def C :> B { attribute z :>> A::x; }
         }",
    );
    let mut r = ResolvedModel::build(&model);
    let c = r.resolve_qualified("P::C").unwrap();
    let leftover: Vec<_> = r
        .inherited_features(c, false)
        .iter()
        .filter_map(|&m| r.element_name(m).map(str::to_string))
        .collect();
    assert!(
        leftover.is_empty(),
        "y and x both removed by the intersection condition, got {leftover:?}"
    );

    // (4) Alias memberships inherit as memberships: `alias m for mass`
    // in the base arrives on the subtype, navigable to its target.
    let mut model = Model::new();
    model.add_source(
        "a.sysml",
        "package P {
            part def Base { attribute mass; alias m for mass; }
            part def Sub :> Base;
         }",
    );
    let mut r = ResolvedModel::build(&model);
    let sub = r.resolve_qualified("P::Sub").unwrap();
    let memberships = r.inherited_memberships(sub, false);
    let alias = memberships
        .iter()
        .copied()
        .find(|&m| r.membership_is_alias(m))
        .expect("inherited alias membership");
    assert_eq!(r.membership_member_name(alias).as_deref(), Some("m"));
    let mass = r.resolve_qualified("P::Base::mass").unwrap();
    assert_eq!(r.membership_member(alias), Some(mass));
    // The ordinary membership for `mass` is present too.
    assert!(
        memberships
            .iter()
            .any(|&m| !r.membership_is_alias(m) && r.membership_member(m) == Some(mass))
    );
}

/// Composition corner cases: nested re-export filter policy,
/// imported aliases, cross-branch redefiner independence, and the
/// heritage of imported scopes.
#[cfg(feature = "json")]
#[test]
fn inherited_members_import_policy_composition() {
    use sysmlv2_parser::json::ResolvedModel;

    // (1) A nested public re-export keeps its own filter policy.
    let mut model = Model::new();
    model.add_source(
        "f.sysml",
        "package P {
            metadata def Safety;
            package Lib {
                part safe { @Safety; }
                part plain;
            }
            package Reexport { public import Lib::*[@Safety]; }
            part def Base { public import Reexport::*; }
            part def Sub :> Base;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let sub = r.resolve_qualified("P::Sub").unwrap();
    let names: Vec<_> = r
        .inherited_features(sub, false)
        .iter()
        .filter_map(|&m| r.element_name(m).map(str::to_string))
        .collect();
    assert!(names.contains(&"safe".to_string()), "{names:?}");
    assert!(
        !names.contains(&"plain".to_string()),
        "nested [@Safety] filter must hold through the re-export: {names:?}"
    );

    // (2) Aliases reached through a public import are enumerated.
    let mut model = Model::new();
    model.add_source(
        "a.sysml",
        "package P {
            package Lib {
                part x;
                alias a for x;
            }
            part def Base { public import Lib::*; }
            part def Sub :> Base;
         }",
    );
    let mut r = ResolvedModel::build(&model);
    let sub = r.resolve_qualified("P::Sub").unwrap();
    let memberships = r.inherited_memberships(sub, false);
    let alias = memberships
        .iter()
        .copied()
        .find(|&m| r.membership_is_alias(m))
        .expect("imported alias membership");
    assert_eq!(r.membership_member_name(alias).as_deref(), Some("a"));
    let x = r.resolve_qualified("P::Lib::x").unwrap();
    assert_eq!(r.membership_member(alias), Some(x));

    // (3) Redefiners of unrelated heritage branches never suppress one
    // another; an owned redefiner still suppresses both.
    let mut model = Model::new();
    model.add_source(
        "b.sysml",
        "package P {
            part def A { attribute x; }
            part def B :> A { attribute y :>> x; }
            part def D :> A { attribute z :>> x; }
            part def E :> D;
            part def C :> B, E;
            part def F :> B, E { attribute own :>> A::x; }
         }",
    );
    let mut r = ResolvedModel::build(&model);
    let c = r.resolve_qualified("P::C").unwrap();
    let mut names: Vec<_> = r
        .inherited_features(c, false)
        .iter()
        .filter_map(|&m| r.element_name(m).map(str::to_string))
        .collect();
    names.sort();
    assert_eq!(names, ["y", "z"], "both branch redefiners inherit");
    let f = r.resolve_qualified("P::F").unwrap();
    let leftover: Vec<_> = r
        .inherited_features(f, false)
        .iter()
        .filter_map(|&m| r.element_name(m).map(str::to_string))
        .collect();
    assert!(
        leftover.is_empty(),
        "owned `own :>> A::x` suppresses x, y, and z: {leftover:?}"
    );

    // (4) Inherited members of an *imported* type resolve through the
    // import — enumeration follows lookup's base arm.
    let mut model = Model::new();
    model.add_source(
        "h.sysml",
        "package P {
            part def Other { attribute deep; }
            part def Mixin :> Other { attribute shallow; }
            part def Base { public import Mixin::*; }
            part def Sub :> Base;
         }",
    );
    let mut r = ResolvedModel::build(&model);
    let sub = r.resolve_qualified("P::Sub").unwrap();
    let names: Vec<_> = r
        .inherited_features(sub, false)
        .iter()
        .filter_map(|&m| r.element_name(m).map(str::to_string))
        .collect();
    assert!(
        names.contains(&"shallow".to_string()) && names.contains(&"deep".to_string()),
        "imported type's own + inherited members both arrive: {names:?}"
    );
}

/// `include_implied = false` holds through imported type scopes too: a
/// base's `import T::*` contributes T's own members, not the members of
/// T's implied library bases.
#[cfg(feature = "json")]
#[test]
fn include_implied_false_holds_through_imported_type_scopes() {
    use sysmlv2_parser::json::ResolvedModel;
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "a.sysml",
        "package Q {
            part def T { attribute x; }
            part def Base { public import T::*; }
            part def Sub :> Base;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let sub = r.resolve_qualified("Q::Sub").unwrap();
    let names = |r: &mut ResolvedModel, implied: bool| -> Vec<String> {
        let mut v: Vec<String> = r
            .inherited_memberships(sub, implied)
            .iter()
            .filter_map(|&m| r.membership_member_name(m))
            .collect();
        v.sort();
        v
    };
    assert_eq!(names(&mut r, false), ["x"]);
    let implied = names(&mut r, true);
    assert!(
        implied.contains(&"x".to_string()) && implied.len() > 1,
        "T's implied bases contribute only when asked: {implied:?}"
    );
}

/// Written heritage is consulted before implied library heritage — the
/// order `base_scopes` has always used, now made explicit by the
/// written/implied split. Where a written base and an implied Tables 31/32
/// base both declare a member of one name with non-overlapping metaclasses,
/// lookup keeps the earlier candidate, so the written base's member wins.
#[cfg(feature = "json")]
#[test]
fn written_base_precedes_implied_library_base_in_lookup() {
    use sysmlv2_parser::json::ResolvedModel;
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    // `Actions::Action` (the implied base of every action definition)
    // declares the action usage `start`; the written base declares an
    // attribute of the same name.
    model.add_source(
        "p.sysml",
        "package Q {
            action def Base { attribute start; }
            action def A :> Base { attribute again :>> start; }
         }",
    );
    let mut r = ResolvedModel::build(&model);
    let again = r.resolve_qualified("Q::A::again").unwrap();
    let base = r.resolve_qualified("Q::Base").unwrap();
    let targets = r.redefinition_targets(again);
    assert_eq!(targets.len(), 1, "{targets:?}");
    assert_eq!(
        r.owner(targets[0]),
        Some(base),
        "the written base's member wins"
    );
    assert_eq!(r.element_type(targets[0]), "AttributeUsage");
}

/// A chain-source transition (`first v.a`) still reports its source
/// through `transition_parts` now that the source membership is an
/// OwningMembership owning the chain feature.
#[cfg(feature = "json")]
#[test]
fn transition_parts_reads_a_chain_source() {
    use sysmlv2_parser::json::ResolvedModel;
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package P {
            part def V { part a; }
            state def S {
                part v : V;
                state s1; state s2;
                transition t1 first s1 then s2;
                transition t2 first v.a then s2;
            }
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let t1 = r.resolve_qualified("P::S::t1").unwrap();
    let t2 = r.resolve_qualified("P::S::t2").unwrap();
    let s1 = r.resolve_qualified("P::S::s1").unwrap();
    assert_eq!(r.transition_parts(t1).source, Some(s1));
    let src = r.transition_parts(t2).source.expect("chain source");
    assert_eq!(r.element_type(src), "Feature");
    assert!(
        r.owned_relationships(src)
            .iter()
            .any(|&x| r.element_type(x) == "FeatureChaining"),
        "the source is the synthesized chain feature"
    );
}

/// The declared multiplicity of an element is its own written clause,
/// read through the owner index the builder keeps for the table.
#[test]
fn declared_multiplicity_reads_the_element_s_own_clause() {
    use sysmlv2_parser::json::ResolvedModel;
    let mut model = Model::new();
    model.add_source(
        "p.sysml",
        "package P {
            part def D;
            part a : D[2..5];
            part bare : D;
            part heir :>> a;
            part many : D[*];
         }",
    );
    let mut r = ResolvedModel::build(&model);
    let [a, bare, heir, many] =
        ["P::a", "P::bare", "P::heir", "P::many"].map(|qn| r.resolve_qualified(qn).unwrap());
    assert_eq!(r.declared_multiplicity(a), Some((2.0, 5.0)));
    // Answers are stable across lookups and independent of the order.
    assert_eq!(r.declared_multiplicity(many), Some((0.0, f64::INFINITY)));
    assert_eq!(r.declared_multiplicity(a), Some((2.0, 5.0)));
    // An element that declares none has none; inherited clauses are
    // deliberately not walked.
    assert_eq!(r.declared_multiplicity(bare), None);
    assert_eq!(r.declared_multiplicity(heir), None);
}

/// Elements added on top of a prepared library are indexed alongside the
/// library's own rows, and neither side shadows the other.
#[test]
fn declared_multiplicity_spans_a_prepared_library_and_its_model() {
    use sysmlv2_parser::json::ResolvedModel;
    let mut base = Model::new();
    base.add_library_source(
        "lib.sysml",
        "library package L { part def D; part shared : D[3..4]; }",
    );
    let prepared = base.prepare_library().unwrap();
    let mut model = Model::new();
    prepared.install(&mut model).unwrap();
    model.add_source("p.sysml", "package P { part own : L::D[1..2]; }");
    let mut r = ResolvedModel::build(&model);
    let own = r.resolve_qualified("P::own").unwrap();
    let shared = r.resolve_qualified("L::shared").unwrap();
    assert_eq!(r.declared_multiplicity(own), Some((1.0, 2.0)));
    assert_eq!(r.declared_multiplicity(shared), Some((3.0, 4.0)));
}
