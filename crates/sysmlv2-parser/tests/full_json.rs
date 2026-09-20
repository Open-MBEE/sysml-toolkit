//! Full-form JSON gates: derived properties and implied
//! relationships, validated against the published normative schema.
//!
//! One departure from that schema is deliberate and is the exception the
//! conformance note in `INTEROP.md` names: the value of a numeric literal
//! that no JSON number denotes exactly — an integer past 64 bits, more
//! significant digits than a double holds, an exponent outside its range —
//! is emitted as the literal's own text, where the schema declares
//! `LiteralInteger.value` an integer or null and `LiteralRational.value` a
//! number or null. Evaluation reads literals exactly, so rounding one into
//! a JSON number would make a model's two forms disagree about its value.
//! Anything validated here that carries such a literal has to allow the
//! string spelling for that property; nothing else is exempt.

#![cfg(feature = "json")]

use serde_json::{Value, json};
use std::collections::HashMap;
use sysmlv2_parser::full::{from_compact_value, model_to_full_json, to_full_json};
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};

fn schema_validator() -> jsonschema::Validator {
    let path = sysmlv2_testkit::workspace_root().join("spec-refs/SysML.schema.json");
    let schema: Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    jsonschema::validator_for(&schema).expect("published schema compiles")
}

/// Validate every element against the *exact-type* variant of its
/// metaclass definition (detailed per-property errors).
fn validate_elements(validator_schema: &Value, elements: &[Value]) -> Vec<String> {
    let mut validators: std::collections::HashMap<String, jsonschema::Validator> =
        Default::default();
    let mut failures = Vec::new();
    for el in elements {
        let t = el["@type"].as_str().unwrap().to_string();
        let validator = validators.entry(t.clone()).or_insert_with(|| {
            let def = &validator_schema["$defs"][&t];
            let exact = if def.get("anyOf").is_some() {
                def["anyOf"][0].clone()
            } else {
                def.clone()
            };
            let mut mini = exact;
            mini["$defs"] = validator_schema["$defs"].clone();
            jsonschema::validator_for(&mini).unwrap()
        });
        for err in validator.iter_errors(el).take(4) {
            failures.push(format!("{t} @ {}: {err}", err.instance_path()));
        }
        if failures.len() > 25 {
            break;
        }
    }
    failures
}

#[test]
fn full_form_validates_against_published_schema() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "demo.sysml",
        "package Demo {
            import ScalarValues::*;
            part def Vehicle {
                attribute mass : Real = 1500.0;
                part wheels : Wheel[4];
                doc /* a vehicle */
            }
            part def Wheel;
            part car : Vehicle {
                attribute :>> mass = 1800.0;
            }
         }",
    );
    let full = model_to_full_json(&model);
    let elements = full.as_array().unwrap();

    // Implied relationships are present and flagged.
    let implied: Vec<&Value> = elements.iter().filter(|e| e["isImplied"] == true).collect();
    assert!(!implied.is_empty(), "implied relationships expected");
    let wheel_sub = implied.iter().find(|e| {
        e["@type"] == "Subclassification"
            && elements
                .iter()
                .any(|d| d["declaredName"] == "Wheel" && d["@id"] == e["subclassifier"]["@id"])
    });
    assert!(
        wheel_sub.is_some(),
        "part def Wheel (no explicit bases) gets an implied Subclassification"
    );
    // Its target is the normative Parts::Part ID.
    assert_eq!(
        wheel_sub.unwrap()["superclassifier"]["@id"],
        "0774a545-39e3-5bc1-9607-63beabc6bf65"
    );
    // An implied specialization is owned by its specific side and says so.
    let wheel_sub = *wheel_sub.unwrap();
    assert_eq!(wheel_sub["owningClassifier"], wheel_sub["subclassifier"]);
    assert_eq!(wheel_sub["owningType"], wheel_sub["subclassifier"]);
    // Vehicle has an explicit base? No — it also gets one. car : Vehicle has
    // explicit typing but no subsetting → implied Subsetting to Parts::parts.
    assert!(implied.iter().any(|e| e["@type"] == "Subsetting"));

    // Every element is flagged as implied-included and has derived props.
    for e in elements.iter() {
        assert_eq!(e["isImpliedIncluded"], true);
    }
    let vehicle = elements
        .iter()
        .find(|e| e["declaredName"] == "Vehicle")
        .unwrap();
    assert_eq!(vehicle["qualifiedName"], "Demo::Vehicle");
    assert!(vehicle["ownedFeature"].as_array().unwrap().len() >= 2);
    assert!(!vehicle["documentation"].as_array().unwrap().is_empty());
    let mass = elements
        .iter()
        .find(|e| e["declaredName"] == "mass" && e["qualifiedName"] == "Demo::Vehicle::mass")
        .unwrap();
    assert_eq!(mass["owner"]["@id"], vehicle["@id"]);

    // Schema validation of every element.
    let schema: Value = serde_json::from_str(
        &std::fs::read_to_string(
            sysmlv2_testkit::workspace_root().join("spec-refs/SysML.schema.json"),
        )
        .unwrap(),
    )
    .unwrap();
    let failures = validate_elements(&schema, elements);
    assert!(
        failures.is_empty(),
        "{} schema violations:\n{}",
        failures.len(),
        failures.join("\n")
    );
    let _ = schema_validator;
}

#[test]
fn full_form_without_library_completes_properties() {
    let parse = parse_source("package P { part def V; part v : V; enum def E { a; } }");
    let full = to_full_json(&parse.unit);
    let elements = full.as_array().unwrap();
    // No library → no implied relationships (the variant typing of `a`
    // included), flag stays false: `ownedRelationship->exists(isImplied)
    // implies isImpliedIncluded`.
    assert!(elements.iter().all(|e| e["isImpliedIncluded"] == false));
    assert!(elements.iter().all(|e| e["isImplied"] != true));
    let def = elements
        .iter()
        .find(|e| e["@type"] == "PartDefinition")
        .unwrap();
    // Property count matches the published schema's PartDefinition (84 + @id/@type).
    assert!(
        def.as_object().unwrap().len() >= 84,
        "expected the full property set, got {}",
        def.as_object().unwrap().len()
    );
    assert_eq!(def["qualifiedName"], "P::V");
    assert_eq!(def["ownedElement"].as_array().unwrap().len(), 0);
}

/// Element::isLibraryElement follows the ownership tree (KerML
/// deriveElementIsLibraryElement): a `library package` and everything it
/// owns, memberships included, are library elements; nothing else is.
/// The property is a boolean on every element, never null.
#[test]
fn full_form_derives_is_library_element() {
    let parse = parse_source(
        "library package L { part def X { attribute a; } }\n\
         package P { part def A :> L::X; part a : A; }",
    );
    let full = to_full_json(&parse.unit);
    let elements = full.as_array().unwrap();
    assert!(
        elements.iter().all(|e| e["isLibraryElement"].is_boolean()),
        "isLibraryElement must be derived for every element"
    );
    let by_qn = |qn: &str| {
        elements
            .iter()
            .find(|e| e["qualifiedName"] == qn)
            .unwrap_or_else(|| panic!("no element {qn}"))
    };
    for (qn, expected) in [
        ("L", true),
        ("L::X", true),
        ("L::X::a", true),
        ("P", false),
        ("P::A", false),
        ("P::a", false),
    ] {
        assert_eq!(by_qn(qn)["isLibraryElement"], expected, "{qn}");
    }
    // Relationships take their owning element's answer.
    let memberships_of = |qn: &str| {
        let id = by_qn(qn)["@id"].clone();
        elements
            .iter()
            .filter(move |e| e["owningRelatedElement"]["@id"] == id)
            .collect::<Vec<_>>()
    };
    assert!(!memberships_of("L").is_empty());
    assert!(
        memberships_of("L")
            .iter()
            .all(|m| m["isLibraryElement"] == true)
    );
    assert!(
        memberships_of("P")
            .iter()
            .all(|m| m["isLibraryElement"] == false)
    );
}

/// Unresolved-reference recovery (`to_full_json_with(recover_refs)`):
/// the injected TextualRepresentation annotations are schema-valid like
/// every other element, and a partial model round-trips losslessly
/// through the full form.
#[test]
fn recovery_annotations_are_schema_valid_and_round_trip() {
    let src = "package P {
        private import Missing::*;
        part def D;
        part x : UnknownType {
            attribute mass :> unknownAttr = 5.0;
        }
    }";
    let parse = parse_source(src);
    assert!(parse.diagnostics.is_empty());
    let full = sysmlv2_parser::full::to_full_json_with(&parse.unit, true);
    let elements = full.as_array().unwrap().clone();

    // The three unresolved names each carry one recovery annotation.
    let reps: Vec<&Value> = elements
        .iter()
        .filter(|e| {
            e["@type"] == "TextualRepresentation"
                && e["language"] == sysmlv2_parser::full::UNRESOLVED_REP_LANGUAGE
        })
        .collect();
    let mut bodies: Vec<&str> = reps.iter().map(|r| r["body"].as_str().unwrap()).collect();
    bodies.sort();
    assert_eq!(bodies, ["Missing", "UnknownType", "unknownAttr"]);

    // Schema validity of the whole document, injected elements included.
    let path = sysmlv2_testkit::workspace_root().join("spec-refs/SysML.schema.json");
    let schema: Value = serde_json::from_str(&std::fs::read_to_string(path).unwrap()).unwrap();
    let failures = validate_elements(&schema, &elements);
    assert!(failures.is_empty(), "{failures:#?}");

    // Lossless round trip: full form → lift → print == original (modulo
    // formatting), with the carriers suppressed.
    let lifted = sysmlv2_parser::lift::from_compact_json(&full).unwrap();
    assert!(lifted.errors.is_empty(), "{:#?}", lifted.errors);
    let text = sysmlv2_parser::print::print_source(&lifted.unit);
    assert!(text.contains(": UnknownType"), "{text}");
    assert!(text.contains(":> unknownAttr"), "{text}");
    assert!(text.contains("import Missing::*"), "{text}");
    assert!(!text.contains("rep "), "carriers must not surface: {text}");

    // Default emission is lossless too; recovery must not depend on an
    // opt-in flag (or on the CLI's Flexo envelope).
    let plain = to_full_json(&parse.unit);
    assert_eq!(
        plain
            .as_array()
            .unwrap()
            .iter()
            .filter(|e| {
                e["@type"] == "TextualRepresentation"
                    && e["language"] == sysmlv2_parser::full::UNRESOLVED_REP_LANGUAGE
            })
            .count(),
        3
    );
}

/// A `doc`, `comment`, `rep`, or `dependency` written with an
/// identification is an owned member of its namespace, and its owning
/// membership carries that name: an `about` clause — of a comment or of a
/// metadata usage — reaches it by local name, short name, or qualified
/// name, and the emitted Annotation's `annotatedElement` is that element
/// itself. Anonymous ones bind no name at all.
#[test]
fn named_annotating_elements_are_about_targets() {
    let src = "package P {
        metadata def Note;
        part def Vehicle {
            doc <vd> vehicleDoc /* A vehicle. */
            comment namedComment /* a named comment */
            rep inOCL language \"ocl\" /* self.x > 0 */
            doc /* anonymous */
            comment about namedComment /* local name */
            comment about vd /* short name */
            comment about inOCL /* textual representation */
            @Note about vehicleDoc;
        }
        comment about Vehicle::vehicleDoc /* qualified */
        comment about P::Vehicle::namedComment /* fully qualified */
        dependency vDep from Vehicle to Note;
        comment about vDep /* dependency */
        comment about P::vDep /* qualified dependency */
    }";
    let parse = parse_source(src);
    assert!(parse.diagnostics.is_empty());
    let full = sysmlv2_parser::full::to_full_json_with_policy(
        &parse.unit,
        sysmlv2_parser::full::UnresolvedReferencePolicy::Reject,
    )
    .expect("every about target resolves");
    let elements = full.as_array().unwrap();
    let by_id = |id: &Value| elements.iter().find(|e| &e["@id"] == id).unwrap();

    // Each Annotation, keyed by the body (or metaclass) of the element
    // that wrote the `about`, targets the named annotating element.
    let mut targets: Vec<(String, String)> = elements
        .iter()
        .filter(|e| e["@type"] == "Annotation")
        .map(|ann| {
            let owner = by_id(&ann["owningRelatedElement"]["@id"]);
            let target = by_id(&ann["annotatedElement"]["@id"]);
            let from = owner["body"]
                .as_str()
                .map(|b| b.trim().to_string())
                .unwrap_or_else(|| owner["@type"].as_str().unwrap().to_string());
            let to = format!(
                "{} {}",
                target["@type"].as_str().unwrap(),
                target["declaredName"].as_str().unwrap()
            );
            (from, to)
        })
        .collect();
    targets.sort();
    assert_eq!(
        targets,
        [
            ("MetadataUsage".into(), "Documentation vehicleDoc".into()),
            ("dependency".into(), "Dependency vDep".into()),
            ("fully qualified".into(), "Comment namedComment".into()),
            ("local name".into(), "Comment namedComment".into()),
            ("qualified".into(), "Documentation vehicleDoc".into()),
            ("qualified dependency".into(), "Dependency vDep".into()),
            ("short name".into(), "Documentation vehicleDoc".into()),
            (
                "textual representation".into(),
                "TextualRepresentation inOCL".into()
            ),
        ]
    );

    // The owning memberships name their annotating elements; an anonymous
    // one names nothing.
    let member_names = |ty: &str| -> Vec<(Option<String>, Option<String>)> {
        elements
            .iter()
            .filter(|e| e["@type"] == ty)
            .map(|e| {
                let m = by_id(&e["owningRelationship"]["@id"]);
                assert_eq!(m["@type"], "OwningMembership");
                (
                    m["memberName"].as_str().map(str::to_string),
                    m["memberShortName"].as_str().map(str::to_string),
                )
            })
            .collect()
    };
    assert_eq!(
        member_names("Documentation"),
        [(Some("vehicleDoc".into()), Some("vd".into())), (None, None)]
    );
    assert_eq!(
        member_names("TextualRepresentation"),
        [(Some("inOCL".into()), None)]
    );
    assert_eq!(member_names("Dependency"), [(Some("vDep".into()), None)]);

    // The same facts seen through the resolver: the names resolve to the
    // annotating elements, nothing resolves *through* one (they own no
    // members), and an anonymous element is reachable by no name — in
    // particular not by the internal path segment its id derives from.
    let mut model = Model::new();
    model.add_source("p.sysml", src);
    let mut r = sysmlv2_parser::json::ResolvedModel::build(&model);
    for (qn, ty, name) in [
        ("P::Vehicle::vehicleDoc", "Documentation", "vehicleDoc"),
        ("P::Vehicle::vd", "Documentation", "vehicleDoc"),
        ("P::Vehicle::namedComment", "Comment", "namedComment"),
        ("P::Vehicle::inOCL", "TextualRepresentation", "inOCL"),
        ("P::vDep", "Dependency", "vDep"),
    ] {
        let e = r
            .resolve_qualified(qn)
            .unwrap_or_else(|| panic!("{qn} resolves"));
        assert_eq!(r.element_type(e), ty);
        assert_eq!(r.element_name(e), Some(name));
        assert!(r.element_scope(e).is_none(), "{qn} owns no scope");
    }
    assert!(r.resolve_qualified("P::Vehicle::vehicleDoc::x").is_none());
    assert!(r.resolve_qualified("P::Vehicle::doc3").is_none());
    let vehicle = r.resolve_qualified("P::Vehicle").unwrap();
    let scope = r.element_scope(vehicle).unwrap();
    assert!(r.name_is_bound_in(scope, "vehicleDoc"));
    assert!(r.name_is_bound_in(scope, "vd"));
    assert!(!r.name_is_bound_in(scope, "doc3"));
}

#[test]
fn strict_full_form_rejects_unresolved_references() {
    let parse = parse_source("package P { part x : Missing; }");
    let error = sysmlv2_parser::full::to_full_json_with_policy(
        &parse.unit,
        sysmlv2_parser::full::UnresolvedReferencePolicy::Reject,
    )
    .unwrap_err();
    assert_eq!(error.references, ["Missing"]);

    let resolved = parse_source("package P { part def D; part x : D; }");
    assert!(
        sysmlv2_parser::full::to_full_json_with_policy(
            &resolved.unit,
            sysmlv2_parser::full::UnresolvedReferencePolicy::Reject,
        )
        .is_ok()
    );
}

/// The owning-side derived properties and `Type::multiplicity` carry real
/// references instead of the catalog's null default.
#[test]
fn owning_properties_and_multiplicity_derive() {
    let parse = parse_source(
        "package Demo {
            part def Vehicle {
                attribute mass;
                part wheel[4];
            }
            part v : Vehicle {
                part w2;
            }
         }",
    );
    assert!(parse.diagnostics.is_empty());
    let full = to_full_json(&parse.unit);
    let elements = full.as_array().unwrap();
    let by_name = |n: &str| {
        elements
            .iter()
            .find(|e| e.get("declaredName").and_then(Value::as_str) == Some(n))
            .unwrap()
    };
    let id_of = |e: &Value| e.get("@id").unwrap().as_str().unwrap().to_string();
    let ref_id = |e: &Value, k: &str| {
        e.get(k)
            .and_then(|v| v.get("@id"))
            .and_then(Value::as_str)
            .map(str::to_string)
    };

    let vehicle = by_name("Vehicle");
    let wheel = by_name("wheel");
    // Feature side: owner through a FeatureMembership.
    assert_eq!(ref_id(wheel, "owningType").as_ref(), Some(&id_of(vehicle)));
    assert_eq!(
        ref_id(wheel, "owningDefinition").as_ref(),
        Some(&id_of(vehicle)),
        "owner is a Definition"
    );
    assert!(
        wheel.get("owningUsage").unwrap().is_null(),
        "owner is not a Usage"
    );
    let fm = ref_id(wheel, "owningFeatureMembership").unwrap();
    let fm_el = elements
        .iter()
        .find(|e| e.get("@id").and_then(Value::as_str) == Some(fm.as_str()))
        .unwrap();
    assert_eq!(fm_el.get("@type").unwrap(), "FeatureMembership");
    // The membership itself names the type on both of its owner properties.
    assert_eq!(ref_id(fm_el, "owningType").as_ref(), Some(&id_of(vehicle)));
    assert_eq!(
        ref_id(fm_el, "membershipOwningNamespace").as_ref(),
        Some(&id_of(vehicle))
    );
    // Nested usage: both narrowings point at the usage owner.
    let w2 = by_name("w2");
    let v = by_name("v");
    assert_eq!(ref_id(w2, "owningType").as_ref(), Some(&id_of(v)));
    assert_eq!(ref_id(w2, "owningUsage").as_ref(), Some(&id_of(v)));
    assert!(w2.get("owningDefinition").unwrap().is_null());
    // Package-owned usages have no owning type.
    assert!(v.get("owningType").unwrap().is_null());
    // Type::multiplicity references the owned MultiplicityRange.
    let mult = ref_id(wheel, "multiplicity").expect("wheel[4] has a multiplicity");
    let mr = elements
        .iter()
        .find(|e| e.get("@id").and_then(Value::as_str) == Some(mult.as_str()))
        .unwrap();
    assert_eq!(mr.get("@type").unwrap(), "MultiplicityRange");
    assert!(by_name("mass").get("multiplicity").unwrap().is_null());
}

fn find_named<'a>(elements: &'a [Value], name: &str) -> &'a Value {
    elements
        .iter()
        .find(|e| e.get("declaredName").and_then(Value::as_str) == Some(name))
        .unwrap_or_else(|| panic!("no element named {name}"))
}

fn find_id<'a>(elements: &'a [Value], id: &str) -> &'a Value {
    elements
        .iter()
        .find(|e| e.get("@id").and_then(Value::as_str) == Some(id))
        .unwrap_or_else(|| panic!("no element with id {id}"))
}

fn elem_id(e: &Value) -> String {
    e["@id"].as_str().unwrap().to_string()
}

fn ref_of_prop(e: &Value, k: &str) -> Option<String> {
    e.get(k)
        .and_then(|v| v.get("@id"))
        .and_then(Value::as_str)
        .map(str::to_string)
}

fn refs_of_prop(e: &Value, k: &str) -> Vec<String> {
    e.get(k)
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("{k} is not an array on {}", e["@type"]))
        .iter()
        .map(|v| v["@id"].as_str().unwrap().to_string())
        .collect()
}

/// The relationships of metaclass `kind` whose owning related element is
/// `owner` — the owned (not membership-carried) shape.
fn owned_rels_of_kind<'a>(elements: &'a [Value], kind: &str, owner: &str) -> Vec<&'a Value> {
    elements
        .iter()
        .filter(|e| {
            e["@type"] == kind && ref_of_prop(e, "owningRelatedElement").as_deref() == Some(owner)
        })
        .collect()
}

/// Relationship-side owners: a relationship owned by its own source
/// reports that source as `owningType`, narrowed to `owningClassifier`
/// or `owningFeature`; inverting and featuring report `owningFeature`
/// and `owningFeatureOfType`. A standalone relationship rides a
/// membership and reports none of them.
#[test]
fn relationship_side_owners_derive() {
    let parse = parse_kerml_source(
        "package P {
            classifier A;
            classifier D;
            classifier B specializes A disjoint from D;
            classifier X conjugates A;
            feature g : A;
            feature f : A subsets g inverse of g featured by B;
            classifier C specializes B {
                feature :>> g;
            }
            specialization Sub subclassifier B specializes A;
            typing g typed by A;
            subset g subsets f;
            inverse g of f;
            featuring g by B;
            conjugate D ~ A;
            disjoint D from A;
         }",
    );
    assert!(parse.diagnostics.is_empty(), "{:?}", parse.diagnostics);
    let full = to_full_json(&parse.unit);
    let elements = full.as_array().unwrap();
    let a = elem_id(find_named(elements, "A"));
    let b = elem_id(find_named(elements, "B"));
    let d = elem_id(find_named(elements, "D"));
    let x = elem_id(find_named(elements, "X"));
    let f = elem_id(find_named(elements, "f"));

    let [sub] = owned_rels_of_kind(elements, "Subclassification", &b)[..] else {
        panic!("B owns exactly one Subclassification");
    };
    assert_eq!(ref_of_prop(sub, "owningType").as_deref(), Some(b.as_str()));
    assert_eq!(
        ref_of_prop(sub, "owningClassifier").as_deref(),
        Some(b.as_str())
    );
    assert!(
        sub.get("owningFeature").is_none(),
        "not a Subclassification property"
    );

    let [dis] = owned_rels_of_kind(elements, "Disjoining", &b)[..] else {
        panic!("B owns exactly one Disjoining");
    };
    assert_eq!(ref_of_prop(dis, "owningType").as_deref(), Some(b.as_str()));

    let [conj] = owned_rels_of_kind(elements, "Conjugation", &x)[..] else {
        panic!("X owns exactly one Conjugation");
    };
    assert_eq!(ref_of_prop(conj, "owningType").as_deref(), Some(x.as_str()));

    let [typing] = owned_rels_of_kind(elements, "FeatureTyping", &f)[..] else {
        panic!("f owns exactly one FeatureTyping");
    };
    assert_eq!(
        ref_of_prop(typing, "owningType").as_deref(),
        Some(f.as_str())
    );
    assert_eq!(
        ref_of_prop(typing, "owningFeature").as_deref(),
        Some(f.as_str())
    );
    let [subsetting] = owned_rels_of_kind(elements, "Subsetting", &f)[..] else {
        panic!("f owns exactly one Subsetting");
    };
    assert_eq!(
        ref_of_prop(subsetting, "owningFeature").as_deref(),
        Some(f.as_str())
    );
    let [inverting] = owned_rels_of_kind(elements, "FeatureInverting", &f)[..] else {
        panic!("f owns exactly one FeatureInverting");
    };
    assert_eq!(
        ref_of_prop(inverting, "owningFeature").as_deref(),
        Some(f.as_str())
    );
    assert!(
        inverting.get("owningType").is_none(),
        "an inverting is not a specialization"
    );
    let [featuring] = owned_rels_of_kind(elements, "TypeFeaturing", &f)[..] else {
        panic!("f owns exactly one TypeFeaturing");
    };
    assert_eq!(
        ref_of_prop(featuring, "owningFeatureOfType").as_deref(),
        Some(f.as_str())
    );

    // The anonymous redefining feature in C owns its Redefinition.
    let redefinition = elements
        .iter()
        .find(|e| e["@type"] == "Redefinition")
        .expect("one redefinition");
    let redefiner =
        ref_of_prop(redefinition, "owningRelatedElement").expect("owned by its feature");
    assert_eq!(
        ref_of_prop(redefinition, "owningFeature"),
        Some(redefiner.clone())
    );
    assert_eq!(ref_of_prop(redefinition, "owningType"), Some(redefiner));

    // A standalone relationship is a member, not an owned relationship, and
    // names no owner of any kind — for every family.
    let sub = find_named(elements, "Sub");
    assert_eq!(sub["@type"], "Subclassification");
    assert!(ref_of_prop(sub, "owningRelationship").is_some());
    let standalone: Vec<&Value> = elements
        .iter()
        .filter(|e| {
            e["owningRelatedElement"].is_null()
                && ref_of_prop(e, "owningRelationship").is_some()
                && matches!(
                    e["@type"].as_str(),
                    Some(
                        "Subclassification"
                            | "FeatureTyping"
                            | "Subsetting"
                            | "FeatureInverting"
                            | "TypeFeaturing"
                            | "Conjugation"
                            | "Disjoining"
                    )
                )
        })
        .collect();
    let kinds: Vec<&Value> = standalone.iter().map(|e| &e["@type"]).collect();
    assert_eq!(standalone.len(), 7, "{kinds:?}");
    for rel in &standalone {
        for prop in [
            "owningType",
            "owningClassifier",
            "owningFeature",
            "owningFeatureOfType",
        ] {
            assert!(
                rel.get(prop).is_none_or(Value::is_null),
                "{} {prop}",
                rel["@type"]
            );
        }
    }
    // A standalone conjugation still has its spelled ends.
    let conj = standalone
        .iter()
        .find(|e| e["@type"] == "Conjugation")
        .unwrap();
    assert_eq!(refs_of_prop(conj, "source"), [d.as_str()]);
    assert_eq!(refs_of_prop(conj, "target"), [a.as_str()]);
}

/// `Type::multiplicity` is the owned member that is a Multiplicity of any
/// kind, including KerML `multiplicity` members; a multiplicity does not
/// own one of its own.
#[test]
fn type_multiplicity_derives_for_kerml_members() {
    let parse = parse_kerml_source(
        "package P {
            classifier K {
                multiplicity m [2];
                feature f [3];
            }
            classifier N {
                multiplicity n subsets K::m;
            }
         }",
    );
    assert!(parse.diagnostics.is_empty(), "{:?}", parse.diagnostics);
    let full = to_full_json(&parse.unit);
    let elements = full.as_array().unwrap();
    let m = find_named(elements, "m");
    assert_eq!(m["@type"], "MultiplicityRange");
    assert_eq!(
        ref_of_prop(find_named(elements, "K"), "multiplicity"),
        Some(elem_id(m))
    );
    assert!(
        m["multiplicity"].is_null(),
        "a multiplicity owns no multiplicity"
    );
    let range = ref_of_prop(find_named(elements, "f"), "multiplicity").expect("f [3]");
    assert_eq!(find_id(elements, &range)["@type"], "MultiplicityRange");
    let n = find_named(elements, "n");
    assert_eq!(n["@type"], "Multiplicity");
    assert_eq!(
        ref_of_prop(find_named(elements, "N"), "multiplicity"),
        Some(elem_id(n))
    );
}

/// Annotation ends in the shape this toolkit emits: the Annotation is
/// owned by its annotating element, so that element is the source and the
/// owning annotating element; the annotated element owns nothing.
#[test]
fn annotation_ends_derive() {
    let parse = parse_source(
        "package P {
            part def V;
            part def W;
            comment C about V /* about V */
            comment C2 about V, W /* about both */
            doc /* on P */
            metadata def M;
            #M part p;
            @M about V;
         }",
    );
    assert!(parse.diagnostics.is_empty(), "{:?}", parse.diagnostics);
    let full = to_full_json(&parse.unit);
    let elements = full.as_array().unwrap();
    let p = elem_id(find_named(elements, "P"));
    let v = elem_id(find_named(elements, "V"));
    let c = find_named(elements, "C");
    let c_id = elem_id(c);

    let [ann] = owned_rels_of_kind(elements, "Annotation", &c_id)[..] else {
        panic!("C owns exactly one Annotation");
    };
    let ann_id = elem_id(ann);
    assert_eq!(
        ref_of_prop(ann, "annotatingElement").as_deref(),
        Some(c_id.as_str())
    );
    assert_eq!(
        ref_of_prop(ann, "annotatedElement").as_deref(),
        Some(v.as_str())
    );
    assert_eq!(
        ref_of_prop(ann, "owningAnnotatingElement").as_deref(),
        Some(c_id.as_str())
    );
    assert!(ann["owningAnnotatedElement"].is_null());
    assert!(ann["ownedAnnotatingElement"].is_null());
    assert_eq!(refs_of_prop(ann, "source"), [c_id.as_str()]);
    assert_eq!(refs_of_prop(ann, "target"), [v.as_str()]);
    assert_eq!(
        refs_of_prop(ann, "relatedElement"),
        [c_id.clone(), v.clone()]
    );

    assert_eq!(refs_of_prop(c, "annotation"), [ann_id.as_str()]);
    assert_eq!(
        refs_of_prop(c, "ownedAnnotatingRelationship"),
        [ann_id.as_str()]
    );
    assert!(c["owningAnnotatingRelationship"].is_null());
    assert_eq!(refs_of_prop(c, "annotatedElement"), [v.as_str()]);
    assert!(refs_of_prop(c, "ownedAnnotation").is_empty());
    assert!(refs_of_prop(find_id(elements, &v), "ownedAnnotation").is_empty());

    // An implicit annotation: no Annotation at all, the owner is annotated.
    let doc = elements
        .iter()
        .find(|e| e["@type"] == "Documentation")
        .expect("one doc");
    assert!(refs_of_prop(doc, "annotation").is_empty());
    assert!(refs_of_prop(doc, "ownedAnnotatingRelationship").is_empty());
    assert_eq!(refs_of_prop(doc, "annotatedElement"), [p.as_str()]);

    // Prefix metadata rides an owning membership of the annotated usage.
    let part = elem_id(find_named(elements, "p"));
    let metadata_owned_by = |owner: &str| {
        elements
            .iter()
            .find(|e| {
                e["@type"] == "MetadataUsage" && ref_of_prop(e, "owner").as_deref() == Some(owner)
            })
            .unwrap_or_else(|| panic!("no metadata usage owned by {owner}"))
    };
    let meta = metadata_owned_by(&part);
    assert!(meta["owningAnnotatingRelationship"].is_null());
    assert!(refs_of_prop(meta, "annotation").is_empty());
    assert_eq!(refs_of_prop(meta, "annotatedElement"), [part.as_str()]);
    assert!(refs_of_prop(find_id(elements, &part), "ownedAnnotation").is_empty());

    // A metadata usage with an `about` clause owns its Annotation like a
    // comment does.
    let about_meta = metadata_owned_by(&p);
    let about_id = elem_id(about_meta);
    let [meta_ann] = owned_rels_of_kind(elements, "Annotation", &about_id)[..] else {
        panic!("the about metadata usage owns exactly one Annotation");
    };
    assert_eq!(
        ref_of_prop(meta_ann, "annotatingElement").as_deref(),
        Some(about_id.as_str())
    );
    assert_eq!(refs_of_prop(meta_ann, "source"), [about_id.as_str()]);
    assert_eq!(refs_of_prop(about_meta, "annotation"), [elem_id(meta_ann)]);
    assert_eq!(refs_of_prop(about_meta, "annotatedElement"), [v.as_str()]);
    assert!(about_meta["owningAnnotatingRelationship"].is_null());

    // Several `about` targets: one Annotation each, in declaration order.
    let c2 = find_named(elements, "C2");
    let w = elem_id(find_named(elements, "W"));
    assert_eq!(
        owned_rels_of_kind(elements, "Annotation", &elem_id(c2)).len(),
        2
    );
    assert_eq!(
        refs_of_prop(c2, "annotatedElement"),
        [v.as_str(), w.as_str()]
    );
    assert_eq!(refs_of_prop(c2, "annotation").len(), 2);
    assert_eq!(
        refs_of_prop(c2, "annotation"),
        refs_of_prop(c2, "ownedAnnotatingRelationship")
    );
}

/// A foreign prefix annotation remains an Annotation with its original
/// id and ownership. Full-form enrichment must not normalize it into a
/// different membership or project references to a reconstructed graph.
#[test]
fn prefix_annotation_shape_derives_from_compact() {
    const P: &str = "00000000-0000-4000-8000-000000000001";
    const M1: &str = "00000000-0000-4000-8000-000000000002";
    const X: &str = "00000000-0000-4000-8000-000000000003";
    const A1: &str = "00000000-0000-4000-8000-000000000004";
    const C1: &str = "00000000-0000-4000-8000-000000000005";
    const A2: &str = "00000000-0000-4000-8000-000000000006";
    // The Comment is owned by A1 (annotating X) and itself owns A2, an
    // `about` Annotation of the package.
    let payload = |spell_annotated: bool| {
        let mut annotation = json!({"@type": "Annotation", "@id": A1, "isImplied": false,
            "owningRelatedElement": {"@id": X}, "ownedRelatedElement": [{"@id": C1}]});
        if spell_annotated {
            annotation["annotatedElement"] = json!({"@id": X});
        }
        json!([
            {"@type": "Package", "@id": P, "declaredName": "P",
             "ownedRelationship": [{"@id": M1}]},
            {"@type": "OwningMembership", "@id": M1, "isImplied": false, "visibility": "public",
             "owningRelatedElement": {"@id": P}, "ownedRelatedElement": [{"@id": X}]},
            {"@type": "PartDefinition", "@id": X, "declaredName": "X",
             "owningRelationship": {"@id": M1}, "ownedRelationship": [{"@id": A1}]},
            {"@type": "Comment", "@id": C1, "body": "hi", "owningRelationship": {"@id": A1},
             "ownedRelationship": [{"@id": A2}]},
            {"@type": "Annotation", "@id": A2, "isImplied": false,
             "owningRelatedElement": {"@id": C1}, "annotatedElement": {"@id": P}},
            annotation,
        ])
    };
    for spell in [true, false] {
        let full = from_compact_value(payload(spell), &HashMap::new(), false);
        let elements = full.as_array().unwrap();
        // Untouched elements keep their ids.
        assert_eq!(find_id(elements, P)["@type"], "Package");
        assert_eq!(find_id(elements, X)["@type"], "PartDefinition");
        // The comment is still owned through the Annotation, annotating X and P.
        let comment = elements
            .iter()
            .find(|e| e["@type"] == "Comment")
            .expect("the comment survives");
        assert_eq!(comment["body"], "hi");
        assert_eq!(ref_of_prop(comment, "owner").as_deref(), Some(X));
        let annotated = refs_of_prop(comment, "annotatedElement");
        assert!(
            annotated.contains(&X.to_string()) && annotated.contains(&P.to_string()),
            "spell={spell}: {annotated:?}"
        );
        assert_eq!(elem_id(comment), C1, "the comment keeps its id");
        let annotation = find_id(elements, A1);
        assert_eq!(annotation["@type"], "Annotation");
        assert_eq!(
            ref_of_prop(annotation, "annotatingElement").as_deref(),
            Some(C1)
        );
        assert_eq!(
            ref_of_prop(comment, "owningAnnotatingRelationship").as_deref(),
            Some(A1)
        );
        assert_eq!(refs_of_prop(find_id(elements, X), "ownedAnnotation"), [A1]);
        assert!(refs_of_prop(find_id(elements, X), "ownedMembership").is_empty());
    }
}

/// The payload path emits exactly what the text path emits: a toolkit
/// payload converted with `from_compact_value` equals the full form of
/// the model it came from, id for id (the loader keeps the document's
/// ids), and a payload carrying foreign ids equals it under those ids.
#[test]
fn payload_route_matches_the_model_route() {
    let src = "package P {
        part def A { attribute x; attribute y = 3; }
        part def B :> A { part b : A; }
        import Q::*;
        alias C for B;
        comment about A /* about A */
    }
    package Q { part def D; }";
    let mut model = Model::new();
    model.add_source("m.sysml", src);
    assert!(!model.has_errors());
    let compact = sysmlv2_parser::json::model_to_compact_json(&model);
    let expected = model_to_full_json(&model);
    let by_id = |v: &Value| -> HashMap<String, String> {
        v.as_array()
            .unwrap()
            .iter()
            .map(|e| {
                (
                    e["@id"].as_str().unwrap().to_string(),
                    serde_json::to_string(e).unwrap(),
                )
            })
            .collect()
    };
    let want = by_id(&expected);

    // Same ids, same values.
    let got = by_id(&from_compact_value(compact.clone(), &HashMap::new(), true));
    assert_eq!(got.len(), want.len(), "element count");
    let mut differing = 0;
    for (id, el) in &want {
        if got.get(id) != Some(el) {
            differing += 1;
            if differing == 1 {
                let w: Value = serde_json::from_str(el).unwrap();
                let g: Value = got
                    .get(id)
                    .map(|s| serde_json::from_str(s).unwrap())
                    .unwrap_or(Value::Null);
                for (k, v) in w.as_object().unwrap() {
                    if g.get(k) != Some(v) {
                        eprintln!(
                            "differs at {id} ({}) key {k}: want {v} got {:?}",
                            w["@type"],
                            g.get(k)
                        );
                    }
                }
            }
        }
    }
    assert_eq!(differing, 0, "toolkit payload through the payload route");

    // Foreign ids: every id replaced consistently; the output equals the
    // model route's under the foreign ids.
    let mut map: HashMap<String, String> = HashMap::new();
    for e in compact.as_array().unwrap() {
        let id = e["@id"].as_str().unwrap();
        map.insert(
            id.to_string(),
            uuid::Uuid::new_v5(&uuid::Uuid::NAMESPACE_OID, format!("f:{id}").as_bytes())
                .to_string(),
        );
    }
    fn rewrite(v: &Value, map: &HashMap<String, String>) -> Value {
        match v {
            Value::Object(o) => Value::Object(
                o.iter()
                    .map(|(k, x)| {
                        let x = if (k == "@id"
                            || k == "elementId"
                            || k == "memberElementId"
                            || k == "ownedMemberElementId")
                            && x.is_string()
                        {
                            map.get(x.as_str().unwrap())
                                .map(|s| Value::String(s.clone()))
                                .unwrap_or_else(|| x.clone())
                        } else {
                            rewrite(x, map)
                        };
                        (k.clone(), x)
                    })
                    .collect(),
            ),
            Value::Array(a) => Value::Array(a.iter().map(|x| rewrite(x, map)).collect()),
            other => other.clone(),
        }
    }
    let foreign = rewrite(&compact, &map);
    let got = from_compact_value(foreign, &HashMap::new(), true);
    // Compare after mapping the expected form's ids the same way; the
    // implied relationships and recovery elements the emitter adds derive
    // fresh ids on both routes, so compare the user elements only.
    let expected_foreign = by_id(&rewrite(&expected, &map));
    let got = by_id(&got);
    let mut differing = 0;
    for old in map.keys() {
        let id = &map[old];
        if got.get(id) != expected_foreign.get(id) {
            differing += 1;
            if differing == 1 {
                eprintln!(
                    "foreign differs at {id}:\n  want {:?}\n  got  {:?}",
                    expected_foreign.get(id),
                    got.get(id)
                );
            }
        }
    }
    assert_eq!(differing, 0, "foreign-id payload through the payload route");
}

/// Under the closure policy the full form writes the closures and the
/// inheritance-aware properties over them; at the passthrough level the
/// closure names carry the catalog's empty value. A walk past the depth
/// budget refuses the emission.
#[test]
fn closure_policy_writes_the_closures() {
    use sysmlv2_parser::full::{EmissionError, EmissionPolicy, resolved_to_full_json};
    use sysmlv2_parser::json::{ClosurePolicy, ResolvedModel};
    use sysmlv2_parser::model::Model;
    let mut model = Model::new();
    model.add_source(
        "m.sysml",
        "package P { part def V { attribute mass; } part def W :> V { attribute extra; } package Q { part q; } package R { import Q::*; } }",
    );
    let mut r = ResolvedModel::build(&model);
    let find = |full: &serde_json::Value, name: &str| -> serde_json::Value {
        full.as_array()
            .unwrap()
            .iter()
            .find(|e| e["declaredName"] == name)
            .cloned()
            .expect(name)
    };
    let passthrough = resolved_to_full_json(&mut r, &model, EmissionPolicy::default()).unwrap();
    let w = find(&passthrough, "W");
    assert_eq!(w["inheritedFeature"], serde_json::json!([]));
    assert_eq!(w["feature"].as_array().unwrap().len(), 1);
    let closed = resolved_to_full_json(
        &mut r,
        &model,
        EmissionPolicy {
            closures: ClosurePolicy::Closure {
                include_implied: false,
            },
            ..EmissionPolicy::default()
        },
    )
    .unwrap();
    let w = find(&closed, "W");
    let mass_id = find(&closed, "mass")["@id"].clone();
    assert_eq!(
        w["inheritedFeature"],
        serde_json::json!([{ "@id": mass_id }])
    );
    assert_eq!(w["feature"].as_array().unwrap().len(), 2);
    assert_eq!(w["inheritedMembership"].as_array().unwrap().len(), 1);
    let rpkg = find(&closed, "R");
    assert_eq!(rpkg["importedMembership"].as_array().unwrap().len(), 1);
    assert_eq!(rpkg["membership"].as_array().unwrap().len(), 1);
    assert_eq!(find(&passthrough, "R")["membership"], serde_json::json!([]));
    // The policy is restored after the emission.
    assert_eq!(r.closure_policy(), ClosurePolicy::Passthrough);
    // A heritage deeper than the budget.
    let mut src = String::from("package P { part def D0;");
    for i in 1..=26 {
        src.push_str(&format!(" part def D{i} :> D{};", i - 1));
    }
    src.push('}');
    let mut deep = Model::new();
    deep.add_source("d.sysml", &src);
    let mut r = ResolvedModel::build(&deep);
    let err = resolved_to_full_json(
        &mut r,
        &deep,
        EmissionPolicy {
            closures: ClosurePolicy::Closure {
                include_implied: false,
            },
            ..EmissionPolicy::default()
        },
    )
    .unwrap_err();
    assert!(
        matches!(err, EmissionError::TruncatedClosures { ref elements } if !elements.is_empty())
    );
    // Restored after the refusal too.
    assert_eq!(r.closure_policy(), ClosurePolicy::Passthrough);
    assert!(resolved_to_full_json(&mut r, &deep, EmissionPolicy::default()).is_ok());
}
