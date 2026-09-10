//! Full-form JSON gates: derived properties and implied
//! relationships, validated against the published normative schema.

#![cfg(feature = "json")]

use serde_json::Value;
use sysmlv2_parser::full::{model_to_full_json, to_full_json};
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::parse_source;

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
            failures.push(format!("{t} @ {}: {err}", err.instance_path));
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
    let parse = parse_source("package P { part def V; part v : V; }");
    let full = to_full_json(&parse.unit);
    let elements = full.as_array().unwrap();
    // No library → no implied relationships, flag stays false.
    assert!(elements.iter().all(|e| e["isImpliedIncluded"] == false));
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
