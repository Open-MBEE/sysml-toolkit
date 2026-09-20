//! Tests for the compact JSON serialization (KerML clause 10.4, compact form).

#![cfg(feature = "json")]

use serde_json::Value;
use sysmlv2_parser::json::to_compact_json;
use sysmlv2_parser::parser::parse_source;

fn emit(src: &str) -> Vec<Value> {
    let parse = parse_source(src);
    assert!(parse.diagnostics.is_empty(), "{:?}", parse.diagnostics);
    let Value::Array(elements) = to_compact_json(&parse.unit) else {
        panic!("expected a flat JSON array (KerML 10.4.6)")
    };
    elements
}

fn find<'a>(elements: &'a [Value], ty: &str) -> &'a Value {
    elements
        .iter()
        .find(|e| e["@type"] == ty)
        .unwrap_or_else(|| panic!("no {ty} in output"))
}

fn all<'a>(elements: &'a [Value], ty: &str) -> Vec<&'a Value> {
    elements.iter().filter(|e| e["@type"] == ty).collect()
}

fn by_id<'a>(elements: &'a [Value], id: &Value) -> &'a Value {
    let id = id["@id"].as_str().expect("expected an {\"@id\"} reference");
    elements
        .iter()
        .find(|e| e["@id"] == id)
        .unwrap_or_else(|| panic!("dangling @id {id}"))
}

#[test]
fn flat_array_with_type_and_id() {
    let elements = emit("package P;");
    // Root namespace + OwningMembership + Package.
    assert_eq!(elements.len(), 3);
    for e in &elements {
        assert!(e["@type"].is_string());
        assert!(e["@id"].is_string());
        assert_eq!(e["@id"], e["elementId"], "@id must equal elementId");
        // Compact form: no implied relationships were added.
        assert_eq!(e["isImpliedIncluded"], false);
    }
    let pkg = find(&elements, "Package");
    assert_eq!(pkg["declaredName"], "P");
}

#[test]
fn ownership_is_by_reference_not_nesting() {
    let elements = emit("package P { part def V; }");
    let pkg = find(&elements, "Package");
    // Package owns an OwningMembership which owns the PartDefinition.
    let rel_ref = &pkg["ownedRelationship"][0];
    let membership = by_id(&elements, rel_ref);
    assert_eq!(membership["@type"], "OwningMembership");
    assert_eq!(membership["visibility"], "public");
    assert_eq!(membership["isImplied"], false);
    let def = by_id(&elements, &membership["ownedRelatedElement"][0]);
    assert_eq!(def["@type"], "PartDefinition");
    assert_eq!(def["declaredName"], "V");
    // Back-links.
    assert_eq!(
        membership["owningRelatedElement"]["@id"], pkg["@id"],
        "membership must point back to its owning package"
    );
    assert_eq!(def["owningRelationship"]["@id"], membership["@id"]);
}

#[test]
fn deterministic_ids() {
    let a = emit("package P { part def V; }");
    let b = emit("package P { part def V; }");
    assert_eq!(a, b, "same source must serialize identically");
}

#[test]
fn triggered_accept_payload_name_is_not_a_typing() {
    let elements = emit("package P { action a { accept sig at clock; } }");
    let payload = all(&elements, "ReferenceUsage")
        .into_iter()
        .find(|e| e["declaredName"] == "sig")
        .expect("named accept payload");
    let payload_id = &payload["@id"];
    assert!(
        all(&elements, "FeatureTyping")
            .into_iter()
            .all(|typing| { typing["typedFeature"]["@id"] != *payload_id })
    );
    assert_eq!(all(&elements, "TriggerInvocationExpression").len(), 1);
}

#[test]
fn within_file_references_resolve_to_ids() {
    let elements = emit("package P { part def Wheel; part w : Wheel; }");
    let typing = find(&elements, "FeatureTyping");
    let wheel_def = find(&elements, "PartDefinition");
    assert_eq!(
        typing["type"]["@id"], wheel_def["@id"],
        "typing must resolve to the part definition"
    );
    let usage = find(&elements, "PartUsage");
    assert_eq!(typing["typedFeature"]["@id"], usage["@id"]);
}

#[test]
fn specialization_resolves_across_nesting() {
    let elements = emit(
        "package Lib { part def Base; }
         package P {
            import Lib::*;
            part def Car :> Base;
         }",
    );
    let sub = find(&elements, "Subclassification");
    let base = all(&elements, "PartDefinition")
        .into_iter()
        .find(|d| d["declaredName"] == "Base")
        .unwrap();
    assert_eq!(sub["superclassifier"]["@id"], base["@id"]);
    assert_eq!(sub["isImplied"], false);
}

#[test]
fn unresolved_library_reference_becomes_at_ref() {
    let elements = emit("package P { attribute m : ScalarValues::Real; }");
    let typing = find(&elements, "FeatureTyping");
    assert_eq!(typing["type"]["@ref"], "ScalarValues::Real");
}

#[test]
fn feature_value_and_literals() {
    let elements = emit("package P { attribute a : X = 2 + 3.5; }");
    let fv = find(&elements, "FeatureValue");
    assert_eq!(fv["isInitial"], false);
    assert_eq!(fv["isDefault"], false);
    let op = find(&elements, "OperatorExpression");
    assert_eq!(op["operator"], "+");
    let int = find(&elements, "LiteralInteger");
    assert_eq!(int["value"], 2);
    let real = find(&elements, "LiteralRational");
    assert_eq!(real["value"], 3.5);
}

/// A real literal a double cannot denote exactly travels as its written
/// text, and lifts back to that same text — the JSON-path model and the
/// text-path model agree on the value either way.
#[test]
fn real_literals_beyond_double_precision_travel_as_text() {
    use sysmlv2_parser::lift::from_compact_json;
    use sysmlv2_parser::print::print_source;
    for (written, wire) in [
        // Exactly representable: a number, as before.
        ("3.5", Value::from(3.5)),
        ("0.1", Value::from(0.1)),
        // More significant digits than a double holds.
        (
            "1.234567890123456789012345678901",
            Value::from("1.234567890123456789012345678901"),
        ),
        // An exponent past the double range, which would otherwise
        // become an infinity — and JSON has no spelling for that.
        ("1e400", Value::from("1e400")),
    ] {
        let elements = emit(&format!("package P {{ attribute a = {written}; }}"));
        let real = find(&elements, "LiteralRational");
        assert_eq!(real["value"], wire, "wire value of {written}");

        let lifted = from_compact_json(&Value::Array(elements)).expect("lift");
        assert!(lifted.errors.is_empty(), "{:?}", lifted.errors);
        let text = print_source(&lifted.unit);
        assert!(
            text.contains(written),
            "{written} survives the lift: {text}"
        );
    }
}

#[test]
fn initial_and_default_value_flags() {
    let elements = emit("package P { attribute a : X := 1; }");
    let fv = find(&elements, "FeatureValue");
    assert_eq!(fv["isInitial"], true);

    let elements = emit("package P { attribute a : X default = 1; }");
    let fv = find(&elements, "FeatureValue");
    assert_eq!(fv["isDefault"], true);
}

#[test]
fn multiplicity_range() {
    let elements = emit("package P { part w : W[0..*]; }");
    let mr = find(&elements, "MultiplicityRange");
    assert!(mr["ownedRelationship"].as_array().unwrap().len() == 2);
    find(&elements, "LiteralInfinity");
}

#[test]
fn usage_flags_and_direction() {
    let elements = emit("package P { in ref part x : T[2] ordered nonunique; }");
    let usage = find(&elements, "PartUsage");
    assert_eq!(usage["direction"], "in");
    assert_eq!(usage["isOrdered"], true);
    assert_eq!(usage["isUnique"], false, "nonunique => isUnique: false");
}

#[test]
fn imports_and_alias() {
    let elements = emit(
        "package P {
            private import Lib::*;
            import Other::Thing;
            alias t for Other::Thing;
        }",
    );
    let ns_import = find(&elements, "NamespaceImport");
    assert_eq!(ns_import["visibility"], "private");
    assert_eq!(ns_import["importedNamespace"]["@ref"], "Lib");
    let m_import = find(&elements, "MembershipImport");
    assert_eq!(m_import["importedMembership"]["@ref"], "Other::Thing");
    let alias = find(&elements, "Membership");
    assert_eq!(alias["memberName"], "t");
}

/// A bracket-filtered import owns an implicit anonymous FilterPackage
/// (SysML.xtext `FilterPackage`): the outer relationship is the namespace
/// kind and imports an owned anonymous Package holding the actual import
/// (public — the outer import sees only visible memberships) plus one
/// private ElementFilterMembership per bracket.
#[test]
fn bracket_filtered_import_owns_a_filter_package() {
    let elements = emit(
        "package P {
            metadata def Safety;
            part vehicle;
            public import vehicle::**[@Safety];
        }",
    );
    let outer = find(&elements, "NamespaceImport");
    assert_eq!(outer["visibility"], "public");
    assert_eq!(outer["isRecursive"], false, "::** rides the inner import");
    let pkg = by_id(&elements, &outer["importedNamespace"]);
    assert_eq!(pkg["@type"], "Package");
    assert_eq!(pkg["declaredName"], Value::Null);
    assert_eq!(
        pkg["owningRelationship"]["@id"], outer["@id"],
        "the filter package is the import's own ownedRelatedElement"
    );
    let inner = find(&elements, "MembershipImport");
    assert_eq!(inner["visibility"], "public");
    assert_eq!(inner["isRecursive"], true);
    assert_eq!(inner["owningRelatedElement"]["@id"], pkg["@id"]);
    let efm = find(&elements, "ElementFilterMembership");
    assert_eq!(efm["visibility"], "private", "`[` maps to private");
    assert_eq!(efm["owningRelatedElement"]["@id"], pkg["@id"]);
}

#[test]
fn documentation_and_comment_bodies() {
    let elements = emit("package P { doc /* the docs */ }");
    let doc = find(&elements, "Documentation");
    // Body normalized like the pilot's `processCommentBody`: delimiters
    // and leading whitespace stripped (trailing kept).
    assert_eq!(doc["body"], "the docs ");
}

#[test]
fn variant_membership() {
    let elements = emit("package P { variation part def W { variant part w1 : W; } }");
    find(&elements, "VariantMembership");
    let def = find(&elements, "PartDefinition");
    assert_eq!(def["isVariation"], true);
}

#[test]
fn state_machine_lowering() {
    let elements = emit(
        "package P {
            state def S {
                entry action init;
                state off;
                transition first off if go then on;
                state on;
            }
        }",
    );
    let sub = find(&elements, "StateSubactionMembership");
    assert_eq!(sub["kind"], "entry");
    let t = find(&elements, "TransitionUsage");
    // Guard is owned via a TransitionFeatureMembership of kind "guard".
    let guard_rel = all(&elements, "TransitionFeatureMembership")
        .into_iter()
        .find(|r| r["kind"] == "guard")
        .expect("guard membership");
    assert_eq!(guard_rel["owningRelatedElement"]["@id"], t["@id"]);
    find(&elements, "SuccessionAsUsage");
}

#[test]
fn requirement_members_lowering() {
    let elements = emit(
        "package P {
            requirement def R {
                subject s : V;
                actor driver;
                require constraint { mass <= limit }
            }
        }",
    );
    find(&elements, "SubjectMembership");
    let actor = find(&elements, "ActorMembership");
    let part = by_id(&elements, &actor["ownedRelatedElement"][0]);
    assert_eq!(part["@type"], "PartUsage");
    let rc = find(&elements, "RequirementConstraintMembership");
    assert_eq!(rc["kind"], "requirement");
    find(&elements, "ResultExpressionMembership");
}

#[test]
fn connection_and_flow_lowering() {
    let elements = emit(
        "package P {
            part a { port x; }
            part b { port y; }
            connect a.x to b.y;
            flow of F from a.x to b.y;
        }",
    );
    // Two connector ends plus two flow ends, each via EndFeatureMembership.
    let ends = all(&elements, "EndFeatureMembership");
    assert_eq!(ends.len(), 4);
    find(&elements, "PayloadFeature");
    assert_eq!(all(&elements, "FlowEnd").len(), 2);
}

#[test]
fn dependency_lowering() {
    let elements = emit("package P { part def A; part def B; dependency A to B; }");
    let dep = find(&elements, "Dependency");
    let a = all(&elements, "PartDefinition")
        .into_iter()
        .find(|d| d["declaredName"] == "A")
        .unwrap();
    assert_eq!(dep["client"][0]["@id"], a["@id"]);
    assert_eq!(dep["supplier"].as_array().unwrap().len(), 1);
}

#[test]
fn metadata_lowering() {
    let elements = emit(
        "package P {
            metadata def Safety;
            #Safety part def Brake;
        }",
    );
    let mu = find(&elements, "MetadataUsage");
    let typing = find(&elements, "FeatureTyping");
    let def = find(&elements, "MetadataDefinition");
    assert_eq!(typing["type"]["@id"], def["@id"]);
    assert_eq!(typing["owningRelatedElement"]["@id"], mu["@id"]);
}

#[test]
fn every_owned_relationship_reference_is_valid() {
    let elements = emit(
        "package Demo {
            import Lib::*;
            part def Vehicle :> Base {
                doc /* a vehicle */
                attribute mass : Real = 1500.0;
                part wheels : Wheel[4];
            }
            part myCar : Vehicle {
                attribute :>> mass = 1800.0;
            }
         }",
    );
    for e in &elements {
        for r in e["ownedRelationship"].as_array().unwrap() {
            by_id(&elements, r);
        }
        if let Some(rels) = e["ownedRelatedElement"].as_array() {
            for r in rels {
                by_id(&elements, r);
            }
        }
    }
}

#[test]
fn metadata_body_implicit_redefinition_lowers_like_explicit() {
    // `@M { ref M::kind = 1; }` and `@M { M::kind = 1; }` are implicit
    // spellings of `@M { :>> M::kind = 1; }` (SysML.xtext
    // `MetadataBodyUsage`) and must lower to byte-identical JSON:
    // an unnamed ReferenceUsage owning a Redefinition.
    let src = |spelling: &str| {
        format!(
            "package P {{
                metadata def M {{ attribute kind : Integer; }}
                part a {{ @M {{ {spelling} }} }}
            }}"
        )
    };
    let explicit = emit(&src(":>> M::kind = 1;"));
    for spelling in ["ref M::kind = 1;", "M::kind = 1;", "ref :>> M::kind = 1;"] {
        assert_eq!(emit(&src(spelling)), explicit, "{spelling}");
    }
    let ru = all(&explicit, "ReferenceUsage");
    assert_eq!(ru.len(), 1);
    assert!(ru[0]["declaredName"].is_null());
    let redef = find(&explicit, "Redefinition");
    assert!(redef["redefinedFeature"]["@id"].is_string());

    let chain_src = |spelling: &str| {
        format!(
            "package P {{
                metadata def M;
                part a {{ @M {{ {spelling} }} }}
            }}"
        )
    };
    assert_eq!(
        emit(&chain_src("outer.inner = 1;")),
        emit(&chain_src(":>> outer.inner = 1;"))
    );
}
