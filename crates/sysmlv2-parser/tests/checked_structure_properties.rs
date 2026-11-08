//! The checked reads over a member's structure: a connector's ends
//! (`connectorEnd`, `endFeature`) and the features they reference
//! (`sourceFeature`, `targetFeature`), a flow's `payloadType`, an accept
//! action's `payloadParameter`, the subject parameter of requirements and
//! cases, a requirement usage's `requirementDefinition` and a
//! satisfaction's `satisfyingFeature`, each over the standard library on
//! the issue's model, and the refusals that name what is missing.

#![cfg(feature = "json")]

use serde_json::{Value, json};
use sysmlv2_parser::{
    json::{
        ClosurePolicy, Derived, DerivedValue, FeatureStructureIssue, PropertyError, Reference,
        ResolvedModel,
    },
    model::{GraphFormat, Model},
};

const NEEDS: &str = "package Needs {
    port def Out { out attribute v : ScalarValues::Real; }
    part def Box {
        port o : Out;
        port i : ~Out;
        attribute x : ScalarValues::Real = 1.0 + 2.0;
    }
    part def Sys {
        part a : Box;
        part b : Box;
        connect a.o to b.i;
        flow of ScalarValues::Real from a.o.v to b.i.v;
    }
    requirement def R { subject s : Sys; }
    requirement r : R;
    part sys : Sys;
    satisfy r by sys;
    action def Listen { accept sig : ScalarValues::Real; }
    action def Steps { action s1; action s2; first s1 then s2; }
}";

fn model_with(format: GraphFormat, sources: &[(&str, &str)], clean: bool) -> ResolvedModel {
    let mut model = Model::with_graph_format(format);
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    for (name, text) in sources {
        let unit = model.add_source(*name, text);
        if clean {
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        }
    }
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}

fn model() -> ResolvedModel {
    model_with(GraphFormat::LegacyV2, &[("needs.sysml", NEEDS)], true)
}

/// The compatibility value of `name` as the checked reader would spell it:
/// local elements by id; the values compared here never leave the model.
fn derived_json(r: &mut ResolvedModel, e: sysmlv2_parser::json::ElementRef, name: &str) -> Value {
    let Derived::Value(value) = r.derived(e, name) else {
        panic!("{name} is not derived");
    };
    let id = |e| json!({"@id": r.element_id(e).to_string()});
    let reference = |reference: &Reference| match reference {
        Reference::Element(e) => id(*e),
        other => panic!("{name}: {other:?} leaves the model"),
    };
    match &value {
        DerivedValue::Null => Value::Null,
        DerivedValue::Element(e) => id(*e),
        DerivedValue::Elements(es) => Value::Array(es.iter().map(|&e| id(e)).collect()),
        DerivedValue::Reference(r) => reference(r),
        DerivedValue::References(rs) => Value::Array(rs.iter().map(reference).collect()),
        other => panic!("{name}: unexpected {other:?}"),
    }
}

/// The one user element of `metaclass` owned by `owner`.
fn sole(r: &mut ResolvedModel, metaclass: &str, owner: &str) -> sysmlv2_parser::json::ElementRef {
    let user: std::collections::HashSet<_> = r.user_elements().collect();
    let found: Vec<_> = r
        .elements_of_metaclass(metaclass)
        .into_iter()
        .filter(|e| user.contains(e))
        .filter(|&e| {
            r.owner(e)
                .and_then(|o| r.element_qualified_name(o))
                .as_deref()
                == Some(owner)
        })
        .collect();
    assert_eq!(found.len(), 1, "{metaclass} under {owner}: {found:?}");
    found[0]
}

/// A reference value as the element's qualified name, or its metaclass and
/// effective or lookup name where an ancestor is anonymous.
fn describe(r: &mut ResolvedModel, value: &serde_json::Value) -> String {
    let id = value["@id"]
        .as_str()
        .unwrap_or_else(|| panic!("not a reference: {value}"));
    let e = r.element_by_id(id).unwrap();
    r.element_qualified_name(e).unwrap_or_else(|| {
        let name = r
            .element_effective_name(e)
            .or_else(|| r.element_lookup_name(e))
            .unwrap_or_else(|| "(anonymous)".into());
        format!("{} {name}", r.element_type(e))
    })
}

/// `name` of `e` through the checked reader, described.
fn read(r: &mut ResolvedModel, e: sysmlv2_parser::json::ElementRef, name: &str) -> String {
    let value = r
        .property(e, name)
        .unwrap_or_else(|err| panic!("{name}: {err}"));
    assert!(value.is_object(), "{name}: not one reference: {value}");
    describe(r, &value)
}

fn read_all(r: &mut ResolvedModel, e: sysmlv2_parser::json::ElementRef, name: &str) -> Vec<String> {
    let value = r
        .property(e, name)
        .unwrap_or_else(|err| panic!("{name}: {err}"));
    describe_all(r, &value)
}

fn describe_all(r: &mut ResolvedModel, value: &serde_json::Value) -> Vec<String> {
    value
        .as_array()
        .unwrap_or_else(|| panic!("not a list: {value}"))
        .iter()
        .map(|v| describe(r, v))
        .collect()
}

/// The names of the features a chain feature chains, for an end that
/// references `a.o`.
fn chain(r: &mut ResolvedModel, value: &serde_json::Value) -> Vec<String> {
    let id = value["@id"].as_str().unwrap();
    let e = r.element_by_id(id).unwrap();
    let links = r.property(e, "chainingFeature").unwrap();
    describe_all(r, &links)
}

#[test]
fn connector_ends_certify_on_connections_and_flows() {
    let mut r = model();
    let connection = sole(&mut r, "ConnectionUsage", "Needs::Sys");
    let flow = sole(&mut r, "FlowUsage", "Needs::Sys");
    for (connector, kind) in [(connection, "ReferenceUsage"), (flow, "FlowEnd")] {
        for name in ["connectorEnd", "endFeature"] {
            let ends = r.property(connector, name).unwrap();
            assert_eq!(
                describe_all(&mut r, &ends),
                [format!("{kind} source"), format!("{kind} target")],
                "{name}"
            );
        }
    }
    // The ends of a binary connector reference the chains `a.o` and `b.i`.
    for connector in [connection, flow] {
        let source = r.property(connector, "sourceFeature").unwrap();
        assert_eq!(chain(&mut r, &source), ["Needs::Sys::a", "Needs::Box::o"]);
        let targets = r.property(connector, "targetFeature").unwrap();
        let targets = targets.as_array().unwrap();
        assert_eq!(targets.len(), 1);
        assert_eq!(
            chain(&mut r, &targets[0]),
            ["Needs::Sys::b", "Needs::Box::i"]
        );
    }
    // The strict reads agree with the compatibility values.
    for connector in [connection, flow] {
        for name in [
            "connectorEnd",
            "relatedFeature",
            "sourceFeature",
            "targetFeature",
        ] {
            let strict = r.property(connector, name).unwrap();
            let compatibility = derived_json(&mut r, connector, name);
            assert_eq!(strict, compatibility, "{name}");
        }
    }
}

#[test]
fn kernel_connectors_read_their_related_features_by_position() {
    let mut r = model_with(
        GraphFormat::LegacyV2,
        &[(
            "links.kerml",
            "package K {
                class A; class B;
                assoc Z { end feature za : A; end feature zb : B; }
                class H {
                    feature x : A; feature y : B; feature z : B;
                    connector c from x to y;
                    connector n (x, y, z);
                    connector k : Z;
                    connector twice (x, y, y);
                    connector mixed { end e1 : A; end e2 references y; }
                }
            }",
        )],
        true,
    );
    let c = r.resolve_qualified("K::H::c").unwrap();
    assert_eq!(read(&mut r, c, "sourceFeature"), "K::H::x");
    assert_eq!(read_all(&mut r, c, "targetFeature"), ["K::H::y"]);
    assert_eq!(read_all(&mut r, c, "connectorEnd").len(), 2);
    // `relatedFeature` is the ends' features in end order, nothing dropped
    // but an end without a reference, nothing deduplicated; a connector's
    // `relatedElement` reads the same.
    assert_eq!(
        read_all(&mut r, c, "relatedFeature"),
        ["K::H::x", "K::H::y"]
    );
    assert_eq!(
        r.property(c, "relatedElement").unwrap(),
        r.property(c, "relatedFeature").unwrap()
    );
    // An n-ary connector: the first related feature, then the rest as an
    // ordered set.
    let n = r.resolve_qualified("K::H::n").unwrap();
    assert_eq!(read_all(&mut r, n, "connectorEnd").len(), 3);
    assert_eq!(read(&mut r, n, "sourceFeature"), "K::H::x");
    assert_eq!(read_all(&mut r, n, "targetFeature"), ["K::H::y", "K::H::z"]);
    let twice = r.resolve_qualified("K::H::twice").unwrap();
    assert_eq!(read_all(&mut r, twice, "targetFeature"), ["K::H::y"]);
    assert_eq!(
        read_all(&mut r, twice, "relatedFeature"),
        ["K::H::x", "K::H::y", "K::H::y"]
    );
    // Inherited ends reference nothing of their own: no related features.
    let k = r.resolve_qualified("K::H::k").unwrap();
    assert_eq!(
        read_all(&mut r, k, "connectorEnd"),
        ["K::Z::za", "K::Z::zb"]
    );
    assert_eq!(r.property(k, "sourceFeature").unwrap(), Value::Null);
    assert_eq!(read_all(&mut r, k, "targetFeature"), Vec::<String>::new());
    // An end declared without a reference keeps its position: the source
    // stays empty, the referenced second end is the target.
    let mixed = r.resolve_qualified("K::H::mixed").unwrap();
    assert_eq!(r.property(mixed, "sourceFeature").unwrap(), Value::Null);
    assert_eq!(read_all(&mut r, mixed, "targetFeature"), ["K::H::y"]);
    assert_eq!(read_all(&mut r, mixed, "relatedFeature"), ["K::H::y"]);
    assert_eq!(read_all(&mut r, k, "relatedFeature"), Vec::<String>::new());
    for connector in [c, n, twice, k, mixed] {
        for name in ["sourceFeature", "targetFeature"] {
            let strict = r.property(connector, name).unwrap();
            assert_eq!(strict, derived_json(&mut r, connector, name), "{name}");
        }
    }
}

#[test]
fn connection_ends_without_a_reference_hold_their_position() {
    let mut r = model_with(
        GraphFormat::LegacyV2,
        &[(
            "typed.sysml",
            "package T {
                part def A; part def B;
                connection def C { end a : A; end b : B; }
                part def Hold {
                    part a : A; part b : B; part c : B;
                    connection typed : C;
                    connection declared : C { end x : A; end y : B; }
                    connection subsetting : C { end x subsets a; end y subsets b; }
                    connection mixed : C { end x : A; end y ::> b; }
                    connect (a, b, c);
                }
            }",
        )],
        true,
    );
    for name in ["T::Hold::typed", "T::Hold::declared", "T::Hold::subsetting"] {
        let connection = r.resolve_qualified(name).unwrap();
        assert_eq!(
            r.property(connection, "sourceFeature").unwrap(),
            Value::Null,
            "{name}"
        );
        assert_eq!(
            read_all(&mut r, connection, "targetFeature"),
            Vec::<String>::new(),
            "{name}"
        );
        assert_eq!(
            read_all(&mut r, connection, "connectorEnd").len(),
            2,
            "{name}"
        );
    }
    // A first end without a reference leaves the source empty; the second
    // end's feature is the target, as the compatibility read has it.
    let mixed = r.resolve_qualified("T::Hold::mixed").unwrap();
    assert_eq!(r.property(mixed, "sourceFeature").unwrap(), Value::Null);
    assert_eq!(read_all(&mut r, mixed, "targetFeature"), ["T::Hold::b"]);
    let user: std::collections::HashSet<_> = r.user_elements().collect();
    let nary = r
        .elements_of_metaclass("ConnectionUsage")
        .into_iter()
        .find(|e| user.contains(e) && r.element_name(*e).is_none())
        .unwrap();
    assert_eq!(read(&mut r, nary, "sourceFeature"), "T::Hold::a");
    assert_eq!(
        read_all(&mut r, nary, "targetFeature"),
        ["T::Hold::b", "T::Hold::c"]
    );
    // The relationship names take the list shape of their own declaration.
    assert_eq!(read_all(&mut r, nary, "source"), ["T::Hold::a"]);
    assert_eq!(
        read_all(&mut r, nary, "target"),
        ["T::Hold::b", "T::Hold::c"]
    );
    // Every shape agrees with the compatibility read.
    for name in [
        "T::Hold::typed",
        "T::Hold::declared",
        "T::Hold::subsetting",
        "T::Hold::mixed",
    ] {
        let connection = r.resolve_qualified(name).unwrap();
        for property in ["sourceFeature", "targetFeature"] {
            let strict = r.property(connection, property).unwrap();
            assert_eq!(
                strict,
                derived_json(&mut r, connection, property),
                "{name}.{property}"
            );
        }
    }
    for property in ["sourceFeature", "targetFeature"] {
        let strict = r.property(nary, property).unwrap();
        assert_eq!(strict, derived_json(&mut r, nary, property), "{property}");
    }
}

#[test]
fn an_end_whose_reference_never_resolved_is_refused_by_its_spelling() {
    let mut r = model_with(
        GraphFormat::LegacyV2,
        &[(
            "dangling.sysml",
            "package D { part def P { part a; connect a to nowhere; } }",
        )],
        false,
    );
    let connection = sole(&mut r, "ConnectionUsage", "D::P");
    assert_eq!(
        r.property(connection, "targetFeature"),
        Err(PropertyError::UnresolvedReference("nowhere".into()))
    );
    assert_eq!(read(&mut r, connection, "sourceFeature"), "D::P::a");
}

#[test]
fn payload_type_and_payload_parameter() {
    let mut r = model();
    let flow = sole(&mut r, "FlowUsage", "Needs::Sys");
    assert_eq!(
        read_all(&mut r, flow, "payloadType"),
        ["ScalarValues::Real"]
    );
    assert_eq!(
        read(&mut r, flow, "payloadFeature"),
        "PayloadFeature payload"
    );
    // A flow carries its payload type through `Flow::payloadType`, not the
    // accept action's `payloadParameter`.
    assert_eq!(
        r.property(flow, "payloadParameter"),
        Err(PropertyError::NotDeclared)
    );
    // A flow without a payload has no payload types.
    let mut bare = model_with(
        GraphFormat::LegacyV2,
        &[(
            "bare.sysml",
            "package Bare {
                port def Out { out attribute v : ScalarValues::Real; }
                part def Box { port o : Out; port i : ~Out; }
                part def Sys { part a : Box; part b : Box; flow from a.o.v to b.i.v; }
            }",
        )],
        true,
    );
    let flow = sole(&mut bare, "FlowUsage", "Bare::Sys");
    assert_eq!(bare.property(flow, "payloadFeature").unwrap(), Value::Null);
    assert_eq!(
        read_all(&mut bare, flow, "payloadType"),
        Vec::<String>::new()
    );
    let accept = sole(&mut r, "AcceptActionUsage", "Needs::Listen");
    assert_eq!(
        read(&mut r, accept, "payloadParameter"),
        "ReferenceUsage sig"
    );
    let strict = r.property(accept, "payloadParameter").unwrap();
    assert_eq!(strict, derived_json(&mut r, accept, "payloadParameter"));
}

#[test]
fn subject_parameters_requirement_definitions_and_satisfying_features() {
    let mut r = model();
    let definition = r.resolve_qualified("Needs::R").unwrap();
    let requirement = r.resolve_qualified("Needs::r").unwrap();
    let satisfaction = sole(&mut r, "SatisfyRequirementUsage", "Needs");
    assert_eq!(read(&mut r, definition, "subjectParameter"), "Needs::R::s");
    // The usage inherits its definition's subject membership.
    assert_eq!(read(&mut r, requirement, "subjectParameter"), "Needs::R::s");
    // The satisfaction owns a subject of its own, bound to the satisfying part.
    assert_eq!(
        read(&mut r, satisfaction, "subjectParameter"),
        "ReferenceUsage s"
    );
    assert_eq!(
        read(&mut r, satisfaction, "satisfyingFeature"),
        "Needs::sys"
    );
    // The definition is read under every name the redefinition chain gives
    // it, in the shape the requested declaration has.
    for (receiver, name) in [
        (requirement, "requirementDefinition"),
        (requirement, "constraintDefinition"),
        (requirement, "predicate"),
        (requirement, "function"),
        (satisfaction, "requirementDefinition"),
    ] {
        assert_eq!(read(&mut r, receiver, name), "Needs::R", "{name}");
    }
    assert_eq!(read_all(&mut r, requirement, "behavior"), ["Needs::R"]);
    for (receiver, name) in [
        (definition, "subjectParameter"),
        (requirement, "subjectParameter"),
        (satisfaction, "subjectParameter"),
        (satisfaction, "satisfyingFeature"),
        (requirement, "requirementDefinition"),
    ] {
        let strict = r.property(receiver, name).unwrap();
        assert_eq!(strict, derived_json(&mut r, receiver, name), "{name}");
    }
}

#[test]
fn an_owned_subject_shadows_the_inherited_one_on_requirements_and_cases() {
    let mut r = model_with(
        GraphFormat::LegacyV2,
        &[(
            "cases.sysml",
            "package Claims {
                part def Sys;
                requirement def R { subject s : Sys; }
                requirement r2 : R { subject s2 : Sys; }
                case def UCD { subject u : Sys; }
                case uc : UCD;
                analysis def AD { subject z : Sys; }
                analysis an : AD;
                verification def VD { subject v : Sys; }
                verification vc : VD { subject v2 : Sys; }
            }",
        )],
        true,
    );
    for (name, subject) in [
        ("Claims::r2", "Claims::r2::s2"),
        ("Claims::UCD", "Claims::UCD::u"),
        ("Claims::uc", "Claims::UCD::u"),
        ("Claims::AD", "Claims::AD::z"),
        ("Claims::an", "Claims::AD::z"),
        ("Claims::VD", "Claims::VD::v"),
        ("Claims::vc", "Claims::vc::v2"),
    ] {
        let e = r
            .resolve_qualified(name)
            .unwrap_or_else(|| panic!("{name} does not resolve"));
        assert_eq!(read(&mut r, e, "subjectParameter"), subject, "{name}");
        let strict = r.property(e, "subjectParameter").unwrap();
        assert_eq!(
            strict,
            derived_json(&mut r, e, "subjectParameter"),
            "{name}"
        );
    }
}

#[test]
fn satisfactions_without_a_binding_are_refused_with_the_missing_step() {
    let mut r = model_with(
        GraphFormat::LegacyV2,
        &[(
            "claims.sysml",
            "package C {
                part def Sys;
                requirement def R { subject s : Sys; }
                requirement r : R;
                part sys : Sys;
                satisfy r;
                satisfy requirement claim : R by sys;
                satisfy r by missing;
            }",
        )],
        false,
    );
    let claims: Vec<_> = r
        .elements_of_metaclass("SatisfyRequirementUsage")
        .into_iter()
        .filter(|&e| r.user_elements().any(|u| u == e))
        .collect();
    assert_eq!(claims.len(), 3);
    // Without `by`, the subject is the requirement's, which nothing binds.
    assert_eq!(
        r.property(claims[0], "satisfyingFeature"),
        Err(PropertyError::IncompleteFeatureStructure(
            FeatureStructureIssue::SubjectWithoutValue
        ))
    );
    assert_eq!(read(&mut r, claims[1], "satisfyingFeature"), "C::sys");
    assert_eq!(
        r.property(claims[2], "satisfyingFeature"),
        Err(PropertyError::UnresolvedReference("missing".into()))
    );
}

#[test]
fn operator_arguments_answer_on_both_formats() {
    let mut r = model();
    let x = r.resolve_qualified("Needs::Box::x").unwrap();
    let sum = sole(&mut r, "OperatorExpression", "Needs::Box::x");
    assert_eq!(r.element_qualified_name(x), Some("Needs::Box::x".into()));
    // The operator's arguments certify through each parameter's implied
    // redefinition of the library function's input, a row the planner writes
    // from the expression's typing by `DataFunctions::'+'` on both formats:
    // the two literal operands, in order, the same elements under either
    // graph.
    let legacy = r.property(sum, "argument").unwrap();
    let legacy = legacy.as_array().unwrap();
    assert_eq!(legacy.len(), 2, "{legacy:?}");
    let mut canonical = model_with(GraphFormat::CanonicalV3, &[("needs.sysml", NEEDS)], true);
    let sum = sole(&mut canonical, "OperatorExpression", "Needs::Box::x");
    let v3 = canonical.property(sum, "argument").unwrap();
    assert_eq!(v3.as_array().unwrap(), legacy);
}
