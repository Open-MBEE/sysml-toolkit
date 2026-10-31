#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{Reference, ResolvedModel, model_resolution_report},
    model::Model,
};

fn checked(source: &str) -> ResolvedModel {
    let mut model = Model::new();
    model.add_source("ends.sysml", source);
    assert!(!model.has_errors(), "{:?}", model.units()[0].diagnostics);
    let report = model_resolution_report(&model);
    assert!(report.unresolved.is_empty(), "{:?}", report.unresolved);
    assert!(report.ambiguous.is_empty(), "{:?}", report.ambiguous);
    ResolvedModel::build(&model)
}

#[test]
fn declared_connector_ends_keep_context_over_inherited_end_names() {
    for before in [true, false] {
        let actual = "port actual : Composite { port pin1 :> pin; }";
        let source = format!(
            "package P {{
                port def Pin;
                port def Composite {{ port pin : Pin[*]; }}
                interface def Fastener {{ end a: Pin; end b: Pin; }}
                interface def Hub {{
                    end left: Composite; end right: Composite;
                    interface fastener : Fastener connect left.pin to right.pin;
                }}
                part assembly {{
                    {}
                    interface hub : Hub connect left ::> actual to right ::> actual {{
                        interface f :> fastener connect a ::> left.pin1 to b ::> right.pin1;
                    }}
                    {}
                }}
            }}",
            if before { actual } else { "" },
            if before { "" } else { actual },
        );
        let mut resolved = checked(&source);
        let hub = resolved.resolve_qualified("P::assembly::hub").unwrap();
        let left = resolved
            .resolve_qualified("P::assembly::hub::left")
            .unwrap();
        assert_eq!(resolved.owner(left), Some(hub));
        assert_eq!(resolved.element_name(left), Some("left"));
        let source_alias = resolved.resolve_qualified("P::assembly::hub::source");
        assert_eq!(source_alias, Some(left));
        let pin1 = resolved.resolve_qualified("P::assembly::actual::pin1");
        assert_eq!(
            resolved.resolve_qualified("P::assembly::hub::left::pin1"),
            pin1,
        );
        assert!(pin1.is_some());
    }
}

#[test]
fn declared_end_bindings_cover_nary_connectors_and_override_fallback_names() {
    let mut resolved = checked(
        "package P {
            part p { attribute value; }
            connection binary connect left ::> p to source ::> p {
                attribute a = left.value;
                attribute b = source.value;
                attribute c = target.value;
            }
            connection ternary connect (one ::> p, two ::> p, three ::> p) {
                attribute a = one.value;
                attribute b = two.value;
                attribute c = three.value;
            }
            connection ordinary {
                end <l> left ::> p;
                end <r> right ::> p;
                attribute a = l.value;
                attribute b = right.value;
            }
        }",
    );
    let source = resolved.resolve_qualified("P::binary::source").unwrap();
    assert_eq!(resolved.element_name(source), Some("source"));
    assert_eq!(
        resolved.resolve_qualified("P::binary::target"),
        Some(source)
    );
    let one = resolved.resolve_qualified("P::ternary::one").unwrap();
    let ternary = resolved.resolve_qualified("P::ternary").unwrap();
    assert_eq!(resolved.owner(one), Some(ternary));
    assert_eq!(resolved.resolve_qualified("P::ternary::source"), None);
    assert_eq!(
        resolved.resolve_qualified("P::ordinary::l"),
        resolved.resolve_qualified("P::ordinary::left"),
    );
}

/// The two ends of a flow, succession or binding implicitly redefine the
/// library's binary ends by position, so the usage's body finds them by
/// those ends' names (`source`/`target`, `earlierOccurrence`/
/// `laterOccurrence`, `thisThing`/`sameThing`) and their qualified names
/// resolve back to them. A flow end holds its flow feature under the name
/// that feature redefines, and inherits the chain prefix it subsets.
#[test]
fn flow_succession_and_binding_ends_resolve_by_their_positional_names() {
    let mut r = checked(
        "package P {
            part def A { port p; attribute m; attribute w; }
            part def S {
                part a : A;
                part b : A;
                flow f from a.p to b.p;
                succession flow sf from a.p to b.p;
                message mg from a to b;
                action x;
                action y;
                succession s first x then y;
                binding bd bind a.m = b.m;
                flow g :> f { end :>> source ::> a.p; end :>> target ::> b.p; }
                ref fp :> f.source.p;
                ref fw :> f.target.w;
                ref sx :> s.earlierOccurrence;
                ref bs :> bd.sameThing;
            }
        }",
    );
    for name in [
        "P::S::f::source",
        "P::S::f::target",
        "P::S::f::source::p",
        "P::S::f::target::p",
        "P::S::sf::source",
        "P::S::sf::target",
        "P::S::mg::source",
        "P::S::mg::target::b",
        "P::S::s::earlierOccurrence",
        "P::S::s::laterOccurrence",
        "P::S::bd::thisThing",
        "P::S::bd::sameThing",
    ] {
        let e = r.resolve_semantic_qualified(name).expect(name);
        assert_eq!(r.element_qualified_name(e).as_deref(), Some(name));
    }
    // The chains reach the ends themselves, a flow end's own flow feature,
    // and, through the end's prefix, the prefix's other members.
    for name in [
        "P::S::f::source::p",
        "P::S::s::earlierOccurrence",
        "P::S::bd::sameThing",
        "P::A::w",
    ] {
        let e = r.resolve_qualified(name).unwrap();
        assert!(!r.references_to(e).is_empty(), "{name}");
    }
    let flow_feature = r.resolve_qualified("P::S::f::source::p").unwrap();
    assert_eq!(r.element_type(flow_feature), "ReferenceUsage");
    // A flow specializing `f` redefines `f`'s own ends by those names.
    for end in ["source", "target"] {
        let general = r.resolve_qualified(&format!("P::S::f::{end}")).unwrap();
        let local = r.resolve_qualified(&format!("P::S::g::{end}")).unwrap();
        assert_ne!(local, general);
        let redef = r
            .owned_relationships(local)
            .into_iter()
            .find(|&rel| r.element_type(rel) == "Redefinition")
            .unwrap();
        assert_eq!(
            r.relationship_ends(redef).1,
            vec![Reference::Element(general)],
            "{end}"
        );
    }
}

/// The same names find a KerML succession's and binding connector's ends.
#[test]
fn kerml_succession_and_binding_ends_resolve_by_their_positional_names() {
    let mut model = Model::new();
    model.add_source(
        "ends.kerml",
        "package K {
            behavior B {
                step x;
                step y;
                succession s first x then y;
                binding b of x = y;
            }
        }",
    );
    assert!(!model.has_errors(), "{:?}", model.units()[0].diagnostics);
    let mut r = ResolvedModel::build(&model);
    for name in [
        "K::B::s::earlierOccurrence",
        "K::B::s::laterOccurrence",
        "K::B::b::thisThing",
        "K::B::b::sameThing",
    ] {
        let e = r.resolve_semantic_qualified(name).expect(name);
        assert_eq!(r.element_type(e), "Feature", "{name}");
        assert_eq!(r.element_qualified_name(e).as_deref(), Some(name));
    }
}

#[test]
fn standard_library_nested_interfaces_resolve_numbered_actual_ports() {
    let corpus = sysmlv2_testkit::corpus_root();
    let path = corpus
        .join("sysml/src/examples/Vehicle Example/SysML v2 Spec Annex A SimpleVehicleModel.sysml");
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source(
        "nested-interfaces.sysml",
        &std::fs::read_to_string(path).unwrap(),
    );
    assert!(!model.has_errors());
    let mut resolved = ResolvedModel::build(&model);
    let missing = resolved.unresolved_references();
    for name in [
        "lugNutPort1",
        "lugNutPort2",
        "lugNutPort3",
        "shankPort1",
        "shankPort2",
        "shankPort3",
    ] {
        assert!(
            !missing.iter().any(|reference| reference.spelling == name),
            "{name}"
        );
    }
    let base = "SimpleVehicleModel::VehicleConfigurations::WheelHubAssemblies::wheelHubAssy3";
    let hub = resolved
        .resolve_qualified(&format!("{base}::wheelHubInterface"))
        .unwrap();
    for end in ["lugNutCompositePort", "shankCompositePort"] {
        let feature = resolved
            .resolve_qualified(&format!("{base}::wheelHubInterface::{end}"))
            .unwrap();
        assert_eq!(resolved.owner(feature), Some(hub), "{end}");
    }
}

/// An unnamed end of a typed connector-family usage, or of a definition
/// specializing one with ends, redefines its type's end at the same
/// position and takes that end's name, so the usage's body finds the end
/// by that name ahead of the type's end it redefines, and its qualified
/// name resolves back to it — binary or n-ary, connection, allocation,
/// interface, binding or succession. Chains through the end reach its
/// connected feature.
#[test]
fn typed_connector_ends_resolve_by_their_types_end_names() {
    let mut r = checked(
        "package P {
            part def A { port p; attribute m; }
            part def B { port q; attribute w; }
            part a : A;
            part b : B;
            allocation def L2P { end logical : A; end physical : B; }
            allocation a1 : L2P allocate a to b;
            connection def C3 { end e1; end e2; end e3; }
            connection bus : C3 connect (a, b, a.p, b.q);
            connection def Seat { end bead : A; end rim : B; }
            connection def Seat2 :> Seat { end : A; end : B; }
            connection s2 : Seat2 connect a to b;
            interface def I { end port pin; end port socket; }
            interface i1 : I connect a.p to b.q;
            connection def AB { end x; end y; }
            binding ab1 : AB bind a.m = b.w;
            succession s1 : AB first a then b;
            allocation a2 : L2P { end :>> logical ::> a; end :>> physical ::> b; }
            ref r1 :> a1.logical.m;
            ref r2 :> bus.e3;
            ref r3 :> s2.rim.w;
            ref r4 :> ab1.y;
        }",
    );
    for (usage, ends) in [
        ("P::a1", &["logical", "physical"][..]),
        ("P::bus", &["e1", "e2", "e3"]),
        ("P::Seat2", &["bead", "rim"]),
        ("P::s2", &["bead", "rim"]),
        ("P::i1", &["pin", "socket"]),
        ("P::ab1", &["x", "y"]),
        ("P::s1", &["x", "y"]),
        ("P::a2", &["logical", "physical"]),
    ] {
        let owner = r.resolve_qualified(usage).unwrap();
        for end in ends {
            let name = format!("{usage}::{end}");
            let e = r.resolve_semantic_qualified(&name).expect(&name);
            assert_eq!(r.owner(e), Some(owner), "{name}");
            assert_eq!(r.element_qualified_name(e), Some(name.clone()));
        }
    }
    // The binary positional names still find the same ends, and a fourth
    // end beyond the type's three has no name to be found by.
    assert_eq!(
        r.resolve_qualified("P::a1::source"),
        r.resolve_qualified("P::a1::logical")
    );
    assert_eq!(
        r.resolve_qualified("P::i1::target"),
        r.resolve_qualified("P::i1::socket")
    );
    let bus = r.resolve_qualified("P::bus").unwrap();
    let fourth = r
        .owned_members(bus)
        .into_iter()
        .filter(|&m| r.owning_membership_type(m) == Some("EndFeatureMembership"))
        .nth(3)
        .unwrap();
    assert_eq!(r.element_qualified_name(fourth), None);
    // The chains reach the usages' own ends, and through them the
    // connected features' members.
    for name in [
        "P::a1::logical",
        "P::bus::e3",
        "P::s2::rim",
        "P::ab1::y",
        "P::A::m",
        "P::B::w",
    ] {
        let e = r.resolve_qualified(name).unwrap();
        assert!(!r.references_to(e).is_empty(), "{name}");
    }
    // The types' own ends are untouched.
    let logical = r.resolve_qualified("P::L2P::logical").unwrap();
    assert_eq!(r.owner(logical), r.resolve_qualified("P::L2P"));
}

/// With the library loaded, the type's end names still find the usage's
/// own ends ahead of the library bases its kind implies, for a flow typed
/// by a flow definition as well; the binary positional names find the
/// same ends.
#[test]
fn typed_connector_ends_resolve_by_their_types_end_names_with_the_library() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source(
        "ends.sysml",
        "package P {
            part def A { port p; }
            allocation def L2P { end logical : A; end physical : A; }
            flow def FD { end src : A; end dst : A; }
            interface def I { end port pin; end port socket; }
            part s {
                part a : A;
                part b : A;
                allocation a1 : L2P allocate a to b;
                flow f : FD from a.p to b.p;
                interface i1 : I connect a.p to b.p;
            }
        }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    for (owner, ends) in [
        ("P::s::a1", ["logical", "physical"]),
        ("P::s::f", ["src", "dst"]),
        ("P::s::i1", ["pin", "socket"]),
    ] {
        for end in ends {
            let name = format!("{owner}::{end}");
            let e = r.resolve_semantic_qualified(&name).expect(&name);
            assert_eq!(r.owner(e), r.resolve_qualified(owner), "{name}");
            assert_eq!(r.element_qualified_name(e), Some(name.clone()));
        }
    }
    assert_eq!(
        r.resolve_qualified("P::s::a1::target"),
        r.resolve_qualified("P::s::a1::physical")
    );
}
