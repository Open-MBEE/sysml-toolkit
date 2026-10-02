#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ResolvedModel, model_resolution_report},
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
