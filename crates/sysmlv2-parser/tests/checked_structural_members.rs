//! Ordinary structural members do not require execution of their own bodies.
use sysmlv2_parser::{
    json::{ClosurePolicy, ResolvedModel},
    model::{GraphFormat, Model},
};

#[test]
fn checked_part_features_include_ordinary_usage_members_and_library_members() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut model = Model::with_graph_format(format);
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        let unit = model.add_source(
            "members.sysml",
            "package P {
            part def Base {
                part sensor;
                port bus;
                action act;
                state status;
                constraint guard;
                connect sensor to sensor;
            }
            part def Child :> Base { part extra; }
            part def Broken :> Missing { port bus; }
        }",
        );
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let mut r = ResolvedModel::build(&model);
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let child = r.resolve_qualified("P::Child").unwrap();
        for property in ["feature", "inheritedFeature"] {
            let values = r.property(child, property).unwrap();
            for member in [
                "P::Base::sensor",
                "P::Base::bus",
                "P::Base::act",
                "P::Base::status",
                "P::Base::guard",
                "Parts::Part::ownedPorts",
                "Items::Item::checkedConstraints",
            ] {
                let element = r.resolve_qualified(member).unwrap();
                let id = r.element_id(element).to_string();
                assert!(
                    values.as_array().unwrap().iter().any(|v| v["@id"] == id),
                    "{format:?} {property} lacks {member}"
                );
            }
        }
        let broken = r.resolve_qualified("P::Broken").unwrap();
        assert!(r.property(broken, "feature").is_err());
    }
}
