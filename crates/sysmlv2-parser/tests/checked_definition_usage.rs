//! Inherited Usage subsets share the complete Type feature certificate.
use sysmlv2_parser::{
    json::{ClosurePolicy, ResolvedModel},
    model::{GraphFormat, Model},
};

#[test]
fn definition_usage_subsets_include_actual_library_and_inherited_members() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut model = Model::with_graph_format(format);
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        let parsed = model.add_source("usages.sysml", "package P { part def Base { part sensor; port bus; action act; } part def Child :> Base { part extra; } part def Broken :> Missing; }");
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut r = ResolvedModel::build(&model);
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let child = r.resolve_qualified("P::Child").unwrap();
        let usages = r.property(child, "usage").unwrap();
        for name in [
            "P::Base::sensor",
            "P::Base::bus",
            "P::Base::act",
            "P::Child::extra",
            "Parts::Part::ownedPorts",
            "Items::Item::checkedConstraints",
        ] {
            let member = r.resolve_qualified(name).unwrap();
            assert!(
                usages
                    .as_array()
                    .unwrap()
                    .iter()
                    .any(|v| v["@id"] == r.element_id(member).to_string()),
                "{format:?}: {name}"
            );
        }
        assert_eq!(
            r.property(child, "directedUsage").unwrap(),
            serde_json::json!([])
        );
        let broken = r.resolve_qualified("P::Broken").unwrap();
        assert!(r.property(broken, "usage").is_err());
    }
}

#[test]
fn simple_part_strict_export_retains_only_the_unproved_implied_completeness_flag() {
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut model = Model::with_graph_format(format);
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        assert!(
            model
                .add_source("simple.sysml", "part def Box;")
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        let report = r.to_full_json_strict().unwrap_err();
        assert_eq!(report.issues.len(), 1, "{format:?}: {report:?}");
        assert_eq!(report.issues[0].property, "isImpliedIncluded");
    }
}
