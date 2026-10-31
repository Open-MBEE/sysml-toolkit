//! KerML 8.2.3.5.2: the `references` target of an end feature owned by a
//! connector resolves in the connector's owning namespace, not in the
//! connector's body, where an end the connector inherits from its own type
//! would hide the owner's feature of that name.

#![cfg(feature = "json")]

use sysmlv2_parser::{json::ResolvedModel, model::Model};

#[test]
fn connector_end_references_resolve_in_the_connectors_owner() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source(
        "ends.kerml",
        "package EndReference {
            assoc T {
                end feature source { feature sourceOutput; }
                end feature target;
            }
            assoc Untyped specializes T {
                connector link {
                    end feature ts references source;
                    end feature tp subsets ts.sourceOutput;
                }
            }
            assoc Typed specializes T {
                connector link : Links::BinaryLink {
                    end feature ts references source;
                    end feature tp subsets ts.sourceOutput;
                }
            }
        }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let unresolved: Vec<_> = r
        .unresolved_references()
        .into_iter()
        .filter(|u| {
            let unit = model.unit(u.unit);
            !unit.is_library
                || (unit.name.ends_with("Transfers.kerml")
                    && matches!(u.spelling.as_str(), "sourceOutput" | "targetInput"))
        })
        .map(|u| (model.unit(u.unit).name.clone(), u.spelling))
        .collect();
    assert!(unresolved.is_empty(), "{unresolved:?}");
    let source = r.resolve_qualified("EndReference::T::source").unwrap();
    let output = r
        .resolve_qualified("EndReference::T::source::sourceOutput")
        .unwrap();
    for q in [
        "EndReference::Untyped::link::ts",
        "EndReference::Typed::link::ts",
    ] {
        let ts = r.resolve_qualified(q).unwrap();
        let rel = r
            .owned_relationships(ts)
            .into_iter()
            .find(|&rel| r.element_type(rel) == "ReferenceSubsetting")
            .unwrap();
        let referenced = r
            .element_properties(rel)
            .get("referencedFeature")
            .and_then(|v| v.get("@id"))
            .and_then(|v| v.as_str())
            .and_then(|id| r.element_by_id(id));
        assert_eq!(referenced, Some(source), "{q}");
        // A chain through the end reaches the members of the owner's end.
        assert_eq!(
            r.resolve_qualified(&format!("{q}::sourceOutput")),
            Some(output),
            "{q}"
        );
    }
}
