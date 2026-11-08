use super::{TreeNode, TreeOptions, render, tree};
use crate::json::ResolvedModel;
use crate::model::Model;
use std::collections::HashSet;
use std::path::Path;

fn resolved(text: &str) -> ResolvedModel {
    let mut model = Model::new();
    let unit = model.add_source("t.sysml", text);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

const VEHICLE: &str = "package Demo {
    attribute def Mass;
    part def Vehicle {
        attribute mass : Mass;
    }
    part v : Vehicle;
    alias m for Vehicle::mass;
}
";

#[test]
fn ownership_alternates_element_and_relationship() {
    let mut r = resolved(VEHICLE);
    let root = r.resolve_qualified("Demo::Vehicle").unwrap();
    let nodes = tree(&mut r, Some(root), &TreeOptions::default());
    assert_eq!(nodes.len(), 1);
    let vehicle = &nodes[0];
    assert_eq!(vehicle.metaclass, "PartDefinition");
    assert_eq!(vehicle.qualified_name.as_deref(), Some("Demo::Vehicle"));
    assert!(!vehicle.library && !vehicle.truncated);
    assert_eq!(
        vehicle.site.as_ref().map(|s| (s.file.as_str(), s.line)),
        Some(("t.sysml", 3))
    );
    let [membership] = vehicle.relationships.as_slice() else {
        panic!("{:?}", vehicle.relationships);
    };
    assert_eq!(membership.metaclass, "FeatureMembership");
    assert!(!membership.implied);
    assert!(
        membership.references.is_empty(),
        "{:?}",
        membership.references
    );
    let [mass] = membership.children.as_slice() else {
        panic!("{:?}", membership.children);
    };
    assert_eq!(mass.metaclass, "AttributeUsage");
    assert_eq!(mass.name.as_deref(), Some("mass"));
    assert_eq!(mass.qualified_name.as_deref(), Some("Demo::Vehicle::mass"));
    // The typing, then the default multiplicity's membership (SysML
    // 7.6.3), an attribute its type features owns as its last member.
    let [typing, default] = mass.relationships.as_slice() else {
        panic!("{:?}", mass.relationships);
    };
    assert_eq!(typing.metaclass, "FeatureTyping");
    assert!(typing.children.is_empty());
    assert_eq!(default.metaclass, "OwningMembership");
    assert_eq!(default.children[0].metaclass, "Multiplicity");
    assert!(default.children[0].name.is_none());
    let [reference] = typing.references.as_slice() else {
        panic!("{:?}", typing.references);
    };
    assert_eq!(reference.property, "type");
    assert_eq!(
        reference.target.qualified_name.as_deref(),
        Some("Demo::Mass")
    );
    assert_eq!(reference.target.metaclass, Some("AttributeDefinition"));
    assert!(!reference.target.library && !reference.target.outside);
    assert!(reference.target.id.is_none() && reference.target.spelling.is_none());
}

#[test]
fn whole_model_starts_at_top_level_members() {
    let mut r = resolved(VEHICLE);
    let nodes = tree(&mut r, None, &TreeOptions::default());
    let roots: Vec<_> = nodes.iter().map(|n| n.qualified_name.as_deref()).collect();
    assert_eq!(roots, [Some("Demo")]);
    let kinds: Vec<&str> = nodes[0].relationships.iter().map(|r| r.metaclass).collect();
    assert_eq!(
        kinds,
        [
            "OwningMembership",
            "OwningMembership",
            "OwningMembership",
            "Membership"
        ]
    );
}

#[test]
fn alias_membership_points_at_its_member() {
    let mut r = resolved(VEHICLE);
    let nodes = tree(&mut r, None, &TreeOptions::default());
    let alias = nodes[0].relationships.last().unwrap();
    assert_eq!(alias.metaclass, "Membership");
    assert!(alias.children.is_empty());
    let [reference] = alias.references.as_slice() else {
        panic!("{:?}", alias.references);
    };
    assert_eq!(reference.property, "memberElement");
    assert_eq!(
        reference.target.qualified_name.as_deref(),
        Some("Demo::Vehicle::mass")
    );
    assert_eq!(reference.target.metaclass, Some("AttributeUsage"));
}

#[test]
fn depth_limits_and_marks_truncation() {
    let mut r = resolved(VEHICLE);
    let root = r.resolve_qualified("Demo::Vehicle").unwrap();
    let options = TreeOptions {
        depth: Some(0),
        ..Default::default()
    };
    let nodes = tree(&mut r, Some(root), &options);
    assert!(nodes[0].truncated && nodes[0].relationships.is_empty());
    let options = TreeOptions {
        depth: Some(1),
        ..Default::default()
    };
    let nodes = tree(&mut r, Some(root), &options);
    assert!(!nodes[0].truncated);
    let mass = &nodes[0].relationships[0].children[0];
    assert!(mass.truncated && mass.relationships.is_empty());
    let options = TreeOptions {
        depth: Some(2),
        ..Default::default()
    };
    let nodes = tree(&mut r, Some(root), &options);
    let mass = &nodes[0].relationships[0].children[0];
    assert!(!mass.truncated && mass.relationships.len() == 2);
}

#[test]
fn unresolved_reference_keeps_its_spelling() {
    let mut r = resolved("package P { part def V { attribute m : ScalarValues::Real; } }");
    let root = r.resolve_qualified("P::V::m").unwrap();
    let nodes = tree(&mut r, Some(root), &TreeOptions::default());
    let typing = &nodes[0].relationships[0];
    let [reference] = typing.references.as_slice() else {
        panic!("{:?}", typing.references);
    };
    assert_eq!(reference.property, "type");
    assert_eq!(
        reference.target.spelling.as_deref(),
        Some("ScalarValues::Real")
    );
    assert!(reference.target.metaclass.is_none() && !reference.target.outside);
    assert!(render(&nodes).contains("type → ScalarValues::Real (unresolved)\n"));
}

#[test]
fn references_can_be_left_out() {
    let mut r = resolved(VEHICLE);
    let root = r.resolve_qualified("Demo::Vehicle::mass").unwrap();
    let options = TreeOptions {
        references: false,
        ..Default::default()
    };
    let nodes = tree(&mut r, Some(root), &options);
    let typing = &nodes[0].relationships[0];
    assert_eq!(typing.metaclass, "FeatureTyping");
    assert!(typing.references.is_empty());
}

#[test]
fn ids_are_carried_on_request() {
    let mut r = resolved(VEHICLE);
    let root = r.resolve_qualified("Demo::Vehicle").unwrap();
    let options = TreeOptions {
        ids: true,
        ..Default::default()
    };
    let nodes = tree(&mut r, Some(root), &options);
    assert_eq!(
        nodes[0].id.as_deref(),
        Some(r.element_id(root).to_string().as_str())
    );
    let membership = &nodes[0].relationships[0];
    assert!(membership.id.is_some());
    let typing = &membership.children[0].relationships[0];
    let mass_def = r.resolve_qualified("Demo::Mass").unwrap();
    assert_eq!(
        typing.references[0].target.id.as_deref(),
        Some(r.element_id(mass_def).to_string().as_str())
    );
    let text = render(&nodes);
    assert!(text.contains(&format!(
        "Demo::Vehicle [PartDefinition] {}\n",
        r.element_id(root)
    )));
}

#[test]
fn render_draws_branches() {
    let mut r = resolved(VEHICLE);
    let root = r.resolve_qualified("Demo::Vehicle").unwrap();
    let nodes = tree(&mut r, Some(root), &TreeOptions::default());
    assert_eq!(
        render(&nodes),
        "Demo::Vehicle [PartDefinition]
└─ FeatureMembership
   └─ mass [AttributeUsage]
      ├─ FeatureTyping
      │  └─ type → Demo::Mass [AttributeDefinition]
      └─ OwningMembership
         └─ (anonymous) [Multiplicity]
"
    );
    let nodes = tree(&mut r, None, &TreeOptions::default());
    assert_eq!(
        render(&nodes),
        "Demo [Package]
├─ OwningMembership
│  └─ Mass [AttributeDefinition]
├─ OwningMembership
│  └─ Vehicle [PartDefinition]
│     └─ FeatureMembership
│        └─ mass [AttributeUsage]
│           ├─ FeatureTyping
│           │  └─ type → Demo::Mass [AttributeDefinition]
│           └─ OwningMembership
│              └─ (anonymous) [Multiplicity]
├─ OwningMembership
│  └─ v [PartUsage]
│     └─ FeatureTyping
│        └─ type → Demo::Vehicle [PartDefinition]
└─ Membership
   └─ memberElement → Demo::Vehicle::mass [AttributeUsage]
"
    );
    let options = TreeOptions {
        depth: Some(1),
        ..Default::default()
    };
    let nodes = tree(&mut r, Some(root), &options);
    assert_eq!(
        render(&nodes),
        "Demo::Vehicle [PartDefinition]
└─ FeatureMembership
   └─ mass [AttributeUsage] …
"
    );
}

#[test]
fn json_names_are_camel_case_and_sparse() {
    let mut r = resolved(VEHICLE);
    let root = r.resolve_qualified("Demo::Vehicle").unwrap();
    let nodes = tree(&mut r, Some(root), &TreeOptions::default());
    let json = serde_json::to_value(&nodes).unwrap();
    let vehicle = &json[0];
    assert_eq!(vehicle["metaclass"], "PartDefinition");
    assert_eq!(vehicle["qualifiedName"], "Demo::Vehicle");
    assert_eq!(vehicle["site"]["file"], "t.sysml");
    for absent in ["id", "library", "truncated", "references"] {
        assert!(vehicle.get(absent).is_none(), "{absent}: {vehicle}");
    }
    let membership = &vehicle["relationships"][0];
    assert_eq!(membership["metaclass"], "FeatureMembership");
    assert!(membership.get("implied").is_none() && membership.get("references").is_none());
    let typing = &membership["children"][0]["relationships"][0];
    assert_eq!(typing["references"][0]["property"], "type");
    assert_eq!(
        typing["references"][0]["target"]["qualifiedName"],
        "Demo::Mass"
    );
    assert_eq!(typing["children"], serde_json::json!([]));
}

#[test]
fn value_expressions_hang_under_their_feature_value() {
    let mut r = resolved(
        "package P { part def V { attribute mass : Mass; attribute heavy = mass > 1000; } attribute def Mass; }",
    );
    let root = r.resolve_qualified("P::V::heavy").unwrap();
    let nodes = tree(&mut r, Some(root), &TreeOptions::default());
    let text = render(&nodes);
    // The value first, the default multiplicity's membership last.
    assert!(text.starts_with("P::V::heavy [AttributeUsage]\n├─ FeatureValue\n│  └─ (anonymous) [OperatorExpression]\n"), "{text}");
    assert!(
        text.ends_with("└─ OwningMembership\n   └─ (anonymous) [Multiplicity]\n"),
        "{text}"
    );
    // The operand that names `mass` resolves to the attribute: the
    // reference the expression's membership carries.
    assert!(
        text.contains("memberElement → P::V::mass [AttributeUsage]\n"),
        "{text}"
    );
    assert!(text.contains("[LiteralInteger]\n"), "{text}");
}

/// The standard library beside the checkout, when the corpus is present.
fn with_standard_library(text: &str) -> Option<ResolvedModel> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../spec-refs/SysML-v2-Release/sysml.library");
    if !path.exists() {
        eprintln!("skipping: corpus not present");
        return None;
    }
    let mut model = Model::new();
    model.load_library_dir(&path).unwrap();
    let unit = model.add_source("t.sysml", text);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    Some(ResolvedModel::build(&model))
}

/// Every relationship row is owned once, so it appears once.
fn assert_relationships_listed_once(node: &TreeNode, seen: &mut HashSet<String>) {
    for relationship in &node.relationships {
        let id = relationship.id.clone().expect("ids requested");
        assert!(
            seen.insert(id.clone()),
            "{} {id} listed twice under {:?}",
            relationship.metaclass,
            node.qualified_name
        );
        for child in &relationship.children {
            assert_relationships_listed_once(child, seen);
        }
    }
}

#[test]
fn implied_relationships_and_generated_elements_each_appear_once() {
    let Some(mut r) = with_standard_library(
        "package Demo { part def Vehicle { attribute mass : ScalarValues::Real; attribute heavy : ScalarValues::Boolean = mass > 1000; } }",
    ) else {
        return;
    };
    let root = r.resolve_qualified("Demo::Vehicle").unwrap();
    let options = TreeOptions {
        implied: true,
        ids: true,
        ..Default::default()
    };
    let nodes = tree(&mut r, Some(root), &options);
    assert_relationships_listed_once(&nodes[0], &mut HashSet::new());
    let text = render(&nodes);
    assert_eq!(
        text.matches("Subclassification (implied)").count(),
        1,
        "{text}"
    );
    assert!(
        text.contains("superclassifier → Parts::Part [PartDefinition] [library]"),
        "{text}"
    );
    // The generated result parameter of the operand expression and the
    // binding connector it hangs under are listed (once each, above).
    assert!(
        text.contains("ReturnParameterMembership (implied)"),
        "{text}"
    );
    assert!(text.contains("[BindingConnector]"), "{text}");
    // Without the flag nothing implied shows, and the explicit tree is
    // what the text declares.
    let plain = tree(&mut r, Some(root), &TreeOptions::default());
    let text = render(&plain);
    assert!(
        !text.contains("(implied)") && !text.contains("[BindingConnector]"),
        "{text}"
    );
}
