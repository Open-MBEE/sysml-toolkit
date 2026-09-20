//! Behaviour gates for the emitters' subtree walks and node
//! bookkeeping: the interconnection content gate (which packages and
//! definitions render, in text and graph form) and the case view's node
//! set (a case referenced before its declaration draws exactly once).

use sysmlv2_model::json::ResolvedModel;
use sysmlv2_model::model::Model;
use sysmlv2_viz::{View, VizOptions, graph, plantuml};

fn resolved(src: &str) -> ResolvedModel {
    let mut model = Model::new();
    let unit = model.add_source("walks.sysml".to_string(), src);
    assert!(
        unit.diagnostics.is_empty(),
        "fixture must parse: {:?}",
        unit.diagnostics
    );
    ResolvedModel::build(&model)
}

/// Content sits three containers deep (`Inner`'s port), beside empty
/// siblings at every level.
const NESTED: &str = "package Outer {
    package Empty { part def NoContent; attribute def Plain; }
    package Deep {
        part def Shell { part def Inner { port p; } }
        part def Bare;
    }
    part def Top { part sub; }
}
";

#[test]
fn interconnection_gate_renders_only_containers_with_content() {
    let mut r = resolved(NESTED);
    let opts = VizOptions::default().with_view(View::Interconnection);
    let out = plantuml(&mut r, None, &opts);
    let expected = "@startuml
package \"Outer\" as n1 {
  package \"Deep\" as n2 {
    rectangle \"Shell\" as n3 <<part def>> {
      rectangle \"Inner\" as n4 <<part def>> {
        port \"p\" as n5
      }
    }
  }
  rectangle \"Top\" as n6 <<part def>> {
    rectangle \"sub\" as n7 <<part>>
  }
}
@enduml
";
    assert_eq!(out, expected);

    let g = graph(&mut r, None, &opts).unwrap();
    let labels: Vec<&str> = g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .map(|n| n["label"].as_str().unwrap())
        .collect();
    assert_eq!(
        labels,
        ["Outer", "Deep", "Shell", "Inner", "p", "Top", "sub"]
    );
}

/// An `include` reaching a case declared later in the package draws
/// that case once: the reference draws it lazily, and the containment
/// walk that reaches it afterwards keeps the declaration it has.
#[test]
fn case_view_draws_an_included_case_once() {
    let mut r = resolved(
        "package Ops {
    use case def Drive { include unlock; }
    use case unlock : UnlockVehicle;
    use case def UnlockVehicle;
}
",
    );
    let out = plantuml(&mut r, None, &VizOptions::default().with_view(View::Case));
    let expected = "@startuml
usecase \"Drive\" as n1 <<use case def>>
usecase \"unlock : UnlockVehicle\" as n2 <<use case>>
usecase \"UnlockVehicle\" as n3 <<use case def>>
n1 ..> n2 : «include»
@enduml
";
    assert_eq!(out, expected);
}
