//! PlantUML emission gates: golden outputs per view (structure /
//! interconnection / state / action), library-typed labels, element
//! scoping, KerML units, determinism, and a corpus sweep (every
//! non-library corpus file emits a balanced diagram for every view
//! without panicking, with a floor on how many are non-empty).

use std::collections::HashMap;
use std::path::PathBuf;

use sysmlv2_model::eval::UnitDisplay;
use sysmlv2_model::json::{ElementRef, ResolvedModel};
use sysmlv2_model::model::Model;
use sysmlv2_viz::{Direction, LineStyle, View, VizOptions, plantuml};

const DEMO: &str = "package Vehicles {
    part def Vehicle {
        attribute mass : Real = 1200;
        part wheels : Wheel[4];
    }
    part def Wheel;
    part def SportsCar :> Vehicle;
    part myCar : SportsCar;
    enum def Phase { halt; mid; init; }
}
";

fn resolved(src: &str) -> ResolvedModel {
    resolved_named("demo.sysml", src)
}

fn resolved_named(name: &str, src: &str) -> ResolvedModel {
    let mut model = Model::new();
    let unit = model.add_source(name.to_string(), src);
    assert!(unit.diagnostics.is_empty(), "fixture must parse: {name}");
    ResolvedModel::build(&model)
}

#[test]
fn graph_redefined_nodes_and_rows_have_resolvable_qualified_names() {
    let mut r = resolved(
        "package P {
        part def Tank { attribute mass = 1; }
        part base { part tank : Tank; }
        part actual :> base { part :>> tank { attribute :>> mass = 2; } }
    }",
    );
    let graph = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    for name in ["P::actual::tank", "P::actual::tank::mass"] {
        let element = r.resolve_qualified(name).expect(name);
        let id = r.element_id(element).to_string();
        let item = graph["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .flat_map(|n| std::iter::once(n).chain(n["rows"].as_array().unwrap().iter()))
            .find(|n| n["id"] == id)
            .expect(name);
        assert_eq!(item["qname"], name);
        assert_eq!(item["file"], "demo.sysml");
        assert!(item["line"].as_u64().unwrap() > 0);
    }
}

#[test]
fn graph_says_which_qualified_names_end_in_an_implied_name() {
    let mut r = resolved(
        "package P {
        part def V;
        action refuel;
        verification def Test {
            subject : V;
            objective { verify requirement r; }
        }
        verification def Named { subject v : V; objective goal; }
        state def Engine { do refuel; exit action cool; }
        part def Tank { attribute mass = 1; }
        part def Big :> Tank { attribute :>> mass = 2; }
    }",
    );
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let rows = all_rows(&g);
    let row = |qname: &str| {
        *rows
            .iter()
            .find(|row| row["qname"] == qname)
            .unwrap_or_else(|| panic!("no row {qname}: {rows:#?}"))
    };
    // A name the element is given: a subject's or an objective's by its
    // role, a `do` action's by the action it performs (ahead of the
    // `doAction` it redefines), a redefinition's by what it redefines.
    for qname in [
        "P::Test::subj",
        "P::Test::obj",
        "P::Engine::refuel",
        "P::Big::mass",
    ] {
        assert_eq!(row(qname)["impliedName"], true, "{qname}");
    }
    // A declared name is no implied one, under an implied one too.
    for qname in [
        "P::Test::obj::r",
        "P::Named::v",
        "P::Named::goal",
        "P::Engine::cool",
        "P::Tank::mass",
    ] {
        assert!(row(qname).get("impliedName").is_none(), "{qname}");
    }
    // The cards declare their names.
    for n in g["nodes"].as_array().unwrap() {
        assert!(n.get("impliedName").is_none(), "{n}");
    }
}

#[test]
fn demo_golden() {
    let mut r = resolved(DEMO);
    let out = plantuml(&mut r, None, &VizOptions::default());
    let expected = "@startuml
hide empty members
package \"Vehicles\" as n1 {
  class \"Vehicle\" as n2 <<part def>> {
    mass = 1200
  }
  class \"wheels : Wheel [4]\" as n3 <<part>>
  class \"Wheel\" as n4 <<part def>>
  class \"SportsCar\" as n5 <<part def>>
  class \"myCar : SportsCar\" as n6 <<part>>
  enum \"Phase\" as n7 <<enum def>> {
    halt
    mid
    init
  }
}
n2 *-- n3
n3 ..> n4
n5 --|> n2
n6 ..> n5
@enduml
";
    assert_eq!(out, expected);
}

#[test]
fn demo_is_deterministic() {
    let mut r1 = resolved(DEMO);
    let a = plantuml(&mut r1, None, &VizOptions::default());
    let mut r2 = resolved(DEMO);
    let b = plantuml(&mut r2, None, &VizOptions::default());
    assert_eq!(a, b);
}

#[test]
fn direction_toggle() {
    let mut r = resolved(DEMO);
    let opts = VizOptions::default().with_direction(Direction::LeftToRight);
    let out = plantuml(&mut r, None, &opts);
    assert!(out.contains("left to right direction"));
}

#[test]
fn values_toggle_off() {
    let mut r = resolved(DEMO);
    let opts = VizOptions::default().with_show_values(false);
    let out = plantuml(&mut r, None, &opts);
    assert!(!out.contains("= 1200"), "{out}");
}

#[test]
fn value_units_choose_how_a_quantity_reads() {
    // A product folds into SI units; `AsWritten` shows it in the units
    // it was written in, and a bracket's own unit reads the same either
    // way.
    let mut r = resolved(
        "package P {
    attribute m; attribute s;
    attribute 'in' {
        attribute unitConversion { attribute referenceUnit = m; attribute conversionFactor = 0.0254; }
    }
    part def Board {
        attribute w = 10 ['in'];
        attribute area = w * (4 ['in']);
        attribute speed = w / (2 [s]);
    }
}
",
    );
    let si = plantuml(&mut r, None, &VizOptions::default());
    assert!(si.contains("area = 0.0258064 [m**2]"), "{si}");
    assert!(si.contains("speed = 0.127 [m/s]"), "{si}");
    let opts = VizOptions::default().with_value_units(UnitDisplay::AsWritten);
    let written = plantuml(&mut r, None, &opts);
    assert!(written.contains("w = 10 [in]"), "{written}");
    assert!(written.contains("area = 40 [in**2]"), "{written}");
    assert!(written.contains("speed = 5 [in/s]"), "{written}");
    let graph = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let text = serde_json::to_string(&graph).unwrap();
    assert!(text.contains("area = 40 [in**2]"), "{text}");
    assert!(text.contains("speed = 5 [in/s]"), "{text}");
}

#[test]
fn enum_defaults_render_by_literal_name() {
    let mut r = resolved(
        "package P {
    enum def Mode { fast; slow; }
    part def Box {
        attribute m : Mode = Mode::fast;
        attribute unbound : Mode;
    }
}
",
    );
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert!(out.contains("m : Mode = fast"), "{out}");
    assert!(
        out.contains("unbound : Mode\n"),
        "unvalued stays bare: {out}"
    );
    let graph = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let text = serde_json::to_string(&graph).unwrap();
    assert!(text.contains("m : Mode = fast"), "{text}");
}

#[test]
fn enum_metadata_members_are_not_literal_rows() {
    // A metadata usage in an enum body annotates the enumeration; only
    // the enumerated values are drawn as its literals.
    let mut r = resolved(
        "package P {
    metadata def M;
    enum def E { metadata m : M; enum a; b; }
}
",
    );
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert!(out.contains("<<enum def>> {\n    a\n    b\n  }"), "{out}");
}

#[test]
fn top_level_valued_usages_keep_values_as_nodes() {
    // An attribute with no enclosing node renders as its own node —
    // the `= value` suffix its compartment-row form carries must
    // survive the promotion.
    let mut r = resolved("package P {\n    attribute budget = 42;\n    part def K;\n}\n");
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert!(out.contains("budget = 42"), "{out}");
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    assert!(serde_json::to_string(&g).unwrap().contains("budget = 42"));
    let opts = VizOptions::default().with_show_values(false);
    let out = plantuml(&mut r, None, &opts);
    assert!(!out.contains("= 42"), "{out}");
}

#[test]
fn anonymous_redefining_members_label_by_target_name() {
    // `:>> x = v` members carry no declared name of their own; the
    // compartment line borrows the redefined feature's name instead of
    // rendering a bare `= v`.
    let mut r = resolved(
        "package P {
    enum def Mode { idle; run; }
    part def Machine {
        attribute mode : Mode;
        attribute rate = 10;
    }
    part def Rig {
        part m1 : Machine {
            attribute redefines mode = Mode::run;
            attribute redefines rate = 25;
        }
    }
}
",
    );
    let out = plantuml(&mut r, None, &VizOptions::default());
    // The borrowed name carries the type derived through the
    // redefinition (`mode : Mode`); `rate`'s target declares none.
    assert!(out.contains("mode : Mode = run"), "{out}");
    assert!(out.contains("rate = 25"), "{out}");
    assert!(!out.contains("\n    = "), "nameless line survived: {out}");
    let graph = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let text = serde_json::to_string(&graph).unwrap();
    assert!(text.contains("mode : Mode = run"), "{text}");

    // The borrowed name also shadows: with inherited lines on, the
    // target's own `mode : Mode` must not reappear beside it.
    let opts = VizOptions::default().with_show_inherited(true);
    let out = plantuml(&mut r, None, &opts);
    assert!(!out.contains("^mode"), "shadowing lost: {out}");
    assert!(out.contains("mode : Mode = run"), "{out}");
}

#[test]
fn anonymous_chain_redefinitions_label_by_chain() {
    // `:>> chassis.mass = 2` redefines a feature chain: the line borrows the
    // chain's spelling, and its type is found through the chain's last link,
    // that link's redefinition and the redefined feature's subsetting.
    let mut r = resolved(
        "package P {
    attribute def MassValue;
    attribute massRef : MassValue;
    part def Base {
        attribute mass :> massRef;
    }
    part def Chassis :> Base {
        attribute wheelbase : MassValue;
    }
    part def Crawler {
        part chassis : Chassis {
            attribute :>> mass = 1;
        }
    }
    part def Context {
        part med : Crawler {
            attribute :>> chassis.mass = 2;
        }
        part tiny : Crawler {
            part :>> chassis {
                attribute :>> mass = 3;
            }
        }
    }
}
",
    );
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert!(out.contains("chassis.mass : MassValue = 2"), "{out}");
    assert!(out.contains("mass : MassValue = 3"), "{out}");
    assert!(!out.contains("\n    = "), "nameless line survived: {out}");
    // A named feature keeps its label: `mass :> massRef` declares no type and
    // its subsetting is not followed for it.
    assert!(out.contains("    mass\n"), "{out}");

    let graph = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let rows: Vec<serde_json::Value> = graph["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .flat_map(|n| n["rows"].as_array().cloned().unwrap_or_default())
        .collect();
    let row = |label: &str| {
        rows.iter()
            .find(|r| r["label"] == label)
            .unwrap_or_else(|| panic!("no row {label}: {rows:#?}"))
            .clone()
    };
    let chain = row("chassis.mass : MassValue = 2");
    assert_eq!(chain["redefining"], true);
    assert_eq!(chain["chain"], serde_json::json!(["chassis", "mass"]));
    assert_eq!(chain["typeDerived"], true);
    let nested = row("mass : MassValue = 3");
    assert_eq!(nested["redefining"], true);
    assert!(nested.get("chain").is_none(), "{nested}");
    assert_eq!(nested["typeDerived"], true);
    // a written type is no derived one, and a named row is no redefining one
    let wheelbase = row("wheelbase : MassValue");
    assert!(
        wheelbase.get("typeDerived").is_none() && wheelbase.get("redefining").is_none(),
        "{wheelbase}"
    );
    // the nested block's card borrows its name the same way; a named card does not
    let nodes = graph["nodes"].as_array().unwrap();
    let block = nodes
        .iter()
        .find(|n| n["qname"] == "P::Context::tiny::chassis")
        .unwrap_or_else(|| panic!("no chassis block: {nodes:#?}"));
    assert_eq!(block["redefining"], true);
    assert!(block.get("chain").is_none(), "{block}");
    assert_eq!(block["typeDerived"], true, "{block}");
    let named = nodes
        .iter()
        .find(|n| n["qname"] == "P::Crawler::chassis")
        .unwrap();
    assert!(named.get("redefining").is_none(), "{named}");
    assert!(named.get("typeDerived").is_none(), "{named}");
}

#[test]
fn a_named_chain_block_shows_the_chain_s_last_type() {
    // `part cb :>> chassis.body` declares a name and no type: its type is
    // the chain's last link's, derived.
    let mut r = resolved(
        "package P {
    part def Body;
    part def Chassis { part body : Body; }
    part def Crawler { part chassis : Chassis; }
    part med : Crawler {
        part cb :>> chassis.body;
    }
}
",
    );
    let graph = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let cb = graph["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["qname"] == "P::med::cb")
        .unwrap_or_else(|| panic!("no cb: {graph:#?}"));
    assert_eq!(cb["label"], "cb : Body", "{cb}");
    assert_eq!(cb["typeDerived"], true, "{cb}");
}

#[test]
fn a_chain_cut_short_or_beside_a_named_target_is_no_chain_label() {
    // An unresolved last link leaves no chain to name (not its resolved
    // prefix), and a named target written beside a chain names the line,
    // as its effective name does.
    let mut r = resolved(
        "package P {
    part def Chassis { attribute mass; attribute body; }
    part def Crawler { part chassis : Chassis; attribute total; }
    part med : Crawler {
        attribute :>> chassis.mas = 1;
        attribute :>> total, chassis.mass = 2;
    }
}
",
    );
    let graph = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let rows: Vec<serde_json::Value> = graph["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|n| n["qname"] == "P::med")
        .flat_map(|n| n["rows"].as_array().cloned().unwrap_or_default())
        .collect();
    assert!(
        !rows.iter().any(|r| r["label"]
            .as_str()
            .is_some_and(|l| l.starts_with("chassis "))),
        "a cut-short chain must not read as its prefix: {rows:#?}"
    );
    assert!(rows.iter().all(|r| r.get("chain").is_none()), "{rows:#?}");
    let total = rows
        .iter()
        .find(|r| r["label"].as_str().is_some_and(|l| l.starts_with("total")))
        .unwrap_or_else(|| panic!("no total row: {rows:#?}"));
    assert_eq!(total["redefining"], true);
}

#[test]
fn graph_emits_note_nodes_for_doc_bodies() {
    let src = "package P {
    part def Box {
        doc /* Holds things. */
    }
}
";
    let mut r = resolved(src);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let note = nodes
        .iter()
        .find(|n| n["kind"] == "note")
        .expect("a note node");
    assert_eq!(note["label"], "Holds things.");
    assert_eq!(note["metaclass"], "Documentation");
    let box_id = nodes
        .iter()
        .find(|n| n["label"] == "Box")
        .and_then(|n| n["id"].as_str())
        .expect("the Box node");
    let edge = g["edges"]
        .as_array()
        .unwrap()
        .iter()
        .find(|e| e["kind"] == "note")
        .expect("a note edge");
    assert_eq!(edge["source"], note["id"]);
    assert_eq!(edge["target"].as_str().unwrap(), box_id);

    // The toggle drops both the node and its edge.
    let mut r = resolved(src);
    let opts = VizOptions::default().with_show_notes(false);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    assert!(
        !g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|n| n["kind"] == "note")
    );
    assert!(
        !g["edges"]
            .as_array()
            .unwrap()
            .iter()
            .any(|e| e["kind"] == "note")
    );
}

#[test]
fn element_scoped_root() {
    let mut r = resolved(DEMO);
    let root = r.resolve_qualified("Vehicles::Vehicle").expect("resolves");
    let out = plantuml(&mut r, Some(root), &VizOptions::default());
    assert!(out.contains("\"Vehicle\""), "{out}");
    assert!(out.contains("wheels"), "{out}");
    assert!(!out.contains("SportsCar"), "root scoping leaked: {out}");
    assert!(!out.contains("package \"Vehicles\""), "{out}");
}

#[test]
fn roots_filter_restricts_top_level() {
    // The package selector behind the diagram panel: with several
    // top-level packages, `opts.roots` renders exactly the chosen ones
    // (and their subtrees), not the whole model — the fix for a model
    // whose full tree is too large to lay out.
    let mut r = resolved(
        "package Alpha { part def A; }
package Beta { part def B; }
package Gamma { part def C; }
",
    );
    // Baseline: no filter draws every package.
    let all = plantuml(&mut r, None, &VizOptions::default());
    assert!(all.contains("\"Alpha\"") && all.contains("\"Beta\"") && all.contains("\"Gamma\""));

    let alpha = r.resolve_qualified("Alpha").expect("resolves");
    let gamma = r.resolve_qualified("Gamma").expect("resolves");
    let opts = VizOptions::default().with_roots(Some(vec![alpha, gamma]));
    let out = plantuml(&mut r, None, &opts);
    assert!(out.contains("\"Alpha\""), "{out}");
    assert!(out.contains("\"Gamma\""), "{out}");
    assert!(
        !out.contains("\"Beta\""),
        "unselected package leaked: {out}"
    );

    // The graph emitter honors it too (the native renderer's path).
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let names: Vec<&str> = g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|n| n["label"].as_str())
        .collect();
    assert!(
        names.contains(&"Alpha") && names.contains(&"Gamma"),
        "{names:?}"
    );
    assert!(
        !names.contains(&"Beta"),
        "unselected package in graph: {names:?}"
    );

    // A single explicit `root` still wins over the roots filter.
    let beta = r.resolve_qualified("Beta").expect("resolves");
    let scoped = plantuml(&mut r, Some(beta), &opts);
    assert!(
        scoped.contains("\"Beta\"") && !scoped.contains("\"Alpha\""),
        "{scoped}"
    );

    // Empty selection is treated as "no filter" (whole model), never
    // an empty diagram — the panel gates the truly-empty case itself.
    let empty_opts = VizOptions::default().with_roots(Some(vec![]));
    let out = plantuml(&mut r, None, &empty_opts);
    assert!(
        out.contains("\"Beta\""),
        "empty roots should not filter: {out}"
    );
}

#[test]
fn library_types_label_attributes() {
    let lib = sysmlv2_testkit::library_dir();
    let mut model = Model::new();
    model.load_library_dir(&lib).expect("library loads");
    model.add_source(
        "typed.sysml".to_string(),
        "package Typed {\n  part def Sensor {\n    attribute reading : ScalarValues::Real;\n  }\n}\n",
    );
    let mut r = ResolvedModel::build(&model);
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert!(out.contains("reading : Real"), "{out}");
    // library elements never render as nodes
    assert!(!out.contains("\"Real\" as"), "{out}");
}

#[test]
fn kerml_unit_renders_classifiers() {
    let mut r = resolved_named(
        "k.kerml",
        "package K {\n  classifier Machine {\n    feature speed;\n  }\n  classifier Robot specializes Machine;\n}\n",
    );
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert!(out.contains("<<classifier>>"), "{out}");
    assert!(out.contains("speed"), "{out}");
    assert!(out.contains("--|>"), "{out}");
}

#[test]
fn quoted_names_escape() {
    let mut r = resolved("package 'My \"Odd\" Package' { part def 'A B'; }\n");
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert!(out.starts_with("@startuml\n"), "{out}");
    assert!(out.ends_with("@enduml\n"), "{out}");
    assert!(!out.contains("\"\"\""), "unescaped quote run: {out}");
}

const IC_DEMO: &str = "package Rig {
    port def FuelPort;
    item def Fuel;
    part def Tank { port fuelOut : FuelPort; }
    part rig {
        part tank : Tank;
        part eng { in port fuelIn : FuelPort; }
        connection c1 connect tank.fuelOut to eng.fuelIn;
        flow of fuel : Fuel from tank.fuelOut to eng.fuelIn;
    }
}
";

fn view_opts(view: View) -> VizOptions {
    VizOptions::default().with_view(view)
}

/// Ports declared on a part's definition render per usage, and both
/// the connection and the flow land on those per-usage port nodes.
#[test]
fn interconnection_golden() {
    let mut r = resolved(IC_DEMO);
    let out = plantuml(&mut r, None, &view_opts(View::Interconnection));
    let expected = "@startuml
package \"Rig\" as n1 {
  rectangle \"Tank\" as n2 <<part def>> {
    port \"fuelOut : FuelPort\" as n3
  }
  rectangle \"rig\" as n4 <<part>> {
    rectangle \"tank : Tank\" as n5 <<part>> {
      port \"fuelOut : FuelPort\" as n6
    }
    rectangle \"eng\" as n7 <<part>> {
      portin \"fuelIn : FuelPort\" as n8
    }
  }
}
n6 -- n8 : c1
n6 --> n8 : fuel : Fuel
@enduml
";
    assert_eq!(out, expected);
}

#[test]
fn interconnection_element_scoped() {
    let mut r = resolved(IC_DEMO);
    let root = r.resolve_qualified("Rig::rig").expect("resolves");
    let out = plantuml(&mut r, Some(root), &view_opts(View::Interconnection));
    assert!(!out.contains("package"), "{out}");
    assert!(out.contains("\"tank : Tank\""), "{out}");
    // The definition is off-diagram, but its port still renders on the
    // usage and the connection still lands on it.
    assert!(out.contains("port \"fuelOut : FuelPort\""), "{out}");
    assert!(out.contains(" : c1\n"), "{out}");
}

#[test]
fn state_golden() {
    let mut r = resolved(
        "package Ctrl {
    item def OpenCmd;
    item def CloseCmd;
    attribute ready : Boolean;
    action def Notify;
    state def DoorStates {
        entry; then Closed;
        state Closed;
        state Open;
        transition t1 first Closed accept OpenCmd if ready then Open;
        transition first Open accept CloseCmd do action notifier : Notify then Closed;
    }
}
",
    );
    let out = plantuml(&mut r, None, &view_opts(View::State));
    let expected = "@startuml
state \"DoorStates\" as n1 <<state def>> {
  state \"Closed\" as n2 <<state>>
  state \"Open\" as n3 <<state>>
  [*] --> n2
  n2 --> n3 : OpenCmd [ready]
  n3 --> n2 : CloseCmd / notifier : Notify
}
@enduml
";
    assert_eq!(out, expected);
}

#[test]
fn state_entry_do_exit_lines() {
    let mut r = resolved(
        "package P {
    action def Log;
    state def S {
        entry action hello : Log;
        do action work : Log;
        exit action bye : Log;
    }
}
",
    );
    let out = plantuml(&mut r, None, &view_opts(View::State));
    assert!(out.contains("n1 : entry / hello : Log"), "{out}");
    assert!(out.contains("n1 : do / work : Log"), "{out}");
    assert!(out.contains("n1 : exit / bye : Log"), "{out}");
}

#[test]
fn action_golden() {
    let mut r = resolved(
        "package Behavior {
    action def Brake {
        action sense { out attribute speed : Real; }
        action plan { in attribute speed : Real; }
        fork f1;
        action applyLeft;
        action applyRight;
        join j1;
        first sense then plan;
        first plan then f1;
        first f1 then applyLeft;
        first f1 then applyRight;
        first applyLeft then j1;
        first applyRight then j1;
        flow from sense.speed to plan.speed;
    }
    part sys { perform action doBrake : Brake; }
}
",
    );
    let out = plantuml(&mut r, None, &view_opts(View::Action));
    let expected = "@startuml
state \"Brake\" as n1 <<action def>> {
  state \"sense\" as n2 <<action>>
  state \"plan\" as n3 <<action>>
  state \"f1\" as n4 <<fork>>
  state \"applyLeft\" as n5 <<action>>
  state \"applyRight\" as n6 <<action>>
  state \"j1\" as n7 <<join>>
  n2 --> n3
  n3 --> n4
  n4 --> n5
  n4 --> n6
  n5 --> n7
  n6 --> n7
  n2 -[dashed]-> n3
}
state \"doBrake : Brake\" as n8 <<perform action>>
@enduml
";
    assert_eq!(out, expected);
}

/// `first start then …` / `… then done` spell the initial/final
/// pseudostates — with or without the library loaded (the written
/// spelling of an unresolved end still names them).
#[test]
fn action_start_done_pseudostates() {
    let mut r = resolved(
        "package B {
    action def A {
        action s1;
        first start then s1;
        first s1 then done;
    }
}
",
    );
    let out = plantuml(&mut r, None, &view_opts(View::Action));
    assert!(out.contains("[*] --> n2"), "{out}");
    assert!(out.contains("n2 --> [*]"), "{out}");
}

/// A genuinely unresolved succession source must not masquerade as an
/// initial-state edge.
#[test]
fn action_unresolved_source_drops_edge() {
    let mut r = resolved(
        "package B {
    action def A {
        action s1;
        first nonesuch then s1;
    }
}
",
    );
    let out = plantuml(&mut r, None, &view_opts(View::Action));
    assert!(!out.contains("[*] --> n2"), "{out}");
}

/// The Interaction Sequencing Examples shape: parts own event
/// occurrences ordered by bare `then`, messages connect
/// `part.event` chains. The succession partial order must re-sort the
/// messages (subscribe before publish, though publish is declared
/// first — the server lifeline says so), and the owning definition
/// draws a `box`.
#[test]
fn sequence_golden() {
    let mut r = resolved(
        "package Seq {
    part def PubSubSequence {
        part producer {
            event occurrence publish_source;
        }
        message publish_message from producer.publish_source to server.publish_target;
        part server {
            event occurrence subscribe_target;
            then event occurrence publish_target;
            then event occurrence deliver_source;
        }
        message subscribe_message from consumer.subscribe_source to server.subscribe_target;
        message deliver_message from server.deliver_source to consumer.deliver_target;
        part consumer {
            event occurrence subscribe_source;
            then event occurrence deliver_target;
        }
    }
}
",
    );
    let out = plantuml(&mut r, None, &view_opts(View::Sequence));
    let expected = "@startuml
box \"PubSubSequence\"
participant \"producer\" as n1
participant \"server\" as n2
participant \"consumer\" as n3
end box
n3 ->> n2 : subscribe_message
n1 ->> n2 : publish_message
n2 ->> n3 : deliver_message
@enduml
";
    assert_eq!(out, expected);
}

/// A message whose ends are parts (no events) still draws between
/// those lifelines, labelled with its payload when unnamed.
#[test]
fn sequence_part_ends_and_payload_label() {
    let mut r = resolved(
        "package P {
    item def Ping;
    part a;
    part b;
    message of ping : Ping from a to b;
}
",
    );
    let out = plantuml(&mut r, None, &view_opts(View::Sequence));
    assert!(out.contains("participant \"a\" as n1"), "{out}");
    assert!(out.contains("participant \"b\" as n2"), "{out}");
    assert!(out.contains("n1 ->> n2 : ping : Ping"), "{out}");
    assert!(!out.contains("box"), "package owners draw no box: {out}");
}

const CASE_DEMO: &str = "package Ops {
    part def Vehicle;
    part def Driver;
    use case unlock : UnlockVehicle;
    use case def DriveVehicle {
        subject vehicle : Vehicle;
        actor driver : Driver;
        objective { doc /* get from A to B safely */ }
        include unlock;
    }
    use case def UnlockVehicle;
}
";

/// Actors, subjects, objectives (with their doc bodies), and
/// `«include»` edges — the use-case diagram shape.
#[test]
fn case_golden() {
    let mut r = resolved(CASE_DEMO);
    let out = plantuml(&mut r, None, &view_opts(View::Case));
    let expected = "@startuml
usecase \"unlock : UnlockVehicle\" as n1 <<use case>>
usecase \"DriveVehicle\" as n2 <<use case def>>
rectangle \"vehicle : Vehicle\" as n3 <<subject>>
actor \"driver : Driver\" as n4
usecase \"UnlockVehicle\" as n5 <<use case def>>
n2 -- n3 : «subject»
n4 -- n2
note \"«objective»\\nget from A to B safely \" as o1
o1 .. n2
n2 ..> n1 : «include»
@enduml
";
    assert_eq!(out, expected);
}

/// The mixed view puts structure, ports, connectors, behavior edges,
/// cases, actors, typing edges, and notes on one canvas.
#[test]
fn mixed_everything_on_one_canvas() {
    let mut r = resolved(
        "package Demo {
    doc /* The whole system. */
    part def Vehicle { attribute mass : Real; port diag; }
    part car : Vehicle {
        part eng { port fuelIn; }
        part tank { port fuelOut; }
        connection c1 connect tank.fuelOut to eng.fuelIn;
    }
    state def Modes { state Off; state On; transition first Off then On; }
    use case def Commute { actor rider; }
    part sys2 { perform action go; exhibit state m : Modes; }
}
",
    );
    let out = plantuml(&mut r, None, &view_opts(View::Mixed));
    // Structure with per-usage definition ports and the connection.
    assert!(out.contains("rectangle \"car : Vehicle\""), "{out}");
    assert!(out.contains("port \"diag\""), "{out}");
    assert!(out.contains(" : c1\n"), "{out}");
    // Behavior: the transition edge between rendered states.
    assert!(out.contains("<<state def>>"), "{out}");
    assert!(out.contains("-->"), "{out}");
    // Cases and actors.
    assert!(out.contains("usecase \"Commute\""), "{out}");
    assert!(out.contains("actor \"rider\" as"), "{out}");
    // Typing edge and exhibit typing, doc note.
    assert!(out.contains("..>"), "{out}");
    assert!(out.contains("\" as c1\n"), "{out}");
    assert!(out.contains("The whole system."), "{out}");
    // Attributes stay off the canvas (no compartments in this dialect).
    assert!(!out.contains("mass"), "{out}");
}

/// Comment/doc bodies attach as notes in the tree view; `show_notes:
/// false` drops them.
#[test]
fn tree_notes_toggle() {
    let src = "package P {
    part def A { doc /* documented */ }
    comment about A /* commented */
}
";
    let mut r = resolved(src);
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert!(out.contains("\" as c1\n"), "{out}");
    assert!(out.contains("documented"), "{out}");
    assert!(out.contains("commented"), "{out}");
    let mut r = resolved(src);
    let out = plantuml(&mut r, None, &VizOptions::default().with_show_notes(false));
    assert!(!out.contains("note"), "{out}");
}

/// Prefix metadata joins the stereotype list; `show_metadata: false`
/// hides it (and metadata nodes).
#[test]
fn metadata_stereotypes_and_hide() {
    let src = "package P {
    metadata def Safety;
    #Safety part def Pump;
}
";
    let mut r = resolved(src);
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert!(out.contains("<<part def>> <<Safety>>"), "{out}");
    let mut r = resolved(src);
    let out = plantuml(
        &mut r,
        None,
        &VizOptions::default().with_show_metadata(false),
    );
    assert!(!out.contains("<<Safety>>"), "{out}");
}

/// `show_inherited` adds `^`-marked compartment lines one explicit
/// hop up; own members shadow.
#[test]
fn tree_inherited_compartments() {
    let mut r = resolved(
        "package P {
    part def Base { attribute mass : Real; attribute kind : Real; }
    part def Sub :> Base { attribute kind : Real; }
}
",
    );
    let out = plantuml(
        &mut r,
        None,
        &VizOptions::default().with_show_inherited(true),
    );
    assert!(out.contains("^mass"), "{out}");
    // Own `kind` shadows the inherited one.
    assert!(!out.contains("^kind"), "{out}");
}

/// `show_lib` gives referenced library types their own marked nodes;
/// without it they stay label-only.
#[test]
fn tree_show_lib_nodes() {
    let lib = sysmlv2_testkit::library_dir();
    let mut model = Model::new();
    model.load_library_dir(&lib).expect("library loads");
    model.add_source(
        "typed.sysml".to_string(),
        "package Typed { part def Sensor :> Parts::Part; }\n",
    );
    let mut r = ResolvedModel::build(&model);
    let out = plantuml(&mut r, None, &VizOptions::default().with_show_lib(true));
    assert!(out.contains("<<library>>"), "{out}");
    assert!(out.contains("--|>"), "{out}");
}

/// `show_imported` draws «import» edges between rendered nodes.
#[test]
fn tree_import_edges() {
    let mut r = resolved(
        "package Lib { part def Wheel; }
package Car { private import Lib::Wheel; part w : Wheel; }
",
    );
    let out = plantuml(
        &mut r,
        None,
        &VizOptions::default().with_show_imported(true),
    );
    assert!(out.contains("«import»"), "{out}");
}

/// Style options: line routing and the metaclass palette land in the
/// header; link templates land on node declarations.
#[test]
fn style_and_link_options() {
    let mut r = resolved(DEMO);
    let out = plantuml(
        &mut r,
        None,
        &VizOptions::default()
            .with_line_style(LineStyle::Ortho)
            .with_std_color(true)
            .with_link_template(Some("vscode://file/{file}:{line}".to_string())),
    );
    assert!(out.contains("skinparam linetype ortho"), "{out}");
    assert!(out.contains("BackgroundColor<<part def>>"), "{out}");
    assert!(out.contains("[[vscode://file/demo.sysml:2]]"), "{out}");
}

/// Every non-library corpus file emits a balanced diagram for every
/// view (parse-clean files only; resolution warnings are fine — viz
/// must tolerate unresolved references), and each view is non-empty
/// often enough to prove it actually renders the corpus.
#[test]
fn corpus_sweep_emits_balanced_diagrams() {
    let files: Vec<PathBuf> = sysmlv2_testkit::user_files();
    assert!(!files.is_empty());
    let views = [
        (View::Tree, 100),
        (View::Interconnection, 50),
        (View::State, 10),
        (View::Action, 30),
        (View::Sequence, 15),
        (View::Case, 10),
        (View::Mixed, 200),
    ];
    let mut emitted = [0usize; 7];
    for path in &files {
        let src = std::fs::read_to_string(path).expect("corpus file reads");
        let mut model = Model::new();
        let unit = model.add_source(path.display().to_string(), &src);
        if !unit.diagnostics.is_empty() {
            continue;
        }
        let mut r = ResolvedModel::build(&model);
        for (i, (view, _)) in views.iter().enumerate() {
            let out = plantuml(&mut r, None, &view_opts(*view));
            assert!(out.starts_with("@startuml\n"), "{}", path.display());
            assert!(out.ends_with("@enduml\n"), "{}", path.display());
            if out != "@startuml\n@enduml\n" {
                emitted[i] += 1;
            }
        }
    }
    for (i, (view, floor)) in views.iter().enumerate() {
        assert!(
            emitted[i] > *floor,
            "{view:?}: expected more than {floor} non-empty diagrams, got {}",
            emitted[i]
        );
    }
}

#[test]
fn graph_tree_carries_identity_rows_and_edges() {
    let mut r = resolved(DEMO);
    let opts = VizOptions::default();
    let g = sysmlv2_viz::graph(&mut r, None, &opts).expect("tree graph");

    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let by_label = |l: &str| nodes.iter().find(|n| n["label"] == l);

    // The package clusters its members via `parent`.
    let pkg = by_label("Vehicles").expect("package node");
    assert_eq!(pkg["kind"], "package");
    let vehicle = by_label("Vehicle").expect("Vehicle node");
    assert_eq!(vehicle["parent"], pkg["id"]);
    assert_eq!(vehicle["stereo"], "part def");

    // Rows carry element identity + spans (mass sits on line 3).
    let rows = vehicle["rows"].as_array().unwrap();
    let mass = rows
        .iter()
        .find(|r| r["label"].as_str().unwrap().starts_with("mass"))
        .unwrap();
    assert_eq!(mass["file"], "demo.sysml");
    assert_eq!(mass["line"], 3);
    assert!(mass["id"].is_string() && mass["qname"].as_str().unwrap().ends_with("::mass"));
    assert!(mass["label"].as_str().unwrap().contains("= 1200"));

    // Every node has an id; ids are unique.
    let mut ids: Vec<&str> = nodes.iter().map(|n| n["id"].as_str().unwrap()).collect();
    ids.sort_unstable();
    let before = ids.len();
    ids.dedup();
    assert_eq!(ids.len(), before, "duplicate node ids");

    // Edge kinds: composition (wheels under Vehicle), specialization
    // (SportsCar :> Vehicle), typing (myCar : SportsCar).
    let id_of = |l: &str| by_label(l).unwrap()["id"].as_str().unwrap().to_string();
    let has_edge = |kind: &str, s: &str, t: &str| {
        edges
            .iter()
            .any(|e| e["kind"] == kind && e["source"] == s && e["target"] == t)
    };
    assert!(has_edge(
        "composition",
        &id_of("Vehicle"),
        &id_of("wheels : Wheel [4]")
    ));
    assert!(has_edge(
        "specialization",
        &id_of("SportsCar"),
        &id_of("Vehicle")
    ));
    assert!(has_edge(
        "typing",
        &id_of("myCar : SportsCar"),
        &id_of("SportsCar")
    ));

    // Enum literals are rows with identity.
    let color = by_label("Phase").expect("enum node");
    assert_eq!(color["kind"], "enum");
    // Enumerations are variations by construction — the notation
    // header stays «enum def», no «variation» prefix.
    assert!(color["prefixes"].is_null(), "got {}", color["prefixes"]);
    let lits: Vec<&str> = color["rows"]
        .as_array()
        .unwrap()
        .iter()
        .map(|r| r["label"].as_str().unwrap())
        .collect();
    assert_eq!(lits, ["halt", "mid", "init"]);

    // Determinism: a second emission is identical.
    let g2 = sysmlv2_viz::graph(&mut r, None, &opts).expect("tree graph again");
    assert_eq!(g, g2);
}

#[test]
fn graph_rejects_views_without_emitters() {
    let mut r = resolved(DEMO);
    let opts = VizOptions::default().with_view(View::Sequence);
    assert!(sysmlv2_viz::graph(&mut r, None, &opts).is_err());
}

const IC_GRAPH_DEMO: &str = "package Rig {
    part def Pump {
        port outlet;
    }
    part pump : Pump;
    part tank {
        port inlet;
    }
    connect pump.outlet to tank.inlet;
    flow feed from pump to tank;
}
";

#[test]
fn graph_interconnection_edges_carry_connector_identity() {
    let mut r = resolved(IC_GRAPH_DEMO);
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).expect("ic graph");

    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let by_label = |l: &str| nodes.iter().find(|n| n["label"] == l);

    // Blocks nest in the package; the definition renders (has a port).
    let pump = by_label("pump : Pump").expect("pump block");
    assert_eq!(pump["kind"], "block");
    let tank = by_label("tank").expect("tank block");
    // tank's own port is a child node of the block.
    let inlet = by_label("inlet").expect("inlet port");
    assert_eq!(inlet["kind"], "port");
    assert_eq!(inlet["parent"], tank["id"]);
    // pump's definition port renders per-usage under a synthetic id but
    // keeps the definition port's identity for editing.
    let usage_port = nodes
        .iter()
        .find(|n| n["kind"] == "port" && n["parent"] == pump["id"])
        .expect("per-usage definition port");
    let uid = usage_port["id"].as_str().unwrap();
    assert!(uid.contains('~'), "synthetic id: {uid}");
    assert!(
        usage_port["qname"]
            .as_str()
            .unwrap()
            .ends_with("Pump::outlet")
    );

    // The connect edge: anonymous (no qname), but with id + span + kind,
    // running port-to-port.
    let connect = edges
        .iter()
        .find(|e| e["kind"] == "connect")
        .expect("connect edge");
    assert!(connect["qname"].is_null());
    assert!(connect["id"].is_string());
    assert_eq!(connect["file"], "demo.sysml");
    assert_eq!(connect["line"], 9);
    assert_eq!(connect["source"], usage_port["id"]);
    assert_eq!(connect["target"], inlet["id"]);

    // The named flow: directed, labelled, block-to-block.
    let flow = edges
        .iter()
        .find(|e| e["kind"] == "flow")
        .expect("flow edge");
    assert_eq!(flow["directed"], true);
    assert_eq!(flow["label"], "feed");
    assert_eq!(flow["source"], pump["id"]);
    assert_eq!(flow["target"], tank["id"]);
}

#[test]
fn graph_state_view_pseudostates_and_transition_identity() {
    const SRC: &str = "package M {
    item def Go;
    part machine {
        state def Cycle {
            entry; then idle;
            state idle;
            transition warmup
                first idle accept Go then running;
            state running;
        }
    }
}
";
    let mut r = resolved(SRC);
    let opts = VizOptions::default().with_view(View::State);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).expect("state graph");
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let by_label = |l: &str| nodes.iter().find(|n| n["label"] == l);

    // The composite nests its states; the part/package left no nodes.
    let cycle = by_label("Cycle").expect("composite");
    let idle = by_label("idle").expect("idle state");
    assert_eq!(idle["parent"], cycle["id"]);
    assert!(
        nodes
            .iter()
            .all(|n| n["label"] != "machine" && n["label"] != "M")
    );

    // The `entry; then idle` succession synthesized an initial
    // pseudostate scoped to the composite.
    let pseudo = nodes
        .iter()
        .find(|n| n["kind"] == "pseudo")
        .expect("initial node");
    assert_eq!(pseudo["stereo"], "initial");
    assert_eq!(pseudo["parent"], cycle["id"]);
    let entry = edges
        .iter()
        .find(|e| e["source"] == pseudo["id"])
        .expect("entry edge");
    assert_eq!(entry["target"], idle["id"]);

    // The named transition is an edge with full element identity and
    // the trigger in its label.
    let t = edges
        .iter()
        .find(|e| e["kind"] == "transition")
        .expect("transition edge");
    assert!(t["qname"].as_str().unwrap().ends_with("Cycle::warmup"));
    assert_eq!(t["label"], "Go");
    assert_eq!(t["source"], idle["id"]);
    assert_eq!(t["target"], by_label("running").unwrap()["id"]);
    assert_eq!(t["directed"], true);
}

/// `toGraph` in the action view draws transitions as edges, as the
/// PlantUML action view has: a decision node's guarded branches (`if g
/// then b;`, `else c;`) leave the decision node, their implicit source, a
/// `then` after a branch leaves it too, and a guarded succession with a
/// written source (`first a if g then b;`) leaves that source.
#[test]
fn graph_action_view_draws_decision_branches_and_guarded_successions() {
    const SRC: &str = "package Repro {
    action def Basic {
        attribute x = 1;
        action a; action b; action c; action e;
        first a then d;
        decide d;
            if x > 0 then b;
            then c;
            else e;
    }
    action def Router {
        attribute ok : Boolean;
        action ingest; action fast; action slow;
        first ingest if ok then fast;
        else slow;
    }
}
";
    let mut r = resolved(SRC);
    let opts = VizOptions::default().with_view(View::Action);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).expect("action graph");
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let id_of = |label: &str| {
        nodes
            .iter()
            .find(|n| n["label"] == label)
            .unwrap_or_else(|| panic!("no node {label}: {nodes:?}"))["id"]
            .clone()
    };
    let edge = |source: &str, target: &str| {
        let (s, t) = (id_of(source), id_of(target));
        edges
            .iter()
            .find(|e| e["source"] == s && e["target"] == t)
            .unwrap_or_else(|| panic!("no edge {source} -> {target}: {edges:?}"))
    };
    // The written succession, the decision's branches, the `then` past
    // the guarded branch.
    assert_ne!(edge("a", "d")["kind"], "transition");
    let guarded = edge("d", "b");
    assert_eq!(guarded["kind"], "transition");
    assert_eq!(guarded["metaclass"], "TransitionUsage");
    assert_eq!(guarded["label"], "[x > 0]");
    assert_eq!(guarded["directed"], true);
    assert_ne!(edge("d", "c")["kind"], "transition");
    let otherwise = edge("d", "e");
    assert_eq!(otherwise["kind"], "transition");
    assert!(otherwise.get("label").is_none(), "{otherwise:?}");
    // A guarded succession with a written source.
    let fast = edge("ingest", "fast");
    assert_eq!(fast["kind"], "transition");
    assert_eq!(fast["label"], "[ok]");
    assert_eq!(edge("ingest", "slow")["kind"], "transition");
    // Every transition drew: none was dropped for want of a source.
    let transitions = edges.iter().filter(|e| e["kind"] == "transition").count();
    assert_eq!(transitions, 4, "{edges:?}");
}

/// A view usage directs its own diagram: `expose`/`filter` pick the
/// elements (finest exposed granularity — the exposed container defers
/// to its individually exposed members, so filtered-out siblings stay
/// off the canvas) and `render` picks the style. Metadata-filtered
/// connectors disappear as edges; the kept connector still draws
/// between the kept parts' ports. The ports the parts inherit from
/// their definitions are exposed too, since a part's visible members
/// include its inherited ones, but they draw once, on each part's box,
/// never again as boxes of their own.
#[test]
fn view_directed_rendering() {
    let src = "package VD {
        metadata def LOUD;
        port def Jack;
        interface def Cable { end a : Jack; end b : Jack; }
        part def Amp { port line : Jack; port aux : Jack; }
        part def Speaker { port feed : Jack; }
        part stage {
            part amp : Amp;
            part main : Speaker;
            part monitor : Speaker;
            interface connect amp.line to main.feed;
            #LOUD interface connect amp.aux to monitor.feed;
        }
        view quiet {
            expose stage::**;
            filter not (@LOUD);
        }
        view whole {
            expose Amp;
            expose stage::**;
        }
    }";
    let mut r = resolved(src);
    let view = r.resolve_qualified("VD::quiet").expect("view resolves");
    let (style, roots) = sysmlv2_viz::view_directed(&mut r, view).expect("a view usage");
    // No `render` member: the style stays the caller's choice.
    assert_eq!(style, None);
    let names: Vec<String> = roots
        .iter()
        .map(|&e| {
            r.element_qualified_name(e)
                .unwrap_or_else(|| r.element_type(e).to_string())
        })
        .collect();
    assert_eq!(
        names,
        [
            "VD::stage::amp",
            "VD::stage::main",
            "VD::stage::monitor",
            "InterfaceUsage"
        ]
    );
    let opts = VizOptions::default()
        .with_view(View::Interconnection)
        .with_roots(Some(roots));
    let out = plantuml(&mut r, None, &opts);
    // Exactly one connector edge: the untagged cable draws, the
    // LOUD-tagged one is filtered off. The untagged parts (including
    // `monitor`) all stay — only a provably-matching condition hides a
    // member — and the `stage` wrapper defers to its exposed members
    // (no duplicate subtrees). Each part's box carries its definition's
    // ports, and those are the only port nodes.
    assert_eq!(
        out,
        r#"@startuml
rectangle "amp : Amp" as n1 <<part>> {
  port "line : Jack" as n2
  port "aux : Jack" as n3
}
rectangle "main : Speaker" as n4 <<part>> {
  port "feed : Jack" as n5
}
rectangle "monitor : Speaker" as n6 <<part>> {
  port "feed : Jack" as n7
}
n2 -- n5 : «interface»
@enduml
"#
    );
    // A definition the view exposes whole stays a node of its own: the
    // ports `amp` inherits from it do not take it apart.
    let view = r.resolve_qualified("VD::whole").expect("view resolves");
    let (_, roots) = sysmlv2_viz::view_directed(&mut r, view).expect("a view usage");
    let names: Vec<String> = roots
        .iter()
        .filter_map(|&e| r.element_qualified_name(e))
        .collect();
    assert!(names.contains(&"VD::Amp".to_string()), "{names:?}");
    assert!(
        !names
            .iter()
            .any(|n| ["VD::Amp::", "VD::Speaker::", "VD::Jack::"]
                .iter()
                .any(|owner| n.starts_with(owner))),
        "{names:?}"
    );
    // A non-view element answers None.
    let part = r.resolve_qualified("VD::stage").unwrap();
    assert!(sysmlv2_viz::view_directed(&mut r, part).is_none());
}

/// A view usage without a `render` member of its own takes its style
/// from the rendering its definition declares; its own `render` member
/// wins over the inherited one.
#[test]
fn view_directed_style_follows_an_inherited_rendering() {
    let mut r = resolved(
        "package VI {
            package Views {
                rendering asTreeDiagram;
                rendering asInterconnectionDiagram;
            }
            part rig { part amp; }
            view def Wiring { render Views::asInterconnectionDiagram; }
            view wiring : Wiring { expose rig; }
            view outline : Wiring {
                expose rig;
                render Views::asTreeDiagram;
            }
        }",
    );
    let rig = r.resolve_qualified("VI::rig").unwrap();
    for (name, expected) in [
        ("VI::wiring", View::Interconnection),
        ("VI::outline", View::Tree),
    ] {
        let view = r.resolve_qualified(name).expect("view resolves");
        let (style, roots) = sysmlv2_viz::view_directed(&mut r, view).expect("a view usage");
        assert_eq!(style, Some(expected), "{name}");
        assert_eq!(roots, vec![rig], "{name}");
    }
}

/// Finest granularity follows ownership whatever else inherits: a
/// definition whose members the view reaches through ownership still
/// defers to them, so the member its condition rejects stays off the
/// diagram, though a specialization inherits the same members.
#[test]
fn view_directed_owned_members_defer_despite_inheritance() {
    let mut r = resolved(
        "package Kit {
            metadata def LOUD;
            part def Base { part x; #LOUD part y; }
            part def Derived :> Base;
        }
        package Show {
            view kit {
                expose Kit::**;
                filter not (@Kit::LOUD);
            }
        }",
    );
    let view = r.resolve_qualified("Show::kit").expect("view resolves");
    let (_, roots) = sysmlv2_viz::view_directed(&mut r, view).expect("a view usage");
    let names: Vec<String> = roots
        .iter()
        .filter_map(|&e| r.element_qualified_name(e))
        .collect();
    assert!(
        names.contains(&"Kit::Base::x".to_string())
            && names.contains(&"Kit::Derived".to_string())
            && !names.contains(&"Kit::Base".to_string()),
        "{names:?}"
    );
    let out = plantuml(&mut r, None, &VizOptions::default().with_roots(Some(roots)));
    assert!(!out.contains("\"y\""), "{out}");
}

/// `expose x::*` exposes what `x` inherits besides what it owns, from
/// the model's own definitions and from the standard library alike.
/// Those members render through `x`, so the diagram gets `x`'s owned
/// members only, not a node for every feature a part inherits.
#[test]
fn view_directed_leaves_inherited_members_to_their_inheritor() {
    let lib = sysmlv2_testkit::library_dir();
    let mut model = Model::new();
    model.load_library_dir(&lib).expect("library loads");
    model.add_source(
        "rig.sysml".to_string(),
        "package Rig {
            part def Frame { part brace; }
            part rig : Frame {
                part amp;
                part spare;
            }
            view shallow { expose rig::*; }
        }",
    );
    let mut r = ResolvedModel::build(&model);
    let view = r.resolve_qualified("Rig::shallow").expect("view resolves");
    let exposed = r.view_exposed_elements(view);
    let brace = r.resolve_qualified("Rig::Frame::brace").unwrap();
    assert!(exposed.contains(&brace));
    assert!(exposed.iter().any(|&e| r.is_library_element(e)));
    let (_, roots) = sysmlv2_viz::view_directed(&mut r, view).expect("a view usage");
    let names: Vec<String> = roots
        .iter()
        .map(|&e| {
            r.element_qualified_name(e)
                .unwrap_or_else(|| r.element_type(e).to_string())
        })
        .collect();
    assert_eq!(names, ["Rig::rig::amp", "Rig::rig::spare"]);
}

/// Action-view flow anchors: a bare `then x;` succession sources from
/// the member that precedes it, an inline node declaration
/// (`then fork;`, `then action last { … }`) resolves the succession
/// that introduced it, consecutive `then`s after a fork all fan out
/// from it, and `first start;` resets the anchor to the initial
/// pseudostate. Guarded shorthands (`first a if g then b; else c;`)
/// render as guarded edges branching from one node.
#[test]
fn action_view_flow_anchors() {
    let src = "package Flow {
        private import ScalarValues::*;
        action def Pipeline {
            action stage1;
            then junction;
            action stage2;
            then junction;
            first start;
            then fork;
                then stage1;
                then stage2;
            join junction;
            then action wrap;
        }
        action def Router {
            attribute ok : Boolean;
            action ingest;
            action fast;
            action slow;
            first start;
            then ingest;
            first ingest if ok then fast;
            else slow;
        }
    }";
    let mut r = resolved(src);
    let opts = VizOptions::default().with_view(View::Action);
    let out = plantuml(&mut r, None, &opts);
    let alias = |name: &str| {
        let tag = format!("\"{name}\" as ");
        let at = out
            .find(&tag)
            .unwrap_or_else(|| panic!("{name} missing: {out}"));
        out[at + tag.len()..]
            .split_whitespace()
            .next()
            .unwrap()
            .to_string()
    };
    let (s1, s2, fork, join, wrap) = (
        alias("stage1"),
        alias("stage2"),
        alias("(fork)"),
        alias("junction"),
        alias("wrap"),
    );
    for edge in [
        format!("{s1} --> {join}"),
        format!("{s2} --> {join}"),
        format!("[*] --> {fork}"),
        format!("{fork} --> {s1}"),
        format!("{fork} --> {s2}"),
        format!("{join} --> {wrap}"),
    ] {
        assert!(out.contains(&edge), "missing `{edge}` in {out}");
    }
    let (ingest, fast, slow) = (alias("ingest"), alias("fast"), alias("slow"));
    for edge in [
        format!("[*] --> {ingest}"),
        format!("{ingest} --> {fast} : [ok]"),
        format!("{ingest} --> {slow}"),
    ] {
        assert!(out.contains(&edge), "missing `{edge}` in {out}");
    }
}

/// Tree view distinguishes composite from referential ownership: a
/// `ref part` child hangs off the hollow rhomb (`o--`), a composite
/// child off the solid one (`*--`) — the graphical notation must
/// tell the two apart.
#[test]
fn tree_view_referential_vs_composite_edges() {
    let src = "package RC {
        part def P;
        part def Holder {
            part solid : P;
            ref part hollow : P;
        }
    }";
    let mut r = resolved(src);
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert_eq!(out.matches(" *-- ").count(), 1, "{out}");
    assert_eq!(out.matches(" o-- ").count(), 1, "{out}");
}

/// State-view subaction lines: an anonymous `do action { … }` block
/// lists its steps instead of disappearing, per nesting level.
#[test]
fn state_view_anonymous_do_actions_list_steps() {
    let src = "package M {
        action def Chore;
        state def Machine {
            state idle;
            state busy {
                do action {
                    sweep : Chore;
                    polish;
                }
                state deep {
                    do action { rinse; }
                }
            }
        }
    }";
    let mut r = resolved(src);
    let opts = VizOptions::default().with_view(View::State);
    let out = plantuml(&mut r, None, &opts);
    assert!(out.contains(": do / sweep : Chore; polish"), "{out}");
    assert!(out.contains(": do / rinse"), "{out}");
}

// ---------------------------------------------------------------------------
// Graphical-notation gates: graphical-notation vocabulary in
// the structured graph — the def/usage/ref shape triad, header prefix
// keywords, the specialization split, import granularity, dependency
// and «keyword» reference edges, connector end payloads, port
// direction/conjugation.
// ---------------------------------------------------------------------------

#[test]
fn graph_nodes_carry_notation_triad_and_prefixes() {
    const SRC: &str = "package P {
    abstract part def V;
    part def W :> V;
    part def Ctx {
        part p : W;
        ref part q : W;
    }
    part top : W;
}
";
    let mut r = resolved(SRC);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let by_label = |l: &str| nodes.iter().find(|n| n["label"] == l).unwrap();

    let v = by_label("V");
    assert_eq!(v["nodeKind"], "def");
    assert_eq!(v["prefixes"], serde_json::json!(["abstract"]));
    let w = by_label("W");
    assert_eq!(w["nodeKind"], "def");
    assert!(w["prefixes"].is_null());
    assert_eq!(by_label("p : W")["nodeKind"], "usage");
    assert_eq!(by_label("q : W")["nodeKind"], "ref");
    // Package-level usages are unfeatured (non-composite by
    // construction) — never read as declared refs.
    assert_eq!(by_label("top : W")["nodeKind"], "usage");
    // The composition edge to a declared-`ref` child is the notation's
    // hollow-diamond non-composite membership.
    let edges = g["edges"].as_array().unwrap();
    let edge_to = |l: &str| {
        let id = by_label(l)["id"].as_str().unwrap();
        edges
            .iter()
            .find(|e| e["kind"] == "composition" && e["target"] == id)
            .unwrap()
    };
    assert_eq!(edge_to("q : W")["composite"], false);
    assert!(edge_to("p : W")["composite"].is_null());
}

#[test]
fn graph_specialization_edges_carry_rel_split() {
    const SRC: &str = "package P {
    part def A;
    part def B :> A;
    part x : A;
    part y :> x;
}
";
    let mut r = resolved(SRC);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let id_of = |l: &str| {
        nodes.iter().find(|n| n["label"] == l).unwrap()["id"]
            .as_str()
            .unwrap()
            .to_string()
    };
    let rel_edge = |rel: &str, s: &str, t: &str| {
        edges.iter().any(|e| {
            e["kind"] == "specialization" && e["rel"] == rel && e["source"] == s && e["target"] == t
        })
    };
    assert!(rel_edge("subclassification", &id_of("B"), &id_of("A")));
    assert!(rel_edge("subsetting", &id_of("y"), &id_of("x : A")));
}

#[test]
fn graph_import_edges_carry_granularity() {
    const SRC: &str = "package Lib { part def L; }
package NsUser { import Lib::*; part def A; }
package RecUser { import Lib::**; part def B; }
package MemUser { import Lib::L; part def C; }
";
    let mut r = resolved(SRC);
    let opts = VizOptions::default().with_show_imported(true);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let id_of = |l: &str| {
        nodes.iter().find(|n| n["label"] == l).unwrap()["id"]
            .as_str()
            .unwrap()
            .to_string()
    };
    let import_kind = |s: &str| {
        edges
            .iter()
            .find(|e| e["kind"] == "import" && e["source"] == s)
            .map(|e| e["importKind"].as_str().unwrap().to_string())
    };
    assert_eq!(import_kind(&id_of("NsUser")).as_deref(), Some("namespace"));
    assert_eq!(import_kind(&id_of("RecUser")).as_deref(), Some("recursive"));
    // The membership import targets the element, drawn as L's node.
    let mem = edges
        .iter()
        .find(|e| e["kind"] == "import" && e["source"] == id_of("MemUser"))
        .expect("membership import edge");
    assert_eq!(mem["importKind"], "membership");
    assert_eq!(mem["target"], id_of("L"));
}

#[test]
fn graph_dependency_edges_between_drawn_nodes() {
    const SRC: &str = "package P {
    part def A;
    part def B;
    dependency Use from A to B;
}
";
    let mut r = resolved(SRC);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let id_of = |l: &str| {
        nodes.iter().find(|n| n["label"] == l).unwrap()["id"]
            .as_str()
            .unwrap()
            .to_string()
    };
    let dep = edges
        .iter()
        .find(|e| e["kind"] == "dependency")
        .expect("dependency edge");
    assert_eq!(dep["source"], id_of("A"));
    assert_eq!(dep["target"], id_of("B"));
    assert_eq!(dep["label"], "Use");
    assert_eq!(dep["directed"], true);
    assert!(
        dep["id"].is_string(),
        "dependency edge carries element identity"
    );
}

#[test]
fn graph_satisfy_edge_links_shorthand_to_requirement() {
    const SRC: &str = "package P {
    requirement def R;
    requirement r : R;
    part system;
    satisfy r by system;
}
";
    let mut r = resolved(SRC);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let req = nodes
        .iter()
        .find(|n| n["label"] == "r : R")
        .expect("requirement node");
    let sat = nodes
        .iter()
        .find(|n| n["metaclass"] == "SatisfyRequirementUsage")
        .expect("satisfy shorthand node");
    let edge = edges
        .iter()
        .find(|e| e["kind"] == "satisfy")
        .expect("satisfy edge");
    assert_eq!(edge["source"], sat["id"]);
    assert_eq!(edge["target"], req["id"]);
    assert_eq!(edge["directed"], true);
}

#[test]
fn graph_connector_ends_carry_roles() {
    const SRC: &str = "package Rig {
    part def Pump { port outlet; }
    part pump : Pump;
    part tank { port inlet; }
    connection pipe connect supply ::> pump.outlet to sink ::> tank.inlet;
}
";
    let mut r = resolved(SRC);
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let edges = g["edges"].as_array().unwrap();
    let conn = edges
        .iter()
        .find(|e| e["kind"] == "connect")
        .expect("connection edge");
    assert_eq!(conn["label"], "pipe");
    assert_eq!(conn["sourceRole"], "supply");
    assert_eq!(conn["targetRole"], "sink");
}

#[test]
fn graph_ports_carry_direction_and_conjugation() {
    const SRC: &str = "package Rig {
    port def Cmd;
    part def Pump {
        in port intake;
        out port outlet;
    }
    part pump : Pump;
    part ctrl {
        port bus : ~Cmd;
    }
    connect ctrl.bus to pump.intake;
}
";
    let mut r = resolved(SRC);
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let port = |l: &str| {
        nodes
            .iter()
            .find(|n| n["kind"] == "port" && n["label"].as_str().unwrap().starts_with(l))
            .unwrap_or_else(|| panic!("port {l}"))
    };
    assert_eq!(port("intake")["direction"], "in");
    assert_eq!(port("outlet")["direction"], "out");
    assert_eq!(port("bus")["conjugated"], true);
    assert!(port("intake")["conjugated"].is_null());
}

#[test]
fn graph_nodes_carry_alias_lists() {
    const SRC: &str = "package P {
    part def V;
    part v : V;
    alias theCar for v;
    alias auto for v;
}
";
    let mut r = resolved(SRC);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let v = nodes.iter().find(|n| n["label"] == "v : V").unwrap();
    assert_eq!(v["aliases"], serde_json::json!(["theCar", "auto"]));
    assert!(nodes.iter().find(|n| n["label"] == "V").unwrap()["aliases"].is_null());
}

#[test]
fn graph_portion_edges_replace_plain_subsetting() {
    const SRC: &str = "package P {
    occurrence o;
    timeslice t :> o;
    snapshot s :> o;
    occurrence plain :> o;
}
";
    let mut r = resolved(SRC);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let id_of = |l: &str| {
        nodes.iter().find(|n| n["label"] == l).unwrap()["id"]
            .as_str()
            .unwrap()
            .to_string()
    };
    let t = nodes.iter().find(|n| n["label"] == "t").unwrap();
    assert_eq!(t["portion"], "timeslice");
    let portion = |s: &str, kind: &str| {
        edges
            .iter()
            .any(|e| e["kind"] == "portion" && e["portionKind"] == kind && e["source"] == s)
    };
    assert!(portion(&id_of("t"), "timeslice"));
    assert!(portion(&id_of("s"), "snapshot"));
    // A plain occurrence subsetting stays a specialization edge.
    assert!(edges.iter().any(|e| {
        e["kind"] == "specialization" && e["rel"] == "subsetting" && e["source"] == id_of("plain")
    }));
}

#[test]
fn graph_connector_ends_carry_adornments() {
    const SRC: &str = "package Rig {
    part def Pump { port outlet; }
    part pump : Pump;
    part tank { port inlet; }
    connection pipe {
        end supply [1] ::> pump.outlet;
        end sink [0..2] ::> tank.inlet;
    }
}
";
    let mut r = resolved(SRC);
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let edges = g["edges"].as_array().unwrap();
    let conn = edges
        .iter()
        .find(|e| e["kind"] == "connect")
        .expect("connection edge");
    assert_eq!(conn["sourceMultiplicity"], "[1]");
    assert_eq!(conn["targetMultiplicity"], "[0..2]");
    // The written `::>` end targets are the ends themselves, not
    // c-adornment subsettings — no adornment noise on plain ends.
    assert!(
        conn["sourceAdornments"].is_null(),
        "got {}",
        conn["sourceAdornments"]
    );
}

#[test]
fn graph_rows_carry_detail_tail() {
    const SRC: &str = "package P {
    attribute def A1;
    attribute def A2;
    part def Base {
        attribute a : A1;
    }
    part def K :> Base {
        attribute many : A1 [1..*] ordered nonunique;
        attribute b : A2 subsets many;
        attribute c : A1 redefines a;
    }
}
";
    let mut r = resolved(SRC);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let k = nodes.iter().find(|n| n["label"] == "K").unwrap();
    let rows = k["rows"].as_array().unwrap();
    let row = |name: &str| {
        rows.iter()
            .find(|r| r["label"].as_str().unwrap().starts_with(name))
            .unwrap_or_else(|| panic!("row {name}"))
    };
    assert_eq!(row("many")["detail"], "ordered nonunique");
    assert_eq!(row("b")["detail"], "subsets many");
    assert_eq!(row("c")["detail"], "redefines a");
    assert!(row("many")["label"].as_str().unwrap().contains("[1..*]"));
}

#[test]
fn graph_import_edges_carry_visibility() {
    const SRC: &str = "package Lib { part def L; }
package Priv { private import Lib::*; part def A; }
package Pub { import Lib::*; part def B; }
";
    let mut r = resolved(SRC);
    let opts = VizOptions::default().with_show_imported(true);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let id_of = |l: &str| {
        nodes.iter().find(|n| n["label"] == l).unwrap()["id"]
            .as_str()
            .unwrap()
            .to_string()
    };
    let import_of = |s: &str| {
        edges
            .iter()
            .find(|e| e["kind"] == "import" && e["source"] == s)
            .unwrap()
    };
    assert_eq!(import_of(&id_of("Priv"))["visibility"], "private");
    assert!(import_of(&id_of("Pub"))["visibility"].is_null());
}

#[test]
fn graph_action_view_params_are_border_chips() {
    const SRC: &str = "package P {
    action def Capture {
        in shots : ScalarValues::Real;
        out frames : ScalarValues::Real;
        action snap;
        action store;
        first snap then store;
    }
}
";
    let mut r = resolved(SRC);
    let opts = VizOptions::default().with_view(View::Action);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let capture = nodes
        .iter()
        .find(|n| n["label"] == "Capture")
        .expect("action def node");
    let param = |name: &str| {
        nodes
            .iter()
            .find(|n| n["kind"] == "param" && n["label"].as_str().unwrap().starts_with(name))
            .unwrap_or_else(|| panic!("param {name}"))
    };
    assert_eq!(param("shots")["direction"], "in");
    assert_eq!(param("frames")["direction"], "out");
    assert_eq!(param("shots")["parent"], capture["id"]);
}

// ---------------------------------------------------------------------------
// Summary emission (large scopes)
// ---------------------------------------------------------------------------

const SUMMARY_MODEL: &str = "package P {
    doc /* on P */
    package Q {
        part def A;
        part def B :> A;
        part q : A;
        comment about A /* c2 */
    }
    part def D { part d1 : Q::A; part d2 : Q::B; }
    part def L;
    comment about L /* c1 */
}
";

fn summary_graph(
    r: &mut ResolvedModel,
    open: &[&str],
    note_budget: usize,
    leaf_budget: usize,
) -> serde_json::Value {
    let open = open
        .iter()
        .map(|q| r.resolve_qualified(q).expect(q))
        .collect();
    let opts = VizOptions::default().with_summary(Some(sysmlv2_viz::SummaryOptions {
        open,
        note_budget,
        leaf_budget,
        unbounded: Vec::new(),
    }));
    sysmlv2_viz::graph(r, None, &opts).unwrap()
}

fn node<'a>(g: &'a serde_json::Value, qname: &str) -> &'a serde_json::Value {
    g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["qname"] == qname)
        .unwrap_or_else(|| panic!("node {qname}"))
}

#[test]
fn summary_closed_root_is_one_node_with_counts() {
    let mut r = resolved(SUMMARY_MODEL);
    let g = summary_graph(&mut r, &[], 200, 500);
    let ids: Vec<&str> = g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|n| n["qname"].as_str())
        .collect();
    // P plus its own doc note (P is drawn, so its note draws too); nothing below.
    assert_eq!(
        ids.iter()
            .filter(|q| !q.contains("doc") && !q.contains("comment"))
            .collect::<Vec<_>>(),
        vec![&"P"]
    );
    let s = &node(&g, "P")["summary"];
    assert_eq!(s["open"], false);
    assert_eq!(s["members"], 3, "Q, D, L");
    assert_eq!(s["containers"], 2, "Q and the owner card D");
    assert_eq!(s["leaves"], 1);
    assert_eq!(s["notes"], 2, "c1 on L and c2 on A hide under P");
    assert_eq!(s["hidden"], 8, "Q, A, B, q, D, d1, d2, L");
    assert_eq!(s["truncated"], 0);
    // Every reference stays inside P: no aggregated edge.
    assert!(
        g["edges"]
            .as_array()
            .unwrap()
            .iter()
            .all(|e| e["kind"] == "note")
    );
}

#[test]
fn summary_open_root_draws_members_and_aggregates_cross_container_edges() {
    let mut r = resolved(SUMMARY_MODEL);
    let g = summary_graph(&mut r, &["P"], 200, 500);
    assert_eq!(node(&g, "P")["summary"]["open"], true);
    let q = &node(&g, "P::Q")["summary"];
    assert_eq!(q["open"], false);
    assert_eq!(q["members"], 3, "A, B, q");
    assert_eq!(q["containers"], 0);
    assert_eq!(q["notes"], 1);
    let d = &node(&g, "P::D")["summary"];
    assert_eq!(d["members"], 2, "d1, d2 hide under the closed owner card");
    assert_eq!(d["hidden"], 2);
    assert_eq!(q["hidden"], 3);
    assert!(
        node(&g, "P::L").get("summary").is_none(),
        "a leaf carries no summary"
    );
    assert!(
        g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .all(|n| n["qname"] != "P::D::d1")
    );
    // d1 : A and d2 : B become one typing bundle D → Q with a count and no identity.
    let bundle: Vec<&serde_json::Value> = g["edges"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["kind"] == "typing")
        .collect();
    assert_eq!(bundle.len(), 1);
    assert_eq!(bundle[0]["source"], node(&g, "P::D")["id"]);
    assert_eq!(bundle[0]["target"], node(&g, "P::Q")["id"]);
    assert_eq!(bundle[0]["count"], 2);
    assert!(bundle[0].get("id").is_none());
    assert_eq!(d["edgesOut"], 2);
    assert_eq!(q["edgesIn"], 2);
}

#[test]
fn summary_leaf_budget_truncates_and_counts() {
    let mut r = resolved(SUMMARY_MODEL);
    let g = summary_graph(&mut r, &["P"], 200, 1);
    let p = &node(&g, "P")["summary"];
    assert_eq!(p["members"], 3);
    assert_eq!(p["truncated"], 2, "D and L beyond the budget of one");
    assert_eq!(p["notes"], 1, "c1 on the hidden L");
    assert!(
        g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .all(|n| n["qname"] != "P::D" && n["qname"] != "P::L")
    );
    // The hidden D's typings now leave P for Q.
    let bundle: Vec<&serde_json::Value> = g["edges"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| e["kind"] == "typing")
        .collect();
    assert_eq!(bundle.len(), 1);
    assert_eq!(bundle[0]["source"], node(&g, "P")["id"]);
    assert_eq!(bundle[0]["count"], 2);
}

#[test]
fn summary_would_draw_counts_the_nodes_and_what_they_hide() {
    let mut r = resolved(SUMMARY_MODEL);
    // P and its doc note, plus the eight drawable elements below P
    let closed = summary_graph(&mut r, &[], 200, 500);
    assert_eq!(closed["nodes"].as_array().unwrap().len(), 2);
    assert_eq!(sysmlv2_viz::summary_would_draw(&closed), 2 + 8);
    // opened at the root: every drawn node, plus what Q and D still hide
    let open = summary_graph(&mut r, &["P"], 200, 500);
    let nodes = open["nodes"].as_array().unwrap();
    let hidden: u64 = ["P::Q", "P::D"]
        .iter()
        .map(|q| node(&open, q)["summary"]["hidden"].as_u64().unwrap())
        .sum();
    assert!(hidden > 0);
    assert_eq!(
        sysmlv2_viz::summary_would_draw(&open),
        nodes.len() + usize::try_from(hidden).unwrap()
    );
    // a full picture is its node count
    let full = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    assert_eq!(
        sysmlv2_viz::summary_would_draw(&full),
        full["nodes"].as_array().unwrap().len()
    );
    assert_eq!(
        sysmlv2_viz::summary_would_draw(&serde_json::json!({"nodes": []})),
        0
    );
    assert_eq!(sysmlv2_viz::summary_would_draw(&serde_json::json!({})), 0);
}

#[test]
fn summary_counts_hidden_port_copies_at_every_depth() {
    let mut r = resolved(
        "package P {
            port def Signal;
            port def Loop { port again : Loop; }
            port def Bank { port pin : Signal; }
            part def Device { port bank : Bank { port localPin : Signal; } port recursivePort : Loop; }
            part a : Device; part b : Device;
            package Q { part c : Device; }
        }",
    );
    let opts = VizOptions::default().with_show_notes(false);
    let full = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let total = full["nodes"].as_array().unwrap().len();
    for (open, budget) in [
        (vec![], usize::MAX),
        (vec!["P"], usize::MAX),
        (vec!["P", "P::Device", "P::Q"], 2),
        (vec!["P", "P::Device", "P::Q"], usize::MAX),
    ] {
        let opts = opts.clone().with_summary(Some(sysmlv2_viz::SummaryOptions {
            open: open
                .iter()
                .map(|name| r.resolve_qualified(name).unwrap())
                .collect(),
            leaf_budget: budget,
            ..Default::default()
        }));
        let summary = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
        assert_eq!(
            sysmlv2_viz::summary_would_draw(&summary),
            total,
            "{open:?}, budget {budget}"
        );
        for limit in [0, total - 1, total, total + 1] {
            assert_eq!(
                sysmlv2_viz::summary_would_draw_within(&mut r, None, &opts, limit).unwrap(),
                (limit >= total).then_some(total),
                "{open:?}, budget {budget}, limit {limit}"
            );
        }
    }
}

#[test]
fn summary_unbounded_container_draws_every_member() {
    let mut r = resolved(SUMMARY_MODEL);
    let q = r.resolve_qualified("P::Q").expect("P::Q");
    let open = ["P", "P::Q"]
        .iter()
        .map(|name| r.resolve_qualified(name).expect(name))
        .collect();
    let opts = VizOptions::default().with_summary(Some(sysmlv2_viz::SummaryOptions {
        open,
        note_budget: 200,
        leaf_budget: 1,
        unbounded: vec![q],
    }));
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    // Q is unbounded: all three members draw, nothing truncated.
    let qs = &node(&g, "P::Q")["summary"];
    assert_eq!(qs["members"], 3);
    assert_eq!(
        qs["truncated"], 0,
        "an unbounded container draws every member"
    );
    assert!(
        g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|n| n["qname"] == "P::Q::B")
    );
    // P keeps the shared budget: Q drew, D and L are truncated.
    let ps = &node(&g, "P")["summary"];
    assert_eq!(ps["truncated"], 2, "the override is per container");
}

#[test]
fn summary_note_budget_folds_notes_into_counts() {
    let mut r = resolved(SUMMARY_MODEL);
    let g = summary_graph(&mut r, &["P"], 0, 500);
    assert!(
        g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .all(|n| n["kind"] != "note")
    );
    assert_eq!(
        node(&g, "P")["noteCount"],
        1,
        "the doc on P folds into a count"
    );
    assert!(
        g["edges"]
            .as_array()
            .unwrap()
            .iter()
            .all(|e| e["kind"] != "note")
    );
}

#[test]
fn full_emission_carries_no_summary_fields() {
    let mut r = resolved(SUMMARY_MODEL);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    assert!(
        g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .all(|n| n.get("summary").is_none() && n.get("noteCount").is_none())
    );
    assert!(
        g["edges"]
            .as_array()
            .unwrap()
            .iter()
            .all(|e| e.get("count").is_none())
    );
    assert_eq!(
        g["nodes"].as_array().unwrap().len(),
        12,
        "P, Q, A, B, q, D, d1, d2, L + 3 notes"
    );
}

/// The full emission with the summary-only keys removed, for the
/// invariant that opening every container with unbounded budgets is
/// the full picture.
fn strip_summary(mut g: serde_json::Value) -> serde_json::Value {
    for n in g["nodes"].as_array_mut().unwrap() {
        n.as_object_mut().unwrap().remove("summary");
    }
    g
}

#[test]
fn summary_with_everything_open_is_the_full_emission() {
    let src = "package P {
        private import ScalarValues::*;
        doc /* on P */
        package Q { part def A; part def B :> A; part q : A; comment about A /* c2 */ }
        part def D :> Q::A { part d1 : Q::A; part d2 : Q::B; attribute mass : Real; }
        part def L;
        part x : D;
        dependency Dep from D to L;
        enum def E { a; b; }
        package Empty;
        comment about L /* c1 */
    }";
    let mut r = resolved(src);
    let full = sysmlv2_viz::graph(
        &mut r,
        None,
        &VizOptions::default().with_show_imported(true),
    )
    .unwrap();
    let open: Vec<ElementRef> = ["P", "P::Q", "P::D", "P::Empty", "P::E"]
        .iter()
        .map(|q| r.resolve_qualified(q).unwrap())
        .collect();
    let opts = VizOptions::default()
        .with_show_imported(true)
        .with_summary(Some(sysmlv2_viz::SummaryOptions {
            open,
            note_budget: usize::MAX,
            leaf_budget: usize::MAX,
            unbounded: Vec::new(),
        }));
    let all_open = strip_summary(sysmlv2_viz::graph(&mut r, None, &opts).unwrap());
    assert_eq!(all_open.to_string(), full.to_string());
}

#[test]
fn summary_open_owner_card_keeps_member_identity_and_bundles_only_hidden_ends() {
    let src = "package P {
        package Q { part def A; part def B :> A; }
        part def Base;
        part def D :> Base { part d1 : Q::A; part d2 : Q::B; }
        part x : D;
        dependency Dep from D to Base;
    }";
    let mut r = resolved(src);
    let open: Vec<ElementRef> = ["P", "P::D"]
        .iter()
        .map(|q| r.resolve_qualified(q).unwrap())
        .collect();
    let opts = VizOptions::default().with_summary(Some(sysmlv2_viz::SummaryOptions {
        open,
        note_budget: 200,
        leaf_budget: 500,
        unbounded: Vec::new(),
    }));
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let edges = g["edges"].as_array().unwrap();
    // The open owner card's members draw beside it, wired by composition edges without counts.
    assert!(
        g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|n| n["qname"] == "P::D::d1")
    );
    assert_eq!(
        edges
            .iter()
            .filter(|e| e["kind"] == "composition" && e.get("count").is_none())
            .count(),
        2
    );
    // Edges between drawn nodes keep their shape: the specialization's `rel`, the dependency's identity, x's typing.
    let spec = edges
        .iter()
        .find(|e| e["kind"] == "specialization")
        .unwrap();
    assert_eq!(spec["rel"], "subclassification");
    assert!(spec.get("count").is_none());
    let dep = edges.iter().find(|e| e["kind"] == "dependency").unwrap();
    assert!(dep.get("id").is_some() && dep.get("count").is_none());
    let x_typing = edges
        .iter()
        .filter(|e| e["kind"] == "typing" && e.get("count").is_none())
        .count();
    assert_eq!(x_typing, 1, "x : D between two drawn nodes");
    // d1 : Q::A and d2 : Q::B each reach the closed Q: two separate bundles (one per drawn source).
    let bundles: Vec<&serde_json::Value> = edges
        .iter()
        .filter(|e| e["kind"] == "typing" && e.get("count").is_some())
        .collect();
    assert_eq!(bundles.len(), 2);
    assert!(
        bundles
            .iter()
            .all(|b| b["count"] == 1 && b["target"] == node(&g, "P::Q")["id"])
    );
    assert_eq!(node(&g, "P::Q")["summary"]["edgesIn"], 2);
    assert_eq!(node(&g, "P::D")["summary"]["open"], true);
}

#[test]
fn summary_bundles_imports_dependencies_and_library_typings_from_hidden_elements() {
    let src = "package P {
        package Lib { part def T; }
        package C {
            private import Lib::*;
            part def U { part u : T; }
            part def V;
            dependency Need from V to Lib::T;
        }
        part def W;
        dependency Uses from W to Lib::T;
    }";
    let mut r = resolved(src);
    let open: Vec<ElementRef> = ["P"]
        .iter()
        .map(|q| r.resolve_qualified(q).unwrap())
        .collect();
    let opts = VizOptions::default()
        .with_show_imported(true)
        .with_summary(Some(sysmlv2_viz::SummaryOptions {
            open,
            note_budget: 200,
            leaf_budget: 500,
            unbounded: Vec::new(),
        }));
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let edges = g["edges"].as_array().unwrap();
    let c = node(&g, "P::C")["id"].clone();
    let lib = node(&g, "P::Lib")["id"].clone();
    let bundle = |kind: &str| {
        edges
            .iter()
            .find(|e| e["kind"] == kind && e["source"] == c && e["target"] == lib)
            .cloned()
    };
    // C itself is drawn and so is Lib: its import is an edge between drawn nodes and keeps its shape.
    let imp = edges
        .iter()
        .find(|e| e["kind"] == "import" && e["source"] == c && e["target"] == lib)
        .unwrap();
    assert!(imp.get("count").is_none() && imp["importKind"] == "namespace");
    assert_eq!(
        bundle("typing").unwrap()["count"],
        1,
        "u : T inside the hidden U"
    );
    let dep_bundle = bundle("dependency").unwrap();
    assert_eq!(dep_bundle["count"], 1);
    assert!(
        dep_bundle.get("id").is_none(),
        "a hidden dependency loses its identity"
    );
    // The drawn W's dependency to the closed Lib is a bundle too (its target stands in for T).
    let w = node(&g, "P::W")["id"].clone();
    let w_dep = edges
        .iter()
        .find(|e| e["kind"] == "dependency" && e["source"] == w)
        .unwrap();
    assert_eq!(w_dep["target"], lib);
    assert_eq!(w_dep["count"], 1);
    assert_eq!(
        node(&g, "P::C")["summary"]["edgesOut"],
        2,
        "the typing and the dependency from hidden elements"
    );
}

#[test]
fn summary_truncated_container_counts_and_interior_edges_vanish() {
    let src = "package P {
        part def Z;
        package Q { part def A; part q : A; comment about A /* c2 */ }
    }";
    let mut r = resolved(src);
    let open: Vec<ElementRef> = ["P"]
        .iter()
        .map(|q| r.resolve_qualified(q).unwrap())
        .collect();
    let opts = VizOptions::default().with_summary(Some(sysmlv2_viz::SummaryOptions {
        open,
        note_budget: 200,
        leaf_budget: 1,
        unbounded: Vec::new(),
    }));
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let p = &node(&g, "P")["summary"];
    assert_eq!(p["truncated"], 1);
    assert_eq!(
        p["containers"], 1,
        "the truncated Q is still counted as a container"
    );
    assert_eq!(p["leaves"], 1);
    assert_eq!(p["notes"], 1, "Q's note rolls into P");
    assert!(
        g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .all(|n| n["qname"] != "P::Q")
    );
    assert!(
        g["edges"]
            .as_array()
            .unwrap()
            .iter()
            .all(|e| e["kind"] == "note" || e.get("count").is_none()),
        "q : A is interior to P: no bundle"
    );
}

#[test]
fn summary_enumerations_and_empty_packages_are_leaves() {
    let src = "package P { enum def E { a; b; } enum e : E { part p : P::T; } part def T; package Empty; }";
    let mut r = resolved(src);
    let open: Vec<ElementRef> = ["P"]
        .iter()
        .map(|q| r.resolve_qualified(q).unwrap())
        .collect();
    let opts = VizOptions::default().with_summary(Some(sysmlv2_viz::SummaryOptions {
        open,
        note_budget: 200,
        leaf_budget: 500,
        unbounded: Vec::new(),
    }));
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let p = &node(&g, "P")["summary"];
    assert_eq!(p["containers"], 0);
    assert_eq!(p["leaves"], p["members"]);
    assert!(
        node(&g, "P::Empty").get("summary").is_none(),
        "an empty package is not an openable box"
    );
    assert!(node(&g, "P::E").get("summary").is_none());
    assert!(
        g["edges"]
            .as_array()
            .unwrap()
            .iter()
            .all(|e| e.get("count").is_none())
    );
}

/// The probe fixture behind the byte-identity goldens: every node kind
/// the tree emitter draws, values, notes, imports, inherited rows, a
/// library type, a dependency, an enumeration and an empty package.
const IDENTITY_FIXTURE: &str = "package P { private import ScalarValues::*; doc /* on P */ package Q { part def A; part def B :> A; part q : A; comment about A /* c2 */ } part def D :> Q::A { part d1 : Q::A; part d2 : Q::B; attribute mass : Real = 3; } part def L; part x : D; dependency Dep from D to L; enum def E { a; b; } package Empty; comment about L /* c1 */ }";

/// The full emission is byte-identical to the emitter before summary
/// mode existed (goldens captured from it), with every option that
/// touches the emission on, and with overlapping roots.
#[test]
fn full_emission_matches_pre_summary_goldens() {
    let mut r = resolved_named("a.sysml", IDENTITY_FIXTURE);
    let opts = VizOptions::default()
        .with_show_imported(true)
        .with_show_inherited(true)
        .with_show_lib(true);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap().to_string();
    assert_eq!(g, include_str!("golden/graph-full-options.json").trim_end());
    let roots: Vec<ElementRef> = ["P", "P::Q"]
        .iter()
        .map(|q| r.resolve_qualified(q).unwrap())
        .collect();
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default().with_roots(Some(roots)))
        .unwrap()
        .to_string();
    assert_eq!(
        g,
        include_str!("golden/graph-overlapping-roots.json").trim_end()
    );
}

#[test]
fn graph_rows_carry_their_nested_attribute_rows() {
    let mut r = resolved(
        "package P {
        part def Body {
            attribute mass : Real = 120;
            attribute dimension {
                attribute x : Real = 32;
                attribute y : Real = 140;
                attribute inner { attribute z : Real; }
            }
            attribute colour;
        }
    }",
    );
    let graph = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let body = graph["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["qname"] == "P::Body")
        .expect("Body");
    let rows = body["rows"].as_array().unwrap();
    let labels: Vec<_> = rows.iter().map(|r| r["label"].as_str().unwrap()).collect();
    assert_eq!(labels, ["mass = 120", "dimension", "colour"]);
    assert!(rows[0].get("rows").is_none(), "a leaf row carries no rows");
    let nested = rows[1]["rows"].as_array().expect("dimension's rows");
    let nested_labels: Vec<_> = nested
        .iter()
        .map(|r| r["label"].as_str().unwrap())
        .collect();
    assert_eq!(nested_labels, ["x = 32", "y = 140", "inner"]);
    assert_eq!(nested[0]["qname"], "P::Body::dimension::x");
    assert_eq!(nested[0]["section"], "attributes");
    let deeper = nested[2]["rows"].as_array().expect("inner's rows");
    assert_eq!(deeper[0]["qname"], "P::Body::dimension::inner::z");
    assert!(deeper[0].get("rows").is_none());
}

// ---------------------------------------------------------------------------
// Role members: a member introduced into its owner in a role of its own
// (subject, actor, objective, result, state action, end, …) is a row of
// the owner's card that says the role.
// ---------------------------------------------------------------------------

/// Every role a body can introduce a member in, beside a satisfaction,
/// an interface's port ends and a port's directed feature.
const BODY_MEMBERS: &str = include_str!("fixtures/body_members.sysml");

/// A state definition with every shape of state action: named, a
/// reference, a block, one that only says what it does (`exit send …`),
/// and empty ones; beside it, empty members of the other one-of roles.
const STATE_ACTIONS: &str = include_str!("fixtures/state_actions.sysml");

fn state_actions() -> ResolvedModel {
    resolved_named("state_actions.sysml", STATE_ACTIONS)
}

/// References that do not resolve in full (an unresolved name, a chain
/// cut short at `tank.drain`), one package per view under test; a test
/// scopes its diagram to its package. Each package owns its own `tank`,
/// so the chain is cut short in the owner's scope.
const UNRESOLVED_REFERENCES: &str = include_str!("fixtures/unresolved_references.sysml");

fn unresolved_references(package: &str) -> (ResolvedModel, ElementRef) {
    let mut r = resolved_named("unresolved_references.sysml", UNRESOLVED_REFERENCES);
    let root = r.resolve_qualified(package).expect("package resolves");
    (r, root)
}

fn body_members() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library loads");
    let unit = model.add_source("body_members.sysml".to_string(), BODY_MEMBERS);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&model)
}

/// A row's `[role, section, label, expr]`, `-` for an absent field.
fn row_shape(row: &serde_json::Value) -> [&str; 4] {
    [
        row["role"].as_str().unwrap_or("-"),
        row["section"].as_str().unwrap(),
        row["label"].as_str().unwrap(),
        row["expr"].as_str().unwrap_or("-"),
    ]
}

/// The shapes of a node's rows, in order.
fn row_shapes<'a>(g: &'a serde_json::Value, qname: &str) -> Vec<[&'a str; 4]> {
    node(g, qname)["rows"]
        .as_array()
        .unwrap()
        .iter()
        .map(row_shape)
        .collect()
}

/// Every row of a graph with the rows nested under it, depth first.
fn all_rows(g: &serde_json::Value) -> Vec<&serde_json::Value> {
    fn walk<'a>(rows: &'a serde_json::Value, out: &mut Vec<&'a serde_json::Value>) {
        for row in rows.as_array().into_iter().flatten() {
            out.push(row);
            walk(&row["rows"], out);
        }
    }
    let mut out = Vec::new();
    for n in g["nodes"].as_array().unwrap() {
        walk(&n["rows"], &mut out);
    }
    out
}

#[test]
fn graph_role_members_are_rows_that_say_their_role() {
    let mut r = body_members();
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    assert_eq!(
        row_shapes(&g, "BodyMembers::MassLimit"),
        [
            ["subject", "subject", "vehicle : Vehicle", "-"],
            ["actor", "actors", "operator : Driver", "-"],
            ["stakeholder", "stakeholders", "owner : Driver", "-"],
            ["-", "attributes", "in limit : Real", "-"],
            ["-", "attributes", "margin : Real", "-"],
            ["assume", "assume constraints", "fueled", "vehicle.mass > 0"],
            [
                "require",
                "require constraints",
                "underLimit",
                "vehicle.mass <= limit"
            ],
            ["frame", "frames", "worry : Safety", "-"],
        ]
    );
    assert_eq!(
        row_shapes(&g, "BodyMembers::Safety"),
        [
            ["subject", "subject", "v : Vehicle", "-"],
            ["stakeholder", "stakeholders", "driver : Driver", "-"],
        ]
    );
    assert_eq!(
        row_shapes(&g, "BodyMembers::massReq"),
        [["subject", "subject", "vehicle : Vehicle", "-"]]
    );
    // A body's result expression is a row of its own, spelled by its
    // expression; the return parameter is led by no direction.
    assert_eq!(
        row_shapes(&g, "BodyMembers::UnderLimit"),
        [
            ["-", "attributes", "in m : Real", "-"],
            ["-", "attributes", "in limit : Real", "-"],
            ["result", "result", "", "m <= limit"],
        ]
    );
    assert_eq!(
        row_shapes(&g, "BodyMembers::Total"),
        [
            ["-", "attributes", "in a : Real", "-"],
            ["-", "attributes", "in b : Real", "-"],
            ["return", "return", "sum : Real", "-"],
            ["result", "result", "", "a + b"],
        ]
    );
    // An objective with nothing but its doc is still the case's one: its keyword alone.
    assert_eq!(
        row_shapes(&g, "BodyMembers::Drive"),
        [
            ["subject", "subject", "vehicle : Vehicle", "-"],
            ["actor", "actors", "driver : Driver", "-"],
            ["objective", "objective", "", "-"],
            ["include", "includes", "park", "-"],
        ]
    );
    assert_eq!(
        row_shapes(&g, "BodyMembers::MassAnalysis"),
        [
            ["subject", "subject", "vehicle : Vehicle", "-"],
            ["objective", "objective", "massObjective", "-"],
            ["return", "return", "totalMass : Real", "-"],
            ["result", "result", "", "vehicle.mass"],
        ]
    );
    assert_eq!(
        row_shapes(&g, "BodyMembers::MassTest"),
        [
            ["subject", "subject", "vehicle : Vehicle", "-"],
            ["objective", "objective", "", "-"],
            ["return", "return", "verdict : VerdictKind", "-"],
        ]
    );
    assert_eq!(
        row_shapes(&g, "BodyMembers::Engine"),
        [
            ["entry", "state actions", "warm", "-"],
            ["do", "state actions", "refuel", "-"],
            ["exit", "state actions", "cool", "-"],
        ]
    );
    assert_eq!(
        row_shapes(&g, "BodyMembers::Mount"),
        [
            ["end", "ends", "car : Vehicle", "-"],
            ["end", "ends", "sensor : Sensor", "-"],
        ]
    );
    // A reference form names what it references.
    assert_eq!(
        row_shapes(&g, "BodyMembers::Ops"),
        [
            ["frame", "frames", "safety", "-"],
            ["stakeholder", "stakeholders", "driver : Driver", "-"],
        ]
    );
    // Role rows keep a row's identity and notation fields.
    let rows = node(&g, "BodyMembers::Mount")["rows"].as_array().unwrap();
    assert_eq!(rows[0]["qname"], "BodyMembers::Mount::car");
    assert_eq!(rows[0]["file"], "body_members.sysml");
    assert_eq!(rows[0]["line"], 42);
    assert_eq!(rows[0]["prefixes"], serde_json::json!(["end"]));
    let result = &node(&g, "BodyMembers::Total")["rows"][3];
    assert!(result["id"].is_string(), "{result}");
    assert_eq!(result["line"], 24);
    // No role row reads as a parameter row.
    for row in all_rows(&g) {
        if row.get("role").is_some() {
            let label = row["label"].as_str().unwrap();
            for direction in ["in ", "out ", "inout "] {
                assert!(!label.starts_with(direction), "{row}");
            }
            assert!(row.get("direction").is_none(), "{row}");
        }
    }
}

#[test]
fn graph_objective_rows_nest_their_own_role_members() {
    let mut r = body_members();
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let analysis = &node(&g, "BodyMembers::MassAnalysis")["rows"][1];
    assert_eq!(
        analysis["qname"],
        "BodyMembers::MassAnalysis::massObjective"
    );
    let nested: Vec<_> = analysis["rows"]
        .as_array()
        .expect("the objective's rows")
        .iter()
        .map(row_shape)
        .collect();
    // The require constraint carries its expression, not its result row.
    assert_eq!(
        nested,
        [["require", "require constraints", "", "vehicle.mass < 2000"]]
    );
    assert!(analysis["rows"][0].get("rows").is_none());
    let test = &node(&g, "BodyMembers::MassTest")["rows"][1];
    let nested: Vec<_> = test["rows"]
        .as_array()
        .expect("the objective's rows")
        .iter()
        .map(row_shape)
        .collect();
    assert_eq!(nested, [["verify", "verifies", "massReq", "-"]]);
}

#[test]
fn graph_role_members_draw_no_nodes_and_no_edges() {
    let mut r = body_members();
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let role_ids: Vec<&str> = all_rows(&g)
        .into_iter()
        .filter(|row| row.get("role").is_some())
        .map(|row| row["id"].as_str().unwrap())
        .collect();
    assert_eq!(role_ids.len(), 32, "{role_ids:?}");
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    for id in &role_ids {
        assert!(nodes.iter().all(|n| n["id"] != *id), "node {id}");
        assert!(
            edges
                .iter()
                .all(|e| e["source"] != *id && e["target"] != *id),
            "edge at {id}"
        );
    }
    // The named cards left: definitions (the conjugated port definition
    // among them), plain usages, states, and the interface's port ends;
    // the transition and the satisfaction draw unnamed.
    let mut drawn: Vec<&str> = nodes
        .iter()
        .filter(|n| n["kind"] != "note")
        .filter_map(|n| n["qname"].as_str())
        .collect();
    drawn.sort_unstable();
    let expected = [
        "BodyMembers",
        "BodyMembers::Driver",
        "BodyMembers::Drive",
        "BodyMembers::Engine",
        "BodyMembers::Engine::off",
        "BodyMembers::Engine::on",
        "BodyMembers::Fuel",
        "BodyMembers::FuelLine",
        "BodyMembers::FuelLine::dst",
        "BodyMembers::FuelLine::src",
        "BodyMembers::FuelPort",
        "BodyMembers::FuelPort::'~FuelPort'",
        "BodyMembers::Mount",
        "BodyMembers::MassAnalysis",
        "BodyMembers::MassLimit",
        "BodyMembers::MassLimit::sub",
        "BodyMembers::MassTest",
        "BodyMembers::MassTest::weigh",
        "BodyMembers::Ops",
        "BodyMembers::Safety",
        "BodyMembers::Sensor",
        "BodyMembers::Total",
        "BodyMembers::UnderLimit",
        "BodyMembers::Vehicle",
        "BodyMembers::car",
        "BodyMembers::massReq",
        "BodyMembers::park",
        "BodyMembers::refuel",
        "BodyMembers::safety",
    ];
    let mut expected = expected.to_vec();
    expected.sort_unstable();
    assert_eq!(drawn, expected);
    // No «keyword» edge from a role member: the `do refuel` perform edge
    // went with its node.
    let kinds: Vec<&str> = edges.iter().map(|e| e["kind"].as_str().unwrap()).collect();
    for kind in ["perform", "frame", "verify", "include"] {
        assert!(!kinds.contains(&kind), "{kind} edge in {kinds:?}");
    }
    // The doc of an objective that is no node attaches to nothing; the
    // requirement definition's own doc still does.
    let notes: Vec<&str> = nodes
        .iter()
        .filter(|n| n["kind"] == "note")
        .map(|n| n["label"].as_str().unwrap())
        .collect();
    assert_eq!(notes, ["The vehicle mass shall not exceed the limit."]);
}

#[test]
fn graph_satisfactions_and_port_ends_keep_their_nodes() {
    let mut r = body_members();
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    let has_edge = |kind: &str, s: &serde_json::Value, t: &serde_json::Value| {
        edges
            .iter()
            .any(|e| e["kind"] == kind && e["source"] == s["id"] && e["target"] == t["id"])
    };
    // `satisfy massReq by car;`: its own node, its subject no row.
    let car = node(&g, "BodyMembers::car");
    assert!(car["rows"].as_array().unwrap().is_empty(), "{car}");
    let satisfy = nodes
        .iter()
        .find(|n| n["metaclass"] == "SatisfyRequirementUsage")
        .expect("the satisfaction's node");
    assert_eq!(satisfy["label"], "(satisfy requirement)");
    assert!(satisfy["rows"].as_array().unwrap().is_empty(), "{satisfy}");
    assert!(has_edge("composition", car, satisfy));
    assert!(has_edge(
        "satisfy",
        satisfy,
        node(&g, "BodyMembers::massReq")
    ));
    // An interface's port ends stay port nodes with their `end` prefix.
    let line = node(&g, "BodyMembers::FuelLine");
    assert!(line["rows"].as_array().unwrap().is_empty(), "{line}");
    for (end, label) in [("src", "src : FuelPort"), ("dst", "dst : ~FuelPort")] {
        let port = node(&g, &format!("BodyMembers::FuelLine::{end}"));
        assert_eq!(port["label"], label);
        assert_eq!(port["stereo"], "port");
        assert_eq!(port["prefixes"], serde_json::json!(["end"]));
        assert!(has_edge("composition", line, port));
    }
}

#[test]
fn graph_port_directed_features_are_rows_with_their_direction() {
    let mut r = body_members();
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let rows = node(&g, "BodyMembers::FuelPort")["rows"]
        .as_array()
        .unwrap();
    assert_eq!(rows.len(), 1, "{rows:?}");
    let fuel = &rows[0];
    assert_eq!(fuel["qname"], "BodyMembers::FuelPort::fuel");
    assert_eq!(fuel["label"], "fuel : Fuel");
    assert_eq!(fuel["section"], "directed features");
    assert_eq!(fuel["direction"], "in");
    assert!(fuel.get("role").is_none(), "{fuel}");
    assert!(
        g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .all(|n| n["qname"] != "BodyMembers::FuelPort::fuel")
    );
    // Every direction, attributes included, on a port usage as on a port
    // definition; a nested port stays a port, and the directed features
    // of anything but a port keep their parameter rows.
    let mut r = resolved(
        "package P {
        part def Fluid;
        port def Inner;
        port def Valve {
            in item fluid : Fluid;
            out attribute pressure;
            inout part p;
            in port inner : Inner;
        }
        part def Pump { port v : Valve { out attribute rate; } }
        action def Act { in item fluid : Fluid; }
    }",
    );
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let valve: Vec<_> = node(&g, "P::Valve")["rows"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                row["section"].as_str().unwrap(),
                row["label"].as_str().unwrap(),
                row["direction"].as_str().unwrap(),
            )
        })
        .collect();
    assert_eq!(
        valve,
        [
            ("directed features", "fluid : Fluid", "in"),
            ("directed features", "pressure", "out"),
            ("directed features", "p", "inout"),
        ]
    );
    assert_eq!(node(&g, "P::Valve::inner")["stereo"], "port");
    let rate = &node(&g, "P::Pump::v")["rows"][0];
    assert_eq!(
        (&rate["section"], &rate["label"], &rate["direction"]),
        (
            &serde_json::json!("directed features"),
            &serde_json::json!("rate"),
            &serde_json::json!("out")
        )
    );
    // An action's parameter is no port feature.
    assert!(node(&g, "P::Act")["rows"].as_array().unwrap().is_empty());
    assert_eq!(node(&g, "P::Act::fluid")["stereo"], "item");
}

#[test]
fn graph_anonymous_state_actions_say_what_they_do() {
    let mut r = state_actions();
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    // `entry;` (the initial step a succession leaves) is the state's entry
    // action: a row with its role and no label.
    assert_eq!(
        row_shapes(&g, "S::Machine"),
        [["entry", "state actions", "", "-"]]
    );
    let entry = &node(&g, "S::Machine")["rows"][0];
    assert!(entry["id"].is_string(), "{entry}");
    assert_eq!(entry["line"], 8);
    // No state action draws as a node: the only action node is the
    // package's own `action refuel;`.
    let actions: Vec<&serde_json::Value> = g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|n| n["stereo"] == "action" || n["stereo"] == "send action")
        .collect();
    assert_eq!(actions.len(), 1, "{g}");
    assert_eq!(actions[0]["qname"], "S::refuel");
    assert_eq!(
        row_shapes(&g, "S::Machine::busy"),
        [
            ["do", "state actions", "sweep : Chore; polish", "-"],
            ["exit", "state actions", "send action", "-"],
        ]
    );
    assert_eq!(
        row_shapes(&g, "S::Machine::waiting"),
        [
            ["do", "state actions", "", "-"],
            ["exit", "state actions", "", "-"],
        ]
    );
}

/// The state view draws a state's `entry` / `do` / `exit` actions as the
/// tree view does: rows with the subaction's identity, its `role` and the
/// "state actions" section, labelled without the kind (a host reads the
/// role), an anonymous one by what it does, an empty `entry;` by its role
/// alone.
#[test]
fn graph_state_view_state_actions_are_role_rows() {
    let mut r = state_actions();
    let state =
        sysmlv2_viz::graph(&mut r, None, &VizOptions::default().with_view(View::State)).unwrap();
    assert_eq!(
        row_shapes(&state, "S::Machine::idle"),
        [
            ["entry", "state actions", "warm", "-"],
            ["do", "state actions", "refuel", "-"],
            ["exit", "state actions", "bye : Log", "-"],
        ]
    );
    assert_eq!(
        row_shapes(&state, "S::Machine::busy"),
        [
            ["do", "state actions", "sweep : Chore; polish", "-"],
            ["exit", "state actions", "send action", "-"],
        ]
    );
    let warm = &node(&state, "S::Machine::idle")["rows"][0];
    assert_eq!(warm["qname"], "S::Machine::idle::warm");
    assert_eq!(warm["line"], 10);
    assert!(warm["id"].is_string(), "{warm}");
    // Row for row, the tree view's state actions.
    let tree = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    for qname in [
        "S::Machine",
        "S::Machine::idle",
        "S::Machine::busy",
        "S::Machine::waiting",
    ] {
        let actions: Vec<&serde_json::Value> = node(&tree, qname)["rows"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|row| row["section"] == "state actions")
            .collect();
        let rows: Vec<&serde_json::Value> = node(&state, qname)["rows"]
            .as_array()
            .unwrap()
            .iter()
            .collect();
        assert_eq!(rows, actions, "{qname}");
    }
}

/// The PlantUML state view labels its `entry / …`, `do / …` and `exit /
/// …` lines as the graph's state-action rows are: an anonymous action
/// that only says what it does reads as its kind (`exit send …` → `exit
/// / send action`), where it drew no line; a block still lists its
/// steps, and an empty one (`do;`) still draws none.
#[test]
fn state_view_anonymous_state_actions_read_as_their_kind() {
    let mut r = state_actions();
    let out = plantuml(&mut r, None, &view_opts(View::State));
    let busy = out
        .lines()
        .find_map(|line| line.trim().strip_prefix("state \"busy\" as "))
        .and_then(|rest| rest.split(' ').next())
        .expect("busy state");
    assert!(
        out.contains(&format!("{busy} : do / sweep : Chore; polish\n")),
        "{out}"
    );
    assert!(
        out.contains(&format!("{busy} : exit / send action\n")),
        "{out}"
    );
    let waiting = out
        .lines()
        .find_map(|line| line.trim().strip_prefix("state \"waiting\" as "))
        .and_then(|rest| rest.split(' ').next())
        .expect("waiting state");
    assert!(!out.contains(&format!("{waiting} : ")), "{out}");
}

/// An owner has one member at most of some roles (a subject, an
/// objective, a return, a result, an entry, do or exit action), and an
/// empty one is still the one: the graph draws its keyword alone, so a
/// host reading the owner's rows sees that it has one. An empty member of
/// a role an owner may have many of draws nothing, and the PlantUML tree
/// draws neither.
#[test]
fn graph_empty_one_of_role_members_keep_their_rows() {
    let mut r = state_actions();
    let tree = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    assert_eq!(
        row_shapes(&tree, "S::Idle"),
        [
            ["do", "state actions", "", "-"],
            ["exit", "state actions", "", "-"],
        ]
    );
    assert_eq!(
        row_shapes(&tree, "S::Bare"),
        [["subject", "subject", "", "-"]]
    );
    // The state view draws the same rows, beside the initial pseudostate
    // the entry's succession leaves from.
    let state =
        sysmlv2_viz::graph(&mut r, None, &VizOptions::default().with_view(View::State)).unwrap();
    assert_eq!(
        node(&state, "S::Idle")["rows"],
        node(&tree, "S::Idle")["rows"]
    );
    assert!(
        state["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .any(|n| n["kind"] == "pseudo" && n["stereo"] == "initial"),
        "{state}"
    );
    // PlantUML leaves them out, in both views: no keyword stands alone
    // as a tree line, and no state line ends at its kind.
    let out = plantuml(&mut r, None, &VizOptions::default());
    for line in out.lines().map(str::trim) {
        assert!(
            !matches!(line, "entry" | "do" | "exit" | "subject" | "actor"),
            "{out}"
        );
    }
    let out = plantuml(&mut r, None, &view_opts(View::State));
    for line in out.lines().map(str::trim_end) {
        assert!(
            !(line.ends_with(": entry") || line.ends_with(": do") || line.ends_with(": exit")),
            "{out}"
        );
    }
}

#[test]
fn inherited_role_rows_yield_to_an_own_member_of_the_role() {
    let src = "package I {
        calc def Total { in attribute a; in attribute b; return attribute sum; a + b }
        calc def Product :> Total { a * b }
        requirement def R { subject s; require constraint c { true } }
        requirement def R2 :> R { subject t; }
    }";
    let mut r = resolved(src);
    let opts = VizOptions::default().with_show_inherited(true);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let shapes = |qname: &str| -> Vec<(String, bool)> {
        node(&g, qname)["rows"]
            .as_array()
            .unwrap()
            .iter()
            .map(|row| {
                let [role, _, label, expr] = row_shape(row);
                (format!("{role} {label} {expr}"), row["inherited"] == true)
            })
            .collect()
    };
    assert_eq!(
        shapes("I::Product"),
        [
            ("result  a * b".to_string(), false),
            ("- in a -".to_string(), true),
            ("- in b -".to_string(), true),
            ("return sum -".to_string(), true),
        ]
    );
    assert_eq!(
        shapes("I::R2"),
        [
            ("subject t -".to_string(), false),
            ("require c true".to_string(), true),
        ]
    );
    let out = plantuml(&mut r, None, &opts);
    assert!(
        out.contains("    a * b\n    ^a\n    ^b\n    ^return sum\n"),
        "{out}"
    );
    assert!(
        out.contains("    subject t\n    ^require c { true }\n"),
        "{out}"
    );
}

#[test]
fn tree_role_members_are_keyword_lines() {
    let mut r = body_members();
    let out = plantuml(&mut r, None, &VizOptions::default());
    for block in [
        "<<requirement def>> {
    subject vehicle : Vehicle
    actor operator : Driver
    stakeholder owner : Driver
    limit : Real
    margin : Real
    assume fueled { vehicle.mass > 0 }
    require underLimit { vehicle.mass <= limit }
    frame worry : Safety
  }",
        "<<port def>> {
    in fuel : Fuel
  }",
        "<<constraint def>> {
    m : Real
    limit : Real
    m <= limit
  }",
        "<<calculation def>> {
    a : Real
    b : Real
    return sum : Real
    a + b
  }",
        "<<use case def>> {
    subject vehicle : Vehicle
    actor driver : Driver
    objective
    include park
  }",
        "<<analysis case def>> {
    subject vehicle : Vehicle
    objective massObjective { require { vehicle.mass < 2000 } }
    return totalMass : Real
    vehicle.mass
  }",
        "<<verification case def>> {
    subject vehicle : Vehicle
    objective { verify massReq }
    return verdict : VerdictKind
  }",
        "<<state def>> {
    entry warm
    do refuel
    exit cool
  }",
        "<<connection def>> {
    end car : Vehicle
    end sensor : Sensor
  }",
        "<<viewpoint def>> {
    frame safety
    stakeholder driver : Driver
  }",
    ] {
        assert!(out.contains(block), "{block}\nnot in\n{out}");
    }
    for gone in [
        "<<perform action>>",
        "<<include use case>>",
        "\"operator : Driver\"",
        "\"worry : Safety\"",
        "\"fuel : Fuel\"",
        "\"(requirement)\"",
    ] {
        assert!(!out.contains(gone), "{gone} in\n{out}");
    }
    // The satisfaction and the interface's port ends keep their nodes.
    assert!(out.contains("\"(satisfy requirement)\""), "{out}");
    assert!(out.contains("\"src : FuelPort\""), "{out}");
    // Every role row of the graph has its line.
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    for row in all_rows(&g) {
        let (Some(role), Some(label)) = (row["role"].as_str(), row["label"].as_str()) else {
            continue;
        };
        if !label.is_empty() {
            assert!(out.contains(&format!("{role} {label}")), "{row}");
        }
    }
}

#[test]
fn graph_role_references_name_what_they_reference() {
    let mut r = resolved(
        "package U {
        use case park;
        constraint fueled;
        constraint dry;
        concern safety;
        requirement massReq;
        action refuel;
        use case def Drive { include park[0..*]; }
        requirement def Limit { assume fueled; require dry; frame safety; }
        verification def Test { objective { verify massReq; } }
        state def Engine { do refuel; }
    }",
    );
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    assert_eq!(
        row_shapes(&g, "U::Drive"),
        [["include", "includes", "park [0..*]", "-"]]
    );
    // A reference has no expression of its own.
    assert_eq!(
        row_shapes(&g, "U::Limit"),
        [
            ["assume", "assume constraints", "fueled", "-"],
            ["require", "require constraints", "dry", "-"],
            ["frame", "frames", "safety", "-"],
        ]
    );
    let objective = &node(&g, "U::Test")["rows"][0];
    assert_eq!(row_shape(objective), ["objective", "objective", "", "-"]);
    assert_eq!(
        row_shape(&objective["rows"][0]),
        ["verify", "verifies", "massReq", "-"]
    );
    assert_eq!(
        row_shapes(&g, "U::Engine"),
        [["do", "state actions", "refuel", "-"]]
    );
    let out = plantuml(&mut r, None, &VizOptions::default());
    for line in [
        "    include park [0..*]\n",
        "    assume fueled\n",
        "    require dry\n",
        "    frame safety\n",
        "    objective { verify massReq }\n",
        "    do refuel\n",
    ] {
        assert!(out.contains(line), "{line:?} not in\n{out}");
    }
}

/// A role member whose reference does not resolve in full reads as
/// written, in both views and in the PlantUML tree, where it used to
/// draw nothing (an unresolved name) or the chain's resolved prefix
/// (`tank` for `tank.drain`).
#[test]
fn graph_unresolved_role_references_read_as_written() {
    let (mut r, root) = unresolved_references("U");
    let g = sysmlv2_viz::graph(&mut r, Some(root), &VizOptions::default()).unwrap();
    let actions = [
        ["entry", "state actions", "provide power", "-"],
        ["do", "state actions", "tank.drain", "-"],
        ["exit", "state actions", "Ops::park", "-"],
    ];
    assert_eq!(row_shapes(&g, "U::Engine"), actions);
    assert_eq!(
        row_shapes(&g, "U::Limit"),
        [["require", "require constraints", "mass limit", "-"]]
    );
    let opts = VizOptions::default().with_view(View::State);
    let g = sysmlv2_viz::graph(&mut r, Some(root), &opts).unwrap();
    assert_eq!(row_shapes(&g, "U::Engine"), actions);
    let out = plantuml(&mut r, Some(root), &VizOptions::default());
    for line in [
        "    entry provide power\n",
        "    do tank.drain\n",
        "    exit Ops::park\n",
        "    require mass limit\n",
    ] {
        assert!(out.contains(line), "{line:?} not in\n{out}");
    }
}

/// A binding to a feature that has no value to give reads as written
/// (`subject = result`, `a = vv.m`), where it used to read as the name
/// alone or, for an anonymous subject, not at all; a binding that
/// evaluates still reads as its value.
#[test]
fn graph_reference_bindings_read_as_written() {
    let src = "package B {
        part def V { attribute m; }
        part vv : V;
        requirement def Obj { subject s : V; }
        analysis def Case {
            subject v : V;
            objective obj : Obj { subject = result; }
            v.m
        }
        analysis def Plan {
            subject v : V;
            analysis c : Case { subject = v; }
        }
        enum def Color { red; green; }
        part ctx {
            analysis plan : Plan { subject v = vv; }
            attribute a = vv.m;
            attribute n = 3;
            attribute k = n;
            attribute color : Color = Color::red;
            attribute q = 'no such calc'(n);
            out attribute :>> missing = n2;
            attribute n2;
        }
    }";
    let mut r = resolved(src);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let objective = &node(&g, "B::Case")["rows"][1];
    assert_eq!(objective["label"], "obj : Obj");
    // The anonymous subject's label leads with the space a host splits
    // the value off at.
    assert_eq!(
        row_shape(&objective["rows"][0]),
        ["subject", "subject", " = result", "-"]
    );
    assert_eq!(
        row_shapes(&g, "B::Plan::c"),
        [["subject", "subject", " = v", "-"]]
    );
    assert_eq!(
        row_shapes(&g, "B::ctx::plan"),
        [["subject", "subject", "v = vv", "-"]]
    );
    assert_eq!(
        row_shapes(&g, "B::ctx"),
        [
            ["-", "attributes", "a = vv.m", "-"],
            ["-", "attributes", "n = 3", "-"],
            ["-", "attributes", "k = 3", "-"],
            ["-", "attributes", "color : Color = red", "-"],
            ["-", "attributes", "q", "-"],
            // a nameless row's direction and value, one space apart
            ["-", "attributes", "out = n2", "-"],
            ["-", "attributes", "n2", "-"],
        ]
    );
    let out = plantuml(&mut r, None, &VizOptions::default());
    for line in [
        "    objective obj : Obj { subject = result }\n",
        "    subject = v\n",
        "    subject v = vv\n",
        "    a = vv.m\n",
        "    k = 3\n",
    ] {
        assert!(out.contains(line), "{line:?} not in\n{out}");
    }
    // Values off: no binding either.
    let quiet = VizOptions::default().with_show_values(false);
    let g = sysmlv2_viz::graph(&mut r, None, &quiet).unwrap();
    assert_eq!(
        row_shapes(&g, "B::ctx::plan"),
        [["subject", "subject", "v", "-"]]
    );
}

/// The succession of a state's entry transition (`entry; then idle;`)
/// draws no node in the structure tree, in the graph or in PlantUML; the
/// state view still draws it as the edge from the initial pseudostate. A
/// succession written as one (`succession first a then b;`) and an action
/// flow's `then` still draw.
#[test]
fn tree_draws_no_node_for_an_entry_transition() {
    let src = "package T {
        action a;
        action b;
        succession first a then b;
        state def Boot {
            entry; then idle;
            state idle;
        }
        state def Warm {
            entry warm; then idle;
            action warm;
            state idle;
        }
        action def Flow {
            first start;
            then action x;
        }
    }";
    let mut r = resolved(src);
    let g = sysmlv2_viz::graph(&mut r, None, &VizOptions::default()).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    // The package's own succession and the action flow's `then` draw;
    // the two entry transitions' successions do not.
    let successions: Vec<&serde_json::Value> = nodes
        .iter()
        .filter(|n| n["metaclass"] == "SuccessionAsUsage")
        .collect();
    assert_eq!(successions.len(), 2, "{g}");
    let flow = &node(&g, "T::Flow")["id"];
    assert!(
        successions.iter().any(|s| edges
            .iter()
            .any(|e| e["source"] == *flow && e["target"] == s["id"])),
        "{g}"
    );
    for (state, members) in [
        ("T::Boot", &["T::Boot::idle"][..]),
        ("T::Warm", &["T::Warm::warm", "T::Warm::idle"]),
    ] {
        let id = &node(&g, state)["id"];
        let targets: Vec<&serde_json::Value> = edges
            .iter()
            .filter(|e| e["source"] == *id)
            .map(|e| &e["target"])
            .collect();
        let expected: Vec<&serde_json::Value> =
            members.iter().map(|m| &node(&g, m)["id"]).collect();
        assert_eq!(targets, expected, "{state}");
    }
    let out = plantuml(&mut r, None, &VizOptions::default());
    assert_eq!(out.matches("<<succession as>>").count(), 2, "{out}");
    let opts = VizOptions::default().with_view(View::State);
    let g = sysmlv2_viz::graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let initials = nodes.iter().filter(|n| n["kind"] == "pseudo").count();
    assert_eq!(initials, 2, "{g}");
}

/// The state view reads an unresolved state action, transition effect
/// or `exhibit` as written, its names unquoted: `do 'provide power';`
/// draws `do / provide power` where it drew no line, a chain cut short
/// reads whole (`do / tank.drain`, not `do / tank`), and `exhibit 'car
/// states';` is no longer `(exhibit state)`.
#[test]
fn state_view_unresolved_references_read_as_written() {
    let (mut r, root) = unresolved_references("U");
    let out = plantuml(&mut r, Some(root), &view_opts(View::State));
    let expected = "@startuml
state \"Engine\" as n1 <<state def>> {
  state \"on\" as n2 <<state>>
  state \"off\" as n3 <<state>>
  n2 --> n3 : Go / shut down
  n3 --> n2 : Go / tank.fill
}
n1 : entry / provide power
n1 : do / tank.drain
n1 : exit / Ops::park
state \"car states\" as n4 <<exhibit state>>
@enduml
";
    assert_eq!(out, expected);
    let opts = VizOptions::default().with_view(View::State);
    let g = sysmlv2_viz::graph(&mut r, Some(root), &opts).unwrap();
    let labels: Vec<&str> = g["edges"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|e| e["label"].as_str())
        .collect();
    assert_eq!(labels, ["Go / shut down", "Go / tank.fill"], "{g}");
    let exhibit = g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .find(|n| n["metaclass"] == "ExhibitStateUsage")
        .expect("exhibit node");
    assert_eq!(exhibit["label"], "car states");
}

/// The action view labels an anonymous `perform` by what it performs as
/// written when that did not resolve in full, where it drew `(perform
/// action)` (an unresolved name) or the chain's resolved prefix (`tank`
/// for `tank.drain`).
#[test]
fn action_view_unresolved_performs_read_as_written() {
    let (mut r, root) = unresolved_references("A");
    let out = plantuml(&mut r, Some(root), &view_opts(View::Action));
    let expected = "@startuml
state \"fill\" as n1 <<action>>
state \"Run\" as n2 <<action def>> {
  state \"warm up\" as n3 <<perform action>>
  state \"tank.drain\" as n4 <<perform action>>
  state \"tank.fill\" as n5 <<perform action>>
}
@enduml
";
    assert_eq!(out, expected);
    let opts = VizOptions::default().with_view(View::Action);
    let g = sysmlv2_viz::graph(&mut r, Some(root), &opts).unwrap();
    let mut labels: Vec<&str> = g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|n| n["metaclass"] == "PerformActionUsage")
        .map(|n| n["label"].as_str().unwrap())
        .collect();
    labels.sort_unstable();
    assert_eq!(labels, ["tank.drain", "tank.fill", "warm up"], "{g}");
}

/// A `perform`, `exhibit` or `include` whose chain is cut short at an
/// unresolved link draws no «keyword» edge to the chain's resolved
/// prefix, in the graph, the mixed view or the case view; a resolved
/// chain still does. The case view draws such an include, as it draws
/// one naming nothing, as a node of its own, labelled as written.
#[test]
fn reference_edges_skip_a_chain_cut_short() {
    let (mut r, root) = unresolved_references("E");
    let g = sysmlv2_viz::graph(&mut r, Some(root), &VizOptions::default()).unwrap();
    let ids: HashMap<&str, &str> = g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter_map(|n| Some((n["qname"].as_str()?, n["id"].as_str()?)))
        .collect();
    let edges: Vec<(&str, &str)> = g["edges"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|e| ["perform", "exhibit", "include"].contains(&e["kind"].as_str().unwrap()))
        .map(|e| (e["kind"].as_str().unwrap(), e["target"].as_str().unwrap()))
        .collect();
    assert_eq!(edges, [("perform", ids["E::Tank::fill"])], "{g}");
    let out = plantuml(&mut r, Some(root), &view_opts(View::Mixed));
    assert_eq!(out.matches(" : «perform»\n").count(), 1, "{out}");
    assert!(!out.contains("«exhibit»"), "{out}");
    assert!(!out.contains("«include»"), "{out}");
    let out = plantuml(&mut r, Some(root), &view_opts(View::Case));
    assert!(!out.contains("«include»"), "{out}");
    for line in [
        "usecase \"add fuel\" as n3 <<include use case>>\n",
        "usecase \"trip.missing\" as n4 <<include use case>>\n",
    ] {
        assert!(out.contains(line), "{line:?} not in\n{out}");
    }
}

/// An anonymous `perform`, `exhibit`, `satisfy` or `event` drawn as a
/// node of its own, and an anonymous part that references (`::>`), reads
/// as written when its reference does not resolve in full, in the graph
/// (structure tree and interconnection), the PlantUML tree and the
/// mixed view: no «keyword» edge says what it references. A resolved
/// reference reads as before, and so does a connector's end, resolved
/// or not.
#[test]
fn unresolved_reference_nodes_read_as_written() {
    let (mut r, root) = unresolved_references("N");
    // The members of the last `part car`, the one in this package.
    let car_from = UNRESOLVED_REFERENCES
        .lines()
        .enumerate()
        .filter(|(_, line)| line.contains("part car {"))
        .last()
        .expect("part car")
        .0 as u64
        + 1;
    let labels = |g: &serde_json::Value, metaclass: &str| {
        let mut labels: Vec<String> = g["nodes"]
            .as_array()
            .unwrap()
            .iter()
            .filter(|n| n["metaclass"] == metaclass && n["inherited"].is_null())
            .filter(|n| n["line"].as_u64().is_some_and(|line| line > car_from))
            .map(|n| n["label"].as_str().unwrap().to_string())
            .collect();
        labels.sort_unstable();
        labels
    };
    let g = sysmlv2_viz::graph(&mut r, Some(root), &VizOptions::default()).unwrap();
    for (metaclass, expected) in [
        (
            "PerformActionUsage",
            &["(perform action)", "cool down [2]", "tank.drain", "warm up"][..],
        ),
        ("ExhibitStateUsage", &["some state"]),
        (
            "SatisfyRequirementUsage",
            &["(satisfy requirement)", "missing spec"],
        ),
        ("EventOccurrenceUsage", &["some event"]),
        ("PartUsage", &["(part)", "spare tank"]),
    ] {
        assert_eq!(labels(&g, metaclass), expected, "{g}");
    }
    let ends: Vec<&str> = g["nodes"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|n| n["metaclass"] == "PortUsage" && n["qname"].is_null())
        .map(|n| n["label"].as_str().unwrap())
        .collect();
    assert_eq!(ends, ["(port)", "(port)"], "{g}");
    let g = sysmlv2_viz::graph(&mut r, Some(root), &view_opts(View::Interconnection)).unwrap();
    assert_eq!(labels(&g, "PartUsage"), ["(part)", "spare tank"], "{g}");
    let out = plantuml(&mut r, Some(root), &VizOptions::default());
    for line in [
        "class \"(perform action)\" as n13 <<perform action>>\n",
        "class \"tank.drain\" as n14 <<perform action>>\n",
        "class \"warm up\" as n15 <<perform action>>\n",
        "class \"cool down [2]\" as n16 <<perform action>>\n",
        "class \"some state\" as n17 <<exhibit state>>\n",
        "class \"(satisfy requirement)\" as n18 <<satisfy requirement>>\n",
        "class \"missing spec\" as n19 <<satisfy requirement>>\n",
        "class \"some event\" as n20 <<event occurrence>>\n",
        "class \"(part)\" as n21 <<part>>\n",
        "class \"spare tank\" as n22 <<part>>\n",
    ] {
        assert!(out.contains(line), "{line:?} not in\n{out}");
    }
    assert_eq!(out.matches("class \"(port)\"").count(), 2, "{out}");
    let out = plantuml(&mut r, Some(root), &view_opts(View::Mixed));
    for label in [
        "(perform action)",
        "tank.drain",
        "warm up",
        "cool down [2]",
        "some state",
        "(satisfy requirement)",
        "missing spec",
        "some event",
        "spare tank",
    ] {
        assert!(
            out.contains(&format!("rectangle \"{label}\" as ")),
            "{label:?} not in\n{out}"
        );
    }
    let out = plantuml(&mut r, Some(root), &view_opts(View::Interconnection));
    assert!(out.contains("rectangle \"spare tank\" as "), "{out}");
}
