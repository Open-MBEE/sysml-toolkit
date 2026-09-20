use sysmlv2_model::{json::ResolvedModel, model::Model};
use sysmlv2_viz::{View, VizOptions, graph, plantuml};

fn resolved(src: &str) -> ResolvedModel {
    let mut m = Model::new();
    let unit = m.add_source("endpoints.sysml", src);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    ResolvedModel::build(&m)
}

const INTERFACE: &str = "item def Item1; item def Item2;
port def Pa { out item i1Out : Item1; in item i2In : Item2; }
interface def Interface2 {
    end supplierP : Pa; end consumerP : ~Pa;
    flow supplierP.i1Out to consumerP.i1Out;
    flow consumerP.i2In to supplierP.i2In;
}";

#[test]
fn interface_flow_paths_retain_distinct_port_occurrences() {
    let opts = VizOptions::default().with_view(View::Interconnection);
    for scoped in [false, true] {
        let mut r = resolved(INTERFACE);
        let root = if scoped {
            r.resolve_qualified("Interface2")
        } else {
            None
        };
        let g = graph(&mut r, root, &opts).unwrap();
        let nodes = g["nodes"].as_array().unwrap();
        let id = |name| nodes.iter().find(|n| n["qname"] == name).unwrap()["id"].clone();
        let edges = g["edges"].as_array().unwrap();
        assert_eq!(edges.len(), 2);
        for (edge, (src, tgt, sp, tp)) in edges.iter().zip([
            (
                "Interface2::supplierP",
                "Interface2::consumerP",
                "supplierP.i1Out",
                "consumerP.i1Out",
            ),
            (
                "Interface2::consumerP",
                "Interface2::supplierP",
                "consumerP.i2In",
                "supplierP.i2In",
            ),
        ]) {
            assert_eq!(edge["source"], id(src));
            assert_eq!(edge["target"], id(tgt));
            assert_eq!(edge["sourcePath"], sp);
            assert_eq!(edge["targetPath"], tp);
            assert_eq!(edge["directed"], true);
            let e = r.element_by_id(edge["id"].as_str().unwrap()).unwrap();
            assert_eq!(r.element_type(e), "FlowUsage");
            assert_eq!(r.declaration_position(e).unwrap().0, "endpoints.sysml");
        }
        let uml = plantuml(&mut r, root, &opts);
        assert!(
            uml.contains("\"supplierP.i1Out\" --> \"consumerP.i1Out\""),
            "{uml}"
        );
        assert!(
            uml.contains("\"consumerP.i2In\" --> \"supplierP.i2In\""),
            "{uml}"
        );
    }
}

#[test]
fn inherited_ports_keep_usage_context_and_incomplete_paths_do_not_fabricate_edges() {
    let mut r = resolved(
        "port def P { item value; }
        part def Device { port p : P; }
        part a : Device; part b : Device;
        flow a.p.value to b.p.value;
        flow a.p.missing to b.p.value;
        connect (a.p, missing, b.p);",
    );
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    assert_eq!(edges.len(), 1, "{g}");
    let edge = &edges[0];
    for (side, owner) in [("source", "a"), ("target", "b")] {
        let port = nodes.iter().find(|n| n["id"] == edge[side]).unwrap();
        let parent = nodes.iter().find(|n| n["id"] == port["parent"]).unwrap();
        assert_eq!(parent["qname"], owner);
        assert_eq!(port["qname"], "Device::p");
    }
    let uml = plantuml(&mut r, None, &opts);
    assert_eq!(
        uml.lines().filter(|l| l.contains(" --> ")).count(),
        1,
        "{uml}"
    );
}

#[test]
fn performed_action_succession_uses_each_transparent_body() {
    let src = "part def PartDef2;
        part part2 : PartDef2 { perform action action2; then perform action action3; }
        part separate { perform action unrelated; }
        part third { then perform action initialStep; }
        part fourth { then perform action initialStep; }";
    let mut r = resolved(src);
    let opts = VizOptions::default().with_view(View::Action);
    let g = graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let id = |name| nodes.iter().find(|n| n["qname"] == name).unwrap()["id"].clone();
    let edges = g["edges"].as_array().unwrap();
    assert_eq!(edges.len(), 3, "{g}");
    let edge = edges
        .iter()
        .find(|e| e["target"] == id("part2::action3"))
        .unwrap();
    assert_eq!(edge["source"], id("part2::action2"));
    assert_eq!(edge["kind"], "succession");
    assert!(r.element_by_id(edge["id"].as_str().unwrap()).is_some());
    let initial = edges
        .iter()
        .find(|e| e["target"] == id("third::initialStep"))
        .unwrap();
    assert!(
        nodes
            .iter()
            .any(|n| n["id"] == initial["source"] && n["kind"] == "pseudo")
    );
    let other = edges
        .iter()
        .find(|e| e["target"] == id("fourth::initialStep"))
        .unwrap();
    assert_ne!(
        initial["source"], other["source"],
        "transparent bodies retain separate initial nodes"
    );
    let uml = plantuml(&mut r, None, &opts);
    assert_eq!(
        uml.lines().filter(|l| l.contains(" --> ")).count(),
        3,
        "{uml}"
    );
}

#[test]
fn native_action_anchors_preserve_fanout_initial_reset_and_unresolved_sources() {
    let mut r = resolved(
        "action def A {
        action a; then b; action b;
        first start; then fork; then a; then b;
        join junction; then action wrap;
        first missing; then wrap;
        first missing then a;
    }",
    );
    let opts = VizOptions::default().with_view(View::Action);
    let g = graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let id = |label| nodes.iter().find(|n| n["label"] == label).unwrap()["id"].clone();
    let edges = g["edges"].as_array().unwrap();
    assert_eq!(edges.len(), 5, "{g}");
    for (s, t) in [
        ("a", "b"),
        ("(fork)", "a"),
        ("(fork)", "b"),
        ("junction", "wrap"),
    ] {
        assert!(
            edges
                .iter()
                .any(|e| e["source"] == id(s) && e["target"] == id(t)),
            "{s} -> {t}: {g}"
        );
    }
    assert!(edges.iter().any(|e| {
        e["target"] == id("(fork)")
            && nodes
                .iter()
                .any(|n| n["id"] == e["source"] && n["kind"] == "pseudo")
    }));
    let uml = plantuml(&mut r, None, &opts);
    assert_eq!(
        uml.lines().filter(|l| l.contains(" --> ")).count(),
        5,
        "{uml}"
    );
}

#[test]
fn owned_nested_ports_still_resolve_to_the_deepest_drawn_node() {
    let mut r = resolved(
        "part outer { part inner { port p; } } part peer { port q; }
        connect outer.inner.p to peer.q;",
    );
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let edges = g["edges"].as_array().unwrap();
    assert_eq!(edges.len(), 1);
    for (side, qname) in [("source", "outer::inner::p"), ("target", "peer::q")] {
        assert!(
            nodes
                .iter()
                .any(|n| n["qname"] == qname && n["id"] == edges[0][side])
        );
    }
    assert!(edges[0]["sourcePath"].is_null());
    assert!(edges[0]["targetPath"].is_null());
}

#[test]
fn transitively_inherited_ports_render_once_and_redefinitions_shadow() {
    let mut r = resolved(
        "port def P;
        part def Base { port p : P; }
        part def Mid :> Base;
        part def Leaf :> Mid;
        part x : Leaf;
        part z : Leaf { port :>> p; }",
    );
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let ports_under = |owner: &str| -> Vec<String> {
        let parent = nodes.iter().find(|n| n["qname"] == owner).unwrap();
        nodes
            .iter()
            .filter(|n| n["parent"] == parent["id"] && n["kind"] == "port")
            .map(|n| n["qname"].as_str().unwrap_or("").to_string())
            .collect()
    };
    // Two levels up the definition hierarchy, one hop through the typing.
    assert_eq!(ports_under("x"), ["Base::p"], "{g}");
    // The owned redefinition shadows the inherited port: one node, not two.
    assert_eq!(ports_under("z").len(), 1, "{g}");
    assert_ne!(ports_under("z"), ["Base::p"], "{g}");
}

#[test]
fn library_owned_ports_stay_out_of_diagrams() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut m = Model::new();
    m.load_library_dir(&lib).expect("library loads");
    m.add_source(
        "endpoints.sysml",
        "package Q { port def P; part def Device { port p : P; } part d : Device; }",
    );
    let mut r = ResolvedModel::build(&m);
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let usage = nodes.iter().find(|n| n["qname"] == "Q::d").unwrap();
    let on_usage: Vec<&str> = nodes
        .iter()
        .filter(|n| n["kind"] == "port" && n["parent"] == usage["id"])
        .filter_map(|n| n["qname"].as_str())
        .collect();
    // The declared port arrives through the typing; the library's generic
    // `ownedPorts`, which every part inherits through its implied base,
    // does not — on this usage or anywhere else in the diagram.
    assert_eq!(on_usage, ["Q::Device::p"], "{g}");
    assert!(
        nodes
            .iter()
            .filter(|n| n["kind"] == "port")
            .all(|n| !n["qname"].as_str().unwrap_or("").contains("ownedPorts")),
        "{g}"
    );
}

#[test]
fn ports_declared_by_a_domain_library_definition_still_render() {
    // A definition loaded from a library directory is a library element,
    // but a usage typed by it reaches its ports through *written*
    // heritage, so they render — only implied library bases stay out.
    let dir = std::env::temp_dir().join(format!(
        "sysmlv2-viz-domlib-{}-{}",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(
        dir.join("DomLib.sysml"),
        "package DomLib { port def DP; part def Device { port dp : DP; } }",
    )
    .unwrap();
    let mut m = Model::new();
    m.load_library_dir(&dir).expect("domain library loads");
    let _ = std::fs::remove_dir_all(&dir);
    m.add_source("u.sysml", "package Q { part d : DomLib::Device; }");
    let mut r = ResolvedModel::build(&m);
    let device = r.resolve_qualified("DomLib::Device").unwrap();
    assert!(r.is_library_element(device));
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let usage = nodes.iter().find(|n| n["qname"] == "Q::d").unwrap();
    let on_usage: Vec<&str> = nodes
        .iter()
        .filter(|n| n["kind"] == "port" && n["parent"] == usage["id"])
        .filter_map(|n| n["qname"].as_str())
        .collect();
    assert_eq!(on_usage, ["DomLib::Device::dp"], "{g}");
}

#[test]
fn written_specialization_of_a_library_part_keeps_abstract_library_ports_out() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut m = Model::new();
    m.load_library_dir(&lib).expect("library loads");
    // `Parts::Part` declares `abstract port ownedPorts`; a written
    // `:> Parts::Part` reaches it through explicit heritage, and it must
    // still not render — only the model's own port does.
    m.add_source(
        "endpoints.sysml",
        "package Q {
            port def P;
            part def Vehicle :> Parts::Part { port p : P; }
            part v : Vehicle;
         }",
    );
    let mut r = ResolvedModel::build(&m);
    let opts = VizOptions::default().with_view(View::Interconnection);
    let g = graph(&mut r, None, &opts).unwrap();
    let nodes = g["nodes"].as_array().unwrap();
    let usage = nodes.iter().find(|n| n["qname"] == "Q::v").unwrap();
    let on_usage: Vec<&str> = nodes
        .iter()
        .filter(|n| n["kind"] == "port" && n["parent"] == usage["id"])
        .filter_map(|n| n["qname"].as_str())
        .collect();
    assert_eq!(on_usage, ["Q::Vehicle::p"], "{g}");
}
