//! Context view: the parts of a system context as nodes around the
//! most connected one, connectors as edges labelled by their
//! definition, no ports.

use sysmlv2_model::json::ResolvedModel;
use sysmlv2_model::model::Model;
use sysmlv2_viz::{View, VizOptions, plantuml};

fn render(src: &str, root: &str) -> String {
    let mut model = Model::new();
    let unit = model.add_source("context.sysml".to_string(), src);
    assert!(
        unit.diagnostics.is_empty(),
        "fixture must parse: {:?}",
        unit.diagnostics
    );
    let mut r = ResolvedModel::build(&model);
    let root = r
        .resolve_qualified(root)
        .unwrap_or_else(|| panic!("{root} must resolve"));
    plantuml(
        &mut r,
        Some(root),
        &VizOptions::default().with_view(View::Context),
    )
}

const CTX: &str = "package P {
    port def A;
    interface def Web { end s : A; end c : ~A; }
    part def Sys; part def User; part def App; part def Dev; part def Lone;
    part def Cloud;
    part def Ctx {
        part system : Sys { port w : A; port x : A; port y : A; port z : A; }
        part user : User { port w : ~A; part sub { port q : A; } }
        part app : App { port w : ~A; port b : A; }
        part dev : Dev[0..*] { port b : ~A; port q : ~A; }
        part cloud : Cloud { port w : ~A; }
        part lone : Lone;
        interface : Web connect system.w to user.w;
        interface : Web connect system.x to app.w;
        interface ble connect app.b to dev.b;
        interface : Web connect system.y to app.w;
        interface : Web connect system.z to cloud.w;
        interface deep connect user.sub.q to dev.q;
        interface self connect app.b to app.w;
    }
    part def Empty;
    part ctx : Ctx;
    part def Narrow :> Ctx;
    part grown : Ctx {
        part extra : Lone { port w : ~A; }
        interface : Web connect system.w to extra.w;
    }
    part def Tie {
        part one : Sys { port w : A; }
        part two : User { port w : ~A; }
        interface : Web connect one.w to two.w;
    }
}
";

fn ctx() -> String {
    render(CTX, "P::Ctx")
}

/// The alias of the node whose label starts with `label`.
fn alias(out: &str, label: &str) -> String {
    let line = out
        .lines()
        .find(|l| l.starts_with(&format!("rectangle \"{label}")))
        .unwrap_or_else(|| panic!("no node {label} in\n{out}"));
    line.split(" as ")
        .nth(1)
        .and_then(|rest| rest.split_whitespace().next())
        .unwrap()
        .to_string()
}

fn edges(out: &str) -> Vec<&str> {
    out.lines()
        .filter(|l| l.contains(" : "))
        .filter(|l| !l.starts_with("rectangle"))
        .collect()
}

#[test]
fn context_hides_ports() {
    let out = ctx();
    for line in out.lines() {
        let word = line.split_whitespace().next().unwrap_or("");
        assert!(
            !matches!(word, "port" | "portin" | "portout"),
            "port line {line:?} in\n{out}"
        );
    }
}

#[test]
fn context_centre_is_most_connected() {
    let out = ctx();
    let marked: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("rectangle") && l.contains("<<system>>"))
        .collect();
    assert_eq!(marked.len(), 1, "{out}");
    assert!(marked[0].starts_with("rectangle \"system : Sys\""), "{out}");
}

#[test]
fn context_labels_edges_by_definition_or_name() {
    let out = ctx();
    let system = alias(&out, "system : Sys");
    let e = edges(&out);
    assert!(
        e.iter()
            .any(|l| l.starts_with(&system) && l.ends_with(": Web")),
        "{out}"
    );
    assert!(e.iter().any(|l| l.ends_with(": ble")), "{out}");
    assert!(e.iter().any(|l| l.ends_with(": deep")), "{out}");
}

#[test]
fn context_spreads_centre_edges() {
    let out = ctx();
    let system = alias(&out, "system : Sys");
    let arrows: Vec<&str> = edges(&out)
        .into_iter()
        .filter(|l| l.starts_with(&format!("{system} ")))
        .map(|l| l.split_whitespace().nth(1).unwrap())
        .collect();
    assert_eq!(arrows, ["-up-", "-down-", "-down-", "-up-"], "{out}");
    let ble = edges(&out)
        .into_iter()
        .find(|l| l.ends_with(": ble"))
        .unwrap();
    assert_eq!(ble.split_whitespace().nth(1), Some("--"), "{out}");
}

#[test]
fn context_hides_stereotypes() {
    let out = ctx();
    assert!(out.lines().any(|l| l == "hide stereotype"), "{out}");
}

#[test]
fn context_keeps_parallel_edges() {
    let out = ctx();
    let system = alias(&out, "system : Sys");
    let app = alias(&out, "app : App");
    let n = edges(&out)
        .into_iter()
        .filter(|l| {
            let w: Vec<&str> = l.split_whitespace().collect();
            w[0] == system && w[2] == app && l.ends_with(": Web")
        })
        .count();
    assert_eq!(n, 2, "{out}");
}

#[test]
fn context_attaches_nested_ends_to_top_part() {
    let out = ctx();
    let user = alias(&out, "user : User");
    let dev = alias(&out, "dev : Dev");
    let deep = edges(&out)
        .into_iter()
        .find(|l| l.ends_with(": deep"))
        .unwrap_or_else(|| panic!("no deep edge in\n{out}"));
    let w: Vec<&str> = deep.split_whitespace().collect();
    assert_eq!((w[0], w[2]), (user.as_str(), dev.as_str()), "{out}");
}

#[test]
fn context_shows_multiplicity() {
    let out = ctx();
    assert!(out.contains("\"dev : Dev [0..*]\""), "{out}");
}

#[test]
fn context_draws_unconnected_parts() {
    let out = ctx();
    alias(&out, "lone : Lone");
}

#[test]
fn context_skips_self_connectors() {
    let out = ctx();
    assert!(!out.contains(": self"), "{out}");
}

#[test]
fn context_tie_takes_first_declared() {
    let out = render(CTX, "P::Tie");
    let first = out
        .lines()
        .find(|l| l.starts_with("rectangle \"one : Sys\""))
        .unwrap_or_else(|| panic!("{out}"));
    assert!(first.contains("<<system>>"), "{out}");
    assert!(!out.contains("\"two : User\" as n2 <<system>>"), "{out}");
}

#[test]
fn context_empty_root_is_valid() {
    let out = render(CTX, "P::Empty");
    assert!(out.starts_with("@startuml\n"), "{out}");
    assert!(out.ends_with("@enduml\n"), "{out}");
    assert!(!out.contains("rectangle \""), "{out}");
}

#[test]
fn context_gives_one_direction_per_neighbour() {
    let out = ctx();
    let system = alias(&out, "system : Sys");
    let app = alias(&out, "app : App");
    let arrows: Vec<&str> = edges(&out)
        .into_iter()
        .filter(|l| l.starts_with(&format!("{system} ")) && l.contains(&format!(" {app} ")))
        .map(|l| l.split_whitespace().nth(1).unwrap())
        .collect();
    assert_eq!(arrows, ["-down-", "-down-"], "{out}");
}

#[test]
fn context_of_a_usage_draws_its_definition_s_parts() {
    let out = render(CTX, "P::ctx");
    alias(&out, "system : Sys");
    alias(&out, "lone : Lone");
    assert!(edges(&out).iter().any(|l| l.ends_with(": ble")), "{out}");
}

#[test]
fn context_of_a_specialized_definition_draws_the_general_s_parts() {
    let out = render(CTX, "P::Narrow");
    alias(&out, "system : Sys");
    assert!(edges(&out).iter().any(|l| l.ends_with(": deep")), "{out}");
}

#[test]
fn context_of_a_usage_adds_its_own_parts_and_connectors() {
    let out = render(CTX, "P::grown");
    let system = alias(&out, "system : Sys");
    let extra = alias(&out, "extra : Lone");
    let joined = edges(&out).into_iter().any(|l| {
        let w: Vec<&str> = l.split_whitespace().collect();
        w[0] == system && w[2] == extra
    });
    assert!(joined, "{out}");
}
