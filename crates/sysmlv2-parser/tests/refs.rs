//! Reference-site table + typed navigation
//! (`ResolvedModel::{reference_sites, references_to, declaration_site,
//! owner, owned_members, owned_features, elements_of_metaclass, typings,
//! conforms}`) — the transformation SDK's read side. The corpus gate
//! proves the table is *rename-complete*: splicing a new name over the
//! declaration site plus every recorded reference site must leave the
//! model with the same resolution outcomes.

use std::collections::HashMap;
use sysmlv2_parser::json::{ElementRef, RefSite, ResolvedModel};
use sysmlv2_parser::model::Model;
use sysmlv2_parser::span::Span;

const DEMO: &str = "package Defs {
    part def Wheel;
    part def SpareWheel :> Wheel;
}
package Rig {
    private import Defs::Wheel;
    part def Vehicle {
        part front : Wheel;
        part spare : Defs::SpareWheel;
        attribute count = 2;
    }
    part v : Vehicle;
}";

fn resolved(src: &str) -> ResolvedModel {
    let mut model = Model::new();
    let unit = model.add_source("t.sysml", src);
    assert!(
        unit.diagnostics.is_empty(),
        "test source must parse cleanly: {:?}",
        unit.diagnostics[0]
    );
    ResolvedModel::build(&model)
}

fn slice(src: &str, span: Span) -> &str {
    &src[span.start as usize..span.end as usize]
}

#[test]
fn references_to_finds_every_site_with_exact_spans() {
    let mut r = resolved(DEMO);
    let wheel = r.resolve_qualified("Defs::Wheel").expect("resolves");

    let sites = r.references_to(wheel);
    // `:> Wheel`, `import Defs::Wheel`, `front : Wheel` — the SpareWheel
    // typing of `spare` names SpareWheel, not Wheel.
    assert_eq!(sites.len(), 3, "{sites:?}");
    for s in &sites {
        assert_eq!(s.unit, 0);
        assert_eq!(slice(DEMO, s.name_span), "Wheel", "{s:?}");
    }
    let kinds: Vec<&str> = sites.iter().map(|s| s.kind.as_str()).collect();
    assert!(kinds.contains(&"importedMembership"), "{kinds:?}");
    // The import site's target is the member Wheel itself (the serialized
    // value is its owning Membership — the site records what the name
    // denotes).
    let import_site = sites
        .iter()
        .find(|s| s.kind == "importedMembership")
        .unwrap();
    assert_eq!(import_site.target, wheel);
    // The full-qualified-name span covers the whole path at the import.
    assert_eq!(slice(DEMO, import_site.span), "Defs::Wheel");

    let spare_def = r.resolve_qualified("Defs::SpareWheel").expect("resolves");
    let sites = r.references_to(spare_def);
    assert_eq!(sites.len(), 1);
    assert_eq!(slice(DEMO, sites[0].name_span), "SpareWheel");
    assert_eq!(slice(DEMO, sites[0].span), "Defs::SpareWheel");
    assert_eq!(sites[0].kind, "type");

    // Interior qualifier segments are sites of the element they name:
    // `Defs` is referenced by `import Defs::Wheel` and `Defs::SpareWheel`.
    let defs = r.resolve_qualified("Defs").expect("resolves");
    let sites = r.references_to(defs);
    assert_eq!(sites.len(), 2, "{sites:?}");
    for s in &sites {
        assert_eq!(s.kind, "qualifier");
        assert_eq!(slice(DEMO, s.name_span), "Defs");
    }
}

#[test]
fn payload_typings_record_sites() {
    // `of Publish[1]` is a *typing with a multiplicity* (grammar
    // `Payload`: OwnedFeatureTyping OwnedMultiplicity?), not a declared
    // payload name — the misparse that dropped this site stranded
    // renames of payload types. Both spellings must record.
    let src = "package T {\n    item def Publish;\n    occurrence def Seq {\n        part a; part b;\n        message m1 of Publish from a to b;\n        message m2 of Publish[1] from a to b;\n    }\n}\n";
    let mut r = resolved(src);
    let publish = r.resolve_qualified("T::Publish").expect("resolves");
    let sites = r.references_to(publish);
    let typings: Vec<_> = sites.iter().filter(|s| s.kind == "type").collect();
    assert_eq!(typings.len(), 2, "{sites:?}");
    for s in &typings {
        assert_eq!(slice(src, s.name_span), "Publish", "{s:?}");
    }
}

#[test]
fn declaration_sites_point_at_the_name_token() {
    let mut r = resolved(DEMO);
    for (qn, text) in [
        ("Defs::Wheel", "Wheel"),
        ("Defs::SpareWheel", "SpareWheel"),
        ("Rig::Vehicle::front", "front"),
        ("Rig::v", "v"),
    ] {
        let e = r.resolve_qualified(qn).expect("resolves");
        let (unit, span) = r.declaration_site(e).expect("declared");
        assert_eq!(unit, 0);
        assert_eq!(slice(DEMO, span), text);
    }
}

#[test]
fn navigation_owner_members_typings_conforms() {
    let mut r = resolved(DEMO);
    let vehicle = r.resolve_qualified("Rig::Vehicle").expect("resolves");
    let front = r
        .resolve_qualified("Rig::Vehicle::front")
        .expect("resolves");
    let wheel = r.resolve_qualified("Defs::Wheel").expect("resolves");
    let spare_def = r.resolve_qualified("Defs::SpareWheel").expect("resolves");
    let rig = r.resolve_qualified("Rig").expect("resolves");

    assert_eq!(r.owner(front), Some(vehicle));
    assert_eq!(r.owner(vehicle), Some(rig));
    // A top-level package is owned by the (unnamed) document root
    // Namespace, which itself has no owner.
    let root = r.owner(rig).expect("owned by the document root");
    assert_eq!(r.element_type(root), "Namespace");
    assert_eq!(r.owner(root), None);

    let members: Vec<_> = r.owned_members(vehicle);
    assert_eq!(members.len(), 3);
    let features = r.owned_features(vehicle);
    assert_eq!(features, members, "a part def's members are features");
    assert!(
        r.owned_features(rig).is_empty(),
        "package-owned usages are not features"
    );
    // Imports are Import relationships, not memberships — not members.
    assert_eq!(r.owned_members(rig).len(), 2, "Vehicle + v");

    assert_eq!(r.typings(front), vec![wheel]);
    assert!(r.typings(vehicle).is_empty());
    assert!(r.conforms(spare_def, wheel));
    assert!(!r.conforms(wheel, spare_def));

    let part_defs = r.elements_of_metaclass("PartDefinition");
    assert_eq!(part_defs.len(), 3);
    assert!(part_defs.iter().all(|&e| !r.is_library_element(e)));
}

#[test]
fn expression_references_are_recorded() {
    let src = "package P {
        part def V { attribute mass = 10; attribute total = mass * 2; }
    }";
    let mut r = resolved(src);
    let mass = r.resolve_qualified("P::V::mass").expect("resolves");
    let sites = r.references_to(mass);
    assert_eq!(sites.len(), 1, "the `mass * 2` operand: {sites:?}");
    assert_eq!(slice(src, sites[0].name_span), "mass");
    // The operand span sits inside the value expression, after the
    // declaration.
    let (_, decl) = r.declaration_site(mass).unwrap();
    assert!(sites[0].name_span.start > decl.end);
}

/// Splice `new` over each span (all spans must be exact name tokens),
/// descending so earlier offsets stay valid.
fn splice(src: &str, spans: &[Span], new: &str) -> String {
    let mut spans = spans.to_vec();
    spans.sort_by_key(|s| std::cmp::Reverse(s.start));
    spans.dedup();
    let mut out = src.to_string();
    for s in spans {
        out.replace_range(s.start as usize..s.end as usize, new);
    }
    out
}

/// Rename `e` in a single-unit model by splicing its declaration site and
/// every recorded reference site, and assert the renamed source parses
/// cleanly with identical resolution outcomes (same unresolved count) —
/// the table missed no site, and every span was an exact name token.
fn assert_rename_complete(
    src: &str,
    r: &mut ResolvedModel,
    e: ElementRef,
    new_name: &str,
    label: &str,
) {
    let (_, decl) = r.declaration_site(e).expect("candidate is declared");
    let mut spans: Vec<Span> = vec![decl];
    spans.extend(r.references_to(e).iter().map(|s| s.name_span));
    let renamed = splice(src, &spans, new_name);

    let mut model = Model::new();
    let unit = model.add_source("t.sysml", &renamed);
    assert!(
        unit.diagnostics.is_empty(),
        "renamed source must parse [{label}]: {:?}",
        unit.diagnostics[0]
    );
    let r2 = ResolvedModel::build(&model);
    if r2.unresolved_count() != r.unresolved_count() {
        // Debug aid: name the references that broke.
        let mut m1 = Model::new();
        m1.add_source("t.sysml", src);
        let rep1 = sysmlv2_parser::json::model_resolution_report(&m1);
        let rep2 = sysmlv2_parser::json::model_resolution_report(&model);
        let old: Vec<String> = rep1
            .unresolved
            .iter()
            .map(|(_, q)| q.to_display_string())
            .collect();
        for (_, q) in &rep2.unresolved {
            let q = q.to_display_string();
            if !old.contains(&q) {
                eprintln!("newly unresolved [{label}]: {q}");
            }
        }
        eprintln!(
            "candidate {:?} ty={} sites:",
            r.element_qualified_name(e),
            r.element_type(e)
        );
        for s in r.references_to(e) {
            eprintln!("  kind={} slice={:?}", s.kind, slice(src, s.name_span));
        }
        panic!(
            "rename changed resolution outcomes [{label}]: {} -> {}",
            r.unresolved_count(),
            r2.unresolved_count()
        );
    }
}

#[test]
fn rename_via_the_table_preserves_resolution() {
    let mut r = resolved(DEMO);
    for qn in [
        "Defs::Wheel",
        "Defs::SpareWheel",
        "Rig::Vehicle",
        "Rig::Vehicle::front",
    ] {
        let e = r.resolve_qualified(qn).expect("resolves");
        assert_rename_complete(DEMO, &mut r, e, "Zz9RenamedZz9", qn);
    }
}

/// Corpus gate: on every non-library corpus file, splice-rename up to
/// three safe candidates through the table and require identical
/// resolution outcomes. Candidates are conservative by design — the
/// declared name must be written verbatim at the declaration and at
/// every site, and no *other* site in the file may spell the same text
/// (which excludes effective-name aliasing and shadow capture, both of
/// which are legitimate rename *policy* concerns for the transformation
/// engine's semantic-
/// identity commit, not table defects).
#[test]
fn corpus_rename_gate() {
    let files = sysmlv2_testkit::user_files();
    assert!(files.len() > 100, "expected the corpus checkout");
    let mut attempted = 0usize;
    for path in files {
        let src = std::fs::read_to_string(&path).unwrap();
        let mut model = Model::new();
        let name = path.display().to_string();
        if path.extension().and_then(|e| e.to_str()) == Some("kerml") {
            model.add_library_source(&name, &src);
            continue; // user_files are .sysml; belt and braces
        }
        let unit = model.add_source(&name, &src);
        if !unit.diagnostics.is_empty() {
            continue;
        }
        let mut r = ResolvedModel::build(&model);

        // Group sites by (target, spelled text); tally spellings globally.
        let sites: Vec<RefSite> = r.reference_sites().to_vec();
        let mut by_target: HashMap<ElementRef, Vec<RefSite>> = HashMap::new();
        let mut spelling_targets: HashMap<&str, Vec<ElementRef>> = HashMap::new();
        for s in &sites {
            by_target.entry(s.target).or_default().push(s.clone());
            spelling_targets
                .entry(slice(&src, s.name_span))
                .or_default()
                .push(s.target);
        }
        let mut candidates: Vec<(usize, ElementRef)> = by_target
            .iter()
            .filter_map(|(&e, ss)| {
                let (unit_idx, decl) = r.declaration_site(e)?;
                if unit_idx != 0 {
                    return None;
                }
                let name = slice(&src, decl);
                // Verbatim, unique spelling: every site of e spells `name`,
                // and no site of any *other* element does.
                let verbatim = ss.iter().all(|s| slice(&src, s.name_span) == name);
                let unique = spelling_targets
                    .get(name)
                    .is_some_and(|ts| ts.iter().all(|&t| t == e));
                (verbatim && unique).then_some((ss.len(), e))
            })
            .collect();
        candidates.sort_by_key(|&(n, e)| (std::cmp::Reverse(n), e));

        for &(_, e) in candidates.iter().take(3) {
            assert_rename_complete(
                &src,
                &mut r,
                e,
                "Zz9RenamedZz9",
                &format!("{} elem {:?}", path.display(), e),
            );
            attempted += 1;
        }
    }
    assert!(
        attempted >= 100,
        "gate went vacuous: only {attempted} renames attempted"
    );
}

/// Whether `from`'s owner chain passes through `to` — how relocation
/// eligibility attributes a reference site to the declaration it was
/// written in.
fn owner_chain_reaches(r: &mut ResolvedModel, from: ElementRef, to: ElementRef) -> bool {
    let mut cur = Some(from);
    while let Some(c) = cur {
        if c == to {
            return true;
        }
        cur = r.owner(c);
    }
    false
}

#[test]
fn provenance_records_owner_and_chain_root() {
    // The M29a0 classification scenario: references to `Engine::mass`
    // divide into (a) a site internal to the definition body (`margin`'s
    // value), (b) a site reached through the usage (`engine.mass` — chain
    // root = the usage), and (c) an outside reference through the
    // definition (`Engine::mass`).
    let src = "package P {
    part def Engine {
        attribute mass;
        attribute margin = mass * 2;
    }
    part engine : Engine;
    attribute total = engine.mass;
    attribute direct = Engine::mass;
}";
    let mut r = resolved(src);
    let engine_def = r.resolve_qualified("P::Engine").expect("resolves");
    let mass = r.resolve_qualified("P::Engine::mass").expect("resolves");
    let usage = r.resolve_qualified("P::engine").expect("resolves");
    let total = r.resolve_qualified("P::total").expect("resolves");
    let direct = r.resolve_qualified("P::direct").expect("resolves");
    let margin = r.resolve_qualified("P::Engine::margin").expect("resolves");

    let sites = r.references_to(mass);
    assert_eq!(sites.len(), 3, "{sites:?}");
    let internal: Vec<_> = sites
        .iter()
        .filter(|s| owner_chain_reaches(&mut r, s.owner, margin))
        .cloned()
        .collect();
    assert_eq!(internal.len(), 1, "{sites:?}");
    assert_eq!(internal[0].chain_root, None, "sibling reference is plain");

    let through_usage: Vec<_> = sites
        .iter()
        .filter(|s| owner_chain_reaches(&mut r, s.owner, total))
        .cloned()
        .collect();
    assert_eq!(through_usage.len(), 1, "{sites:?}");
    assert_eq!(
        through_usage[0].chain_root,
        Some(usage),
        "the chain member step records the usage it is reached through"
    );

    let outside: Vec<_> = sites
        .iter()
        .filter(|s| owner_chain_reaches(&mut r, s.owner, direct))
        .cloned()
        .collect();
    assert_eq!(outside.len(), 1, "{sites:?}");
    assert_eq!(
        outside[0].chain_root, None,
        "a qualified reference through the definition has no chain root"
    );

    // Sites of the definition itself: the usage's typing (owner = the
    // usage's declaration) and the qualifier segment of `Engine::mass`
    // (owner = `direct`'s declaration).
    let def_sites = r.references_to(engine_def);
    assert_eq!(def_sites.len(), 2, "{def_sites:?}");
    let typing = def_sites
        .iter()
        .find(|s| s.kind == "type")
        .expect("typing site");
    assert!(owner_chain_reaches(&mut r, typing.owner, usage));
    let qualifier = def_sites
        .iter()
        .find(|s| s.kind == "qualifier")
        .expect("qualifier site");
    assert!(owner_chain_reaches(&mut r, qualifier.owner, direct));

    // The chain spine's first link is a site of the usage itself, plain,
    // with no chain root of its own.
    let usage_sites = r.references_to(usage);
    assert_eq!(usage_sites.len(), 1, "{usage_sites:?}");
    assert_eq!(usage_sites[0].chain_root, None);
    assert!(owner_chain_reaches(&mut r, usage_sites[0].owner, total));
}
