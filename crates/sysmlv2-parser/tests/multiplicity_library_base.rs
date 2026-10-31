//! checkMultiplicitySpecialization (KerML 8.3.3.1.9): every Multiplicity
//! subsets `Base::naturals`, the root feature of all multiplicities, so its
//! values are natural numbers — a model's ranges and the library's own.

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, ElementRef, ResolvedModel},
    model::Model,
};

/// The qualified names of the targets of `e`'s implied Subsettings.
fn implied_subsetting_targets(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    let mut targets = Vec::new();
    for rel in r.implied_relationships(e) {
        if r.element_type(rel) != "Subsetting" {
            continue;
        }
        let target = r
            .element_properties(rel)
            .get("subsettedFeature")
            .and_then(|v| v.get("@id"))
            .and_then(|v| v.as_str())
            .and_then(|id| r.element_by_id(id))
            .expect("an implied Subsetting names a loaded target");
        targets.push(r.element_qualified_name(target).unwrap());
    }
    targets.sort();
    targets
}

#[test]
fn multiplicities_subset_the_library_naturals() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source(
        "m.sysml",
        "package M {
            part def P;
            part def A {
                part r : P[2];
                attribute y[0..*];
            }
            part top : P[1];
        }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    let mut ranges: Vec<ElementRef> = r
        .elements_of_metaclass("MultiplicityRange")
        .into_iter()
        .filter(|&m| !r.is_library_element(m))
        .collect();
    assert_eq!(ranges.len(), 3);
    for name in ["Base::exactlyOne", "Base::zeroOrOne"] {
        ranges.push(r.resolve_qualified(name).unwrap());
    }
    for m in ranges {
        let owner = r.owner(m).and_then(|o| r.element_qualified_name(o));
        let targets = implied_subsetting_targets(&mut r, m);
        assert!(
            targets.iter().any(|t| t == "Base::naturals"),
            "{owner:?}: {targets:?}"
        );
        assert!(
            !targets.iter().any(|t| t == "Base::things"),
            "{owner:?}: the generic Feature base is redundant beside naturals: {targets:?}"
        );
    }
    // The checked cardinality domain accepts the new base: `r : P[2]` still
    // certifies two.
    let part = r.resolve_qualified("M::A::r").unwrap();
    let report = r.cardinality_report(part);
    assert_eq!(
        report.bounds.map(|b| b.size()),
        Ok(Some(2)),
        "{:?}",
        report.bounds
    );
}
