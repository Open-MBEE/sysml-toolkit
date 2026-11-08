//! A `meta` cast types the chain step that follows it: the member of
//! `(x meta T).m` is a feature of the metaclass `T`, as the member of
//! `(x as T).m` is a member of `T`, and a member of several links after
//! either cast resolves link by link in that context (public mirror issue
//! #17).

#![cfg(feature = "json")]

use sysmlv2_parser::{check::validate_model, model::Model};

fn unresolved(source: &str) -> Vec<String> {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("meta.sysml", source);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    validate_model(&model)
        .into_iter()
        .map(|(_, d)| d.message)
        .filter(|m| m.contains("unresolved reference"))
        .collect()
}

#[test]
fn a_meta_cast_types_the_chain_member() {
    let model = "occurrence def Occ {
        occurrence occ1 {
            assert constraint {
                (that meta SysML::OccurrenceUsage).owningUsage->SequenceFunctions::size() > 0
            }
            attribute owned = (that meta SysML::OccurrenceUsage).portionKind;
            attribute inherited = (that meta SysML::OccurrenceUsage).owningType;
            attribute counted = (that meta SysML::OccurrenceUsage).owningUsage->SequenceFunctions::size();
        }
    }";
    assert_eq!(unresolved(model), Vec::<String>::new());
    // A member of several links after the cast resolves each link in the
    // cast's context (the generic reference path resolved the first link
    // lexically, for `as` as for `meta`, so both links were unresolved).
    let nested = "part def Q { attribute y; } occurrence def Occ {
        part q : Q;
        occurrence occ1 {
            attribute m = (that meta SysML::OccurrenceUsage).owningUsage.owningType;
            attribute n = (that as Occ).q.y;
            attribute o = (that meta SysML::OccurrenceUsage).individualDefinition.isIndividual;
        }
    }";
    assert_eq!(unresolved(nested), Vec::<String>::new());
    let bogus_nested = "occurrence def Occ {
        occurrence occ1 { attribute m = (that meta SysML::OccurrenceUsage).owningUsage.noSuchFeature; }
    }";
    let found = unresolved(bogus_nested);
    assert_eq!(found.len(), 1, "{found:?}");
    // The metaclass's features are the chain's scope, nothing else.
    let bogus = "occurrence def Occ {
        occurrence occ1 { attribute m = (that meta SysML::OccurrenceUsage).noSuchFeature; }
    }";
    let found = unresolved(bogus);
    assert_eq!(found.len(), 1, "{found:?}");
    assert!(found[0].contains("noSuchFeature"), "{found:?}");
}
