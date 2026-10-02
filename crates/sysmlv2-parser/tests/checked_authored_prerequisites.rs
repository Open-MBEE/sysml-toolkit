//! Strict-ancestor authored positional chains reuse completed prerequisite plans.
#![cfg(feature = "json")]
use std::sync::Arc;
use sysmlv2_parser::{
    json::{DerivedValue, ElementRef, OperationError, Reference, ResolvedModel},
    libcache::LibraryCache,
    model::{GraphFormat, Model},
    prepared::PreparedLibrary,
};
fn inherited(r: &mut ResolvedModel, owner: ElementRef) -> Result<Vec<ElementRef>, OperationError> {
    let report = r.invoke_operation(
        owner,
        "Core-Types-Type-inheritedMemberships_Namespace_Type_Boolean",
        &[
            DerivedValue::Elements(vec![]),
            DerivedValue::Elements(vec![]),
            DerivedValue::Bool(true),
        ],
    )?;
    let DerivedValue::References(values) = report.value else {
        panic!("expected memberships")
    };
    Ok(values
        .into_iter()
        .map(|v| match v {
            Reference::Element(e) => e,
            _ => panic!("expected loaded membership"),
        })
        .collect())
}
fn edges(r: &mut ResolvedModel, name: &str) -> Vec<(String, String)> {
    let e = r.resolve_qualified(name).unwrap();
    let rows = r
        .implied_relationships(e)
        .into_iter()
        .filter(|&e| r.element_type(e) == "Redefinition")
        .collect::<Vec<_>>();
    rows.into_iter()
        .map(|e| {
            (
                r.element_id(e).to_string(),
                r.property(e, "redefinedFeature").unwrap()["@id"]
                    .as_str()
                    .unwrap()
                    .to_owned(),
            )
        })
        .collect()
}
fn id(r: &mut ResolvedModel, name: &str) -> String {
    let e = r.resolve_qualified(name).unwrap();
    r.element_id(e).to_string()
}
fn membership(r: &mut ResolvedModel, name: &str) -> ElementRef {
    let e = r.resolve_qualified(name).unwrap();
    let value = r.property(e, "owningRelationship").unwrap();
    r.element_by_id(value["@id"].as_str().unwrap()).unwrap()
}
fn authored_edges(r: &mut ResolvedModel, name: &str) -> Vec<(String, String)> {
    let e = r.resolve_qualified(name).unwrap();
    let rows = r
        .owned_relationships(e)
        .into_iter()
        .filter(|&e| r.element_type(e) == "Redefinition")
        .collect::<Vec<_>>();
    rows.into_iter()
        .filter_map(|e| {
            if r.property(e, "isImplied").ok().and_then(|v| v.as_bool()) == Some(true) {
                return None;
            }
            Some((
                r.element_id(e).to_string(),
                r.property(e, "redefinedFeature").unwrap()["@id"]
                    .as_str()
                    .unwrap()
                    .to_owned(),
            ))
        })
        .collect()
}
#[test]
fn canonical_authored_prerequisites_preserve_actual_library_suppression_and_replay() {
    let library = sysmlv2_testkit::library_dir();
    if !library.is_dir() {
        return;
    }
    for format in [GraphFormat::LegacyV2, GraphFormat::CanonicalV3] {
        let mut base = Model::with_graph_format(format);
        base.load_library_dir(&library).unwrap();
        base.record_library_cache();
        ResolvedModel::build(&base);
        let cache =
            LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes())
                .unwrap();
        let prepared = base.prepare_library().unwrap();
        let decoded =
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(93).unwrap(), 93).unwrap());
        for early_foreign in [true, false] {
            let mut expected = None;
            for mode in 0..4 {
                let mut model = Model::with_graph_format(format);
                match mode {
                    2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                    3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                    _ => {
                        model.load_library_dir(&library).unwrap();
                        if mode == 1 {
                            model.set_library_cache(cache.clone());
                        }
                    }
                }
                // These are conformant role-preserving authored chains. In
                // particular, an ordinary non-end redefining an end would fail
                // validateRedefinitionEndConformance and is not used as a
                // positive conformance fixture here.
                let foreign="
                    class MidEnd specializes BaseEnd {end feature midEnd;}
                    class LeftEnd specializes MidEnd {end feature leftEnd redefines MidEnd::midEnd;}
                    class RightEnd specializes MidEnd {end feature rightEnd redefines MidEnd::midEnd;}
                    class ForeignEnd specializes LeftEnd,RightEnd {end feature selectedEnd redefines LeftEnd::leftEnd,RightEnd::rightEnd; class Unrelated;}
                    behavior MidInput specializes BaseInput {in midInput;}
                    behavior ForeignInput specializes MidInput {in selectedInput redefines MidInput::midInput;}
                    function MidResult specializes BaseResult {return midResult;}
                    function ForeignResult specializes MidResult {return selectedResult redefines MidResult::midResult;}
                    package Aliases {alias selectedEndAlias for ForeignEnd::selectedEnd; alias selectedInputAlias for ForeignInput::selectedInput;}
                ";
                let consumers = "
                    class EndProvider {public import Aliases::selectedEndAlias;}
                    class EndChild specializes EndProvider,BaseEnd;
                    class EndGrand specializes EndChild {end feature ownEnd;}
                    behavior InputProvider {public import Aliases::selectedInputAlias;}
                    behavior InputChild specializes InputProvider,BaseInput;
                    behavior InputGrand specializes InputChild {in ownInput;}
                    function ResultProvider {public import ForeignResult::selectedResult;}
                    function ResultBridge specializes ResultProvider;
                    function ResultGrand specializes ResultBridge {return ownResult;}
                ";
                let negative="
                    class OtherEnd {end feature outside;}
                    class CrossOwner {end feature selected redefines OtherEnd::outside;}
                    class CrossProvider {public import CrossOwner::selected;}
                    class CrossChild specializes CrossProvider;
                    class SameOwner {end feature selected redefines SameOwner::other; end feature other;}
                    class SameProvider {public import SameOwner::selected;}
                    class SameChild specializes SameProvider;
                    class CycleOne {end feature selected redefines CycleTwo::other;}
                    class CycleTwo {end feature other redefines CycleOne::selected;}
                    class CycleProvider {public import CycleOne::selected;}
                    class CycleChild specializes CycleProvider;
                ";
                let source = format!(
                    "class BaseEnd {{end feature baseEnd;}} behavior BaseInput {{in baseInput;}} function BaseResult {{return baseResult;}} {} {} {negative}",
                    if early_foreign { foreign } else { consumers },
                    if early_foreign { consumers } else { foreign }
                );
                let unit = model.add_source("checked-authored-prerequisites.kerml", &source);
                assert!(
                    unit.diagnostics.is_empty(),
                    "{format:?} early={early_foreign} mode={mode}: {:?}",
                    unit.diagnostics
                );
                let mut r = ResolvedModel::build(&model);
                let result_grand = r.resolve_qualified("ResultGrand").unwrap();
                let cold = inherited(&mut r, result_grand);
                if format == GraphFormat::CanonicalV3 {
                    assert_eq!(cold.unwrap(), vec![], "early={early_foreign} mode={mode}");
                } else {
                    assert!(matches!(cold, Err(OperationError::Incomplete { .. })));
                }
                let mut identities = Vec::<Vec<String>>::new();
                // The intermediate owners contribute the implied suffix. Each
                // later authored edge already fulfils its positional obligation.
                for (source, target) in [
                    ("MidEnd::midEnd", "BaseEnd::baseEnd"),
                    ("MidInput::midInput", "BaseInput::baseInput"),
                    ("MidResult::midResult", "BaseResult::baseResult"),
                ] {
                    let generated = edges(&mut r, source);
                    assert_eq!(generated.len(), 1);
                    assert_eq!(generated[0].1, id(&mut r, target));
                    identities.push(generated.into_iter().flat_map(|(a, b)| [a, b]).collect());
                }
                for (source, targets) in [
                    ("LeftEnd::leftEnd", vec!["MidEnd::midEnd"]),
                    ("RightEnd::rightEnd", vec!["MidEnd::midEnd"]),
                    (
                        "ForeignEnd::selectedEnd",
                        vec!["LeftEnd::leftEnd", "RightEnd::rightEnd"],
                    ),
                    ("ForeignInput::selectedInput", vec!["MidInput::midInput"]),
                    (
                        "ForeignResult::selectedResult",
                        vec!["MidResult::midResult"],
                    ),
                ] {
                    let authored = authored_edges(&mut r, source);
                    assert_eq!(
                        authored
                            .iter()
                            .map(|(_, target)| target.clone())
                            .collect::<Vec<_>>(),
                        targets
                            .into_iter()
                            .map(|name| id(&mut r, name))
                            .collect::<Vec<_>>()
                    );
                    assert!(
                        edges(&mut r, source).is_empty(),
                        "authored edge must prevent duplicate implied edge: {source}"
                    );
                    identities.push(authored.into_iter().flat_map(|(a, b)| [a, b]).collect());
                }
                let result_edges = edges(&mut r, "ResultGrand::ownResult");
                let aliases = r.resolve_qualified("Aliases").unwrap();
                if format == GraphFormat::CanonicalV3 {
                    assert_eq!(result_edges.len(), 1);
                    assert_eq!(
                        result_edges[0].1,
                        id(&mut r, "ForeignResult::selectedResult")
                    );
                    for (owner, alias, excluded) in [
                        (
                            "EndChild",
                            "selectedEndAlias",
                            vec!["ForeignEnd::selectedEnd", "BaseEnd::baseEnd"],
                        ),
                        (
                            "EndGrand",
                            "selectedEndAlias",
                            vec!["ForeignEnd::selectedEnd", "BaseEnd::baseEnd"],
                        ),
                        (
                            "InputChild",
                            "selectedInputAlias",
                            vec!["ForeignInput::selectedInput", "BaseInput::baseInput"],
                        ),
                        (
                            "InputGrand",
                            "selectedInputAlias",
                            vec!["ForeignInput::selectedInput", "BaseInput::baseInput"],
                        ),
                    ] {
                        let owner = r.resolve_qualified(owner).unwrap();
                        let selected = r
                            .owned_relationships(aliases)
                            .into_iter()
                            .find(|&m| r.membership_member_name(m).as_deref() == Some(alias))
                            .unwrap();
                        let actual = inherited(&mut r, owner).unwrap();
                        assert_eq!(actual, vec![selected]);
                        identities.push(
                            actual
                                .into_iter()
                                .map(|e| r.element_id(e).to_string())
                                .collect(),
                        );
                        let features = r.type_feature_report(owner).projections.unwrap();
                        for name in excluded {
                            let e = r.resolve_qualified(name).unwrap();
                            assert!(!features.features.contains(&e));
                        }
                        let unrelated = membership(&mut r, "ForeignEnd::Unrelated");
                        assert!(
                            !features.inherited_memberships.contains(&unrelated),
                            "prerequisite owners cannot add inheritance"
                        );
                    }
                    assert!(edges(&mut r, "EndGrand::ownEnd").is_empty());
                    assert!(edges(&mut r, "InputGrand::ownInput").is_empty());
                    let own_result = r.resolve_qualified("ResultGrand::ownResult").unwrap();
                    assert_eq!(
                        r.function_result_report(result_grand).result,
                        Ok(Some(own_result))
                    );
                } else {
                    for owner in ["EndChild", "EndGrand", "InputChild", "InputGrand"] {
                        let e = r.resolve_qualified(owner).unwrap();
                        assert!(matches!(
                            inherited(&mut r, e),
                            Err(OperationError::Incomplete { .. })
                        ));
                    }
                }
                for owner in ["CrossChild", "SameChild", "CycleChild"] {
                    let e = r.resolve_qualified(owner).unwrap();
                    assert!(
                        matches!(inherited(&mut r, e), Err(OperationError::Incomplete { .. })),
                        "unsupported {owner} {format:?} early={early_foreign} mode={mode}"
                    );
                }
                identities.push(result_edges.into_iter().flat_map(|(a, b)| [a, b]).collect());
                if let Some(expected) = &expected {
                    assert_eq!(
                        &identities, expected,
                        "{format:?} early={early_foreign} mode={mode}"
                    );
                } else {
                    expected = Some(identities);
                }
            }
        }
    }
}
