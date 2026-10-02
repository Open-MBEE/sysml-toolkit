//! Imported parameter prerequisites preserve owned-parameter and effective-result rules.
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
#[test]
fn canonical_parameter_prerequisites_preserve_actual_library_oracles_and_replay() {
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
            Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(91).unwrap(), 91).unwrap());
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
                let foreign="
                    behavior ForeignBehavior specializes BaseBehavior {in a; out z; inout both;}
                    function ForeignFunction specializes BaseFunction {return answer;}
                    package Aliases {alias inputAlias for ForeignBehavior::a; alias resultAlias for ForeignFunction::answer;}
                ";
                let consumers="
                    behavior ParameterProvider {public import ForeignBehavior::a; public import ForeignBehavior::z; public import ForeignBehavior::both;}
                    behavior ParameterBridge specializes ParameterProvider;
                    behavior ParameterGrand specializes ParameterBridge {in ownInput; out ownOutput; inout ownBoth;}
                    behavior AliasProvider {public import Aliases::inputAlias;}
                    behavior AliasChild specializes AliasProvider,BaseBehavior;
                    behavior SiblingChild specializes AliasChild,ForeignBehavior {in siblingInput; out siblingOutput; inout siblingBoth;}
                    function ResultProvider {public import ForeignFunction::answer;}
                    function ResultBridge specializes ResultProvider;
                    function ResultGrand specializes ResultBridge {return ownAnswer;}
                    function ResultAliasProvider {public import Aliases::resultAlias;}
                    function ResultAliasChild specializes ResultAliasProvider,BaseFunction;
                    function ResultAliasGrand specializes ResultAliasChild {return aliasAnswer;}
                ";
                let source=format!("behavior BaseBehavior {{in b; out baseOutput; inout baseBoth;}} function BaseFunction {{return baseAnswer;}} {} {}\n
                    behavior OtherBehavior {{in outside;}}
                    behavior MixedBehavior specializes BaseBehavior {{in a; feature ordinary redefines OtherBehavior::outside;}}
                    behavior MixedProvider {{public import MixedBehavior::a;}}
                    behavior MixedChild specializes MixedProvider {{in localInput;}}
                ", if early_foreign {foreign}else{consumers},if early_foreign {consumers}else{foreign});
                let unit = model.add_source("checked-parameter-prerequisites.kerml", &source);
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
                for (source, target, direction) in [
                    ("ForeignBehavior::a", "BaseBehavior::b", "in"),
                    ("ForeignBehavior::z", "BaseBehavior::baseOutput", "out"),
                    ("ForeignBehavior::both", "BaseBehavior::baseBoth", "inout"),
                    ("ForeignFunction::answer", "BaseFunction::baseAnswer", "out"),
                ] {
                    let generated = edges(&mut r, source);
                    assert_eq!(
                        generated.len(),
                        1,
                        "{format:?} {source} early={early_foreign} mode={mode}"
                    );
                    assert_eq!(generated[0].1, id(&mut r, target));
                    let e = r.resolve_qualified(source).unwrap();
                    assert_eq!(
                        r.property(e, "direction").unwrap().as_str(),
                        Some(direction)
                    );
                    if source == "ForeignFunction::answer" {
                        let m = membership(&mut r, source);
                        assert_eq!(r.element_type(m), "ReturnParameterMembership");
                    }
                    identities.push(generated.into_iter().flat_map(|(a, b)| [a, b]).collect());
                }
                let result_edges = edges(&mut r, "ResultGrand::ownAnswer");
                let alias_result_edges = edges(&mut r, "ResultAliasGrand::aliasAnswer");
                let parameter_grand = r.resolve_qualified("ParameterGrand").unwrap();
                let alias_child = r.resolve_qualified("AliasChild").unwrap();
                let sibling = r.resolve_qualified("SiblingChild").unwrap();
                let alias_result = r.resolve_qualified("ResultAliasChild").unwrap();
                if format == GraphFormat::CanonicalV3 {
                    assert_eq!(result_edges.len(), 1, "early={early_foreign} mode={mode}");
                    assert_eq!(result_edges[0].1, id(&mut r, "ForeignFunction::answer"));
                    assert!(
                        alias_result_edges.is_empty(),
                        "an alias cannot create a result slot"
                    );
                    // Ordinary parameters pair with a direct base's effective
                    // parameters, as results do with its effective result: the
                    // imported inputs are slots one inheritance step later.
                    for (name, target) in [
                        ("ParameterGrand::ownInput", "ForeignBehavior::a"),
                        ("ParameterGrand::ownOutput", "ForeignBehavior::z"),
                        ("ParameterGrand::ownBoth", "ForeignBehavior::both"),
                    ] {
                        let generated = edges(&mut r, name);
                        assert_eq!(
                            generated.len(),
                            1,
                            "{name} early={early_foreign} mode={mode}"
                        );
                        assert_eq!(generated[0].1, id(&mut r, target), "{name}");
                    }
                    let actual = inherited(&mut r, parameter_grand).unwrap();
                    assert!(
                        actual.is_empty(),
                        "the imported inputs are taken over: early={early_foreign} mode={mode}"
                    );
                    identities.push(
                        actual
                            .into_iter()
                            .map(|e| r.element_id(e).to_string())
                            .collect(),
                    );
                    let aliases = r.resolve_qualified("Aliases").unwrap();
                    let alias_membership = r
                        .owned_relationships(aliases)
                        .into_iter()
                        .find(|&m| r.membership_member_name(m).as_deref() == Some("inputAlias"))
                        .unwrap();
                    let actual = inherited(&mut r, alias_child).unwrap();
                    assert_eq!(
                        actual,
                        vec![
                            alias_membership,
                            membership(&mut r, "BaseBehavior::baseOutput"),
                            membership(&mut r, "BaseBehavior::baseBoth")
                        ]
                    );
                    identities.push(
                        actual
                            .into_iter()
                            .map(|e| r.element_id(e).to_string())
                            .collect(),
                    );
                    let alias_features = r.type_feature_report(alias_child).projections.unwrap();
                    for name in ["ForeignBehavior::a", "BaseBehavior::b"] {
                        let e = r.resolve_qualified(name).unwrap();
                        assert!(!alias_features.features.contains(&e));
                    }
                    // Each direct base's parameter at the place: the one
                    // `ForeignBehavior` owns, and `AliasChild`'s effective one
                    // — the alias of `a` suppresses the `b` it redefines but
                    // invents no slot, so `AliasChild`'s parameters are
                    // `baseOutput` and `baseBoth`, shifted one place.
                    for (source, targets) in [
                        (
                            "SiblingChild::siblingInput",
                            &["ForeignBehavior::a", "BaseBehavior::baseOutput"][..],
                        ),
                        (
                            "SiblingChild::siblingOutput",
                            &["ForeignBehavior::z", "BaseBehavior::baseBoth"],
                        ),
                        ("SiblingChild::siblingBoth", &["ForeignBehavior::both"]),
                    ] {
                        let generated = edges(&mut r, source);
                        let mut actual: Vec<String> =
                            generated.iter().map(|(_, target)| target.clone()).collect();
                        actual.sort();
                        let mut wanted: Vec<String> =
                            targets.iter().map(|t| id(&mut r, t)).collect();
                        wanted.sort();
                        assert_eq!(actual, wanted, "{source}");
                        identities.push(generated.into_iter().flat_map(|(a, b)| [a, b]).collect());
                    }
                    let result_alias_membership = r
                        .owned_relationships(aliases)
                        .into_iter()
                        .find(|&m| r.membership_member_name(m).as_deref() == Some("resultAlias"))
                        .unwrap();
                    assert_eq!(
                        inherited(&mut r, alias_result).unwrap(),
                        vec![result_alias_membership]
                    );
                    assert_eq!(r.function_result_report(alias_result).result, Ok(None));
                    let own_answer = r.resolve_qualified("ResultGrand::ownAnswer").unwrap();
                    assert_eq!(
                        r.function_result_report(result_grand).result,
                        Ok(Some(own_answer))
                    );
                    for owner in [sibling, alias_result] {
                        let actual = inherited(&mut r, owner).unwrap();
                        identities.push(
                            actual
                                .into_iter()
                                .map(|e| r.element_id(e).to_string())
                                .collect(),
                        );
                    }
                } else {
                    for owner in [parameter_grand, alias_child, sibling, alias_result] {
                        assert!(matches!(
                            inherited(&mut r, owner),
                            Err(OperationError::Incomplete { .. })
                        ));
                    }
                }
                let mixed = r.resolve_qualified("MixedChild").unwrap();
                assert!(
                    matches!(
                        inherited(&mut r, mixed),
                        Err(OperationError::Incomplete { .. })
                    ),
                    "mixed authored/positional source closure remains unsupported"
                );
                assert!(edges(&mut r, "MixedChild::localInput").is_empty());
                for generated in [result_edges, alias_result_edges] {
                    identities.push(generated.into_iter().flat_map(|(a, b)| [a, b]).collect());
                }
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
