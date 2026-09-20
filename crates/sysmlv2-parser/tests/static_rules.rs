//! Intended-rule regressions: a diagnostic elsewhere in a negative fixture
//! cannot satisfy this gate. Every rejection has a legal nearby model.
use std::{fs, path::Path};
use sysmlv2_parser::{check, json::ResolvedModel, model::Model};

#[test]
fn structural_rules_have_legal_counterparts() {
    let cases = [
        (
            "validateTriggerInvocationActionWhenArgument.sysml",
            "level : Integer",
            "level : Boolean",
        ),
        (
            "validateTriggerInvocationActionAtArgument.sysml",
            "delay : DurationValue",
            "delay : Time::TimeInstantValue",
        ),
        (
            "validateTriggerInvocationActionAfterArgument.sysml",
            "after 5",
            "after 5 [SI::s]",
        ),
        (
            "validateTransitionUsageTriggerActions.sysml",
            "entry action init",
            "state init",
        ),
        (
            "validateTransitionUsageSuccession.sysml",
            "part p : PD",
            "state p",
        ),
        (
            "validateTransitionFeatureMembershipGuardExpression.sysml",
            "if \"yes\"",
            "if true",
        ),
        ("validateSendActionUsageReceiver.sysml", "to p", "via p"),
        (
            "validateSendActionUsagePayloadArgument.sysml",
            "send to d",
            "send new D() to d",
        ),
        (
            "validateOperatorExpressionCastConformance.kerml",
            "ScalarValues::String",
            "ScalarValues::Integer",
        ),
        (
            "validateMergeNodeOutgoingSuccessions.sysml",
            "first m then d;",
            "",
        ),
        (
            "validateMergeNodeIncomingSuccessions.sysml",
            "first [1] a",
            "first [0..1] a",
        ),
        (
            "validateJoinNodeOutgoingSuccessions.sysml",
            "first j then d;",
            "",
        ),
        (
            "validateForkNodeIncomingSuccessions.sysml",
            "first b then f;",
            "",
        ),
        (
            "validateFeatureChainExpressionFeatureConformance.kerml",
            "class N",
            "feature N",
        ),
        (
            "validateElementFilterMembershipIsModelLevelEvaluable.sysml",
            "Sum(1) == 1",
            "1 == 1",
        ),
        (
            "validateElementFilterMembershipIsBoolean.kerml",
            "filter 1",
            "filter true",
        ),
        (
            "validateDecisionNodeOutgoingSuccessions.sysml",
            "then [1] b",
            "then [0..1] b",
        ),
        (
            "validateDecisionNodeIncomingSuccessions.sysml",
            "first b then d;",
            "",
        ),
        (
            "validateControlNodeOutgoingSuccessions.sysml",
            "[0..1] j",
            "[1] j",
        ),
        (
            "validateControlNodeIncomingSuccessions.sysml",
            "[0..1] f",
            "[1] f",
        ),
        (
            "validateAssignmentActionUsageReferentIsTimeVarying.sysml",
            "attribute def K",
            "part def K",
        ),
        (
            "validateAssignmentActionUsageReferent.sysml",
            "part def D; action def A {",
            "action def A { attribute D : ScalarValues::Integer;",
        ),
        (
            "validateSubsettingFeaturingTypes.kerml",
            "class B {",
            "class B specializes A {",
        ),
        (
            "validateSpecializationSpecificNotConjugated.subset.kerml",
            "feature g ~ f",
            "feature g : A",
        ),
        (
            "validateSpecializationSpecificNotConjugated.kerml",
            "class B ~ A",
            "class B",
        ),
        (
            "validateFlowEndImplicitSubsetting.sysml",
            "a::o to b::i",
            "a.o to b.i",
        ),
        (
            "validateFlowEndImplicitSubsetting.kerml",
            "a::o to b::i",
            "a.o to b.i",
        ),
        (
            "validateFlowEndSubsetting.kerml",
            "A::o to B::i",
            "a.o to b.i",
        ),
        (
            "validateFeatureHasType.kerml",
            "class D",
            "feature D : ScalarValues::Integer",
        ),
        ("validateFeatureCrossFeatureType.kerml", "bx : X", "bx : A"),
        (
            "validateFeatureChainingFeatureConformance.kerml",
            "class A {",
            "class A specializes B {",
        ),
        (
            "validateCrossSubsettingCrossingFeature.kerml",
            "crosses p",
            "",
        ),
        (
            "validateConnectorRelatedFeatures.sysml",
            "connection {",
            "abstract connection {",
        ),
        (
            "validateClassifierDefaultSupertype.kerml",
            "class D",
            "struct D",
        ),
        (
            "validateBindingConnectorTypeConformance.subject.sysml",
            "subject n : ID",
            "subject n : PD",
        ),
        (
            "validateBindingConnectorTypeConformance.satisfy.sysml",
            "item i : ID",
            "item i : PD",
        ),
        (
            "validateBindingConnectorTypeConformance.result.kerml",
            "return r : D",
            "return r : C",
        ),
        (
            "validateBindingConnectorTypeConformance.kerml",
            "ScalarValues::String",
            "ScalarValues::Integer",
        ),
        (
            "validateBindingConnectorIsBinary.kerml",
            "end feature e references z;",
            "",
        ),
        (
            "validateAssociationBinarySpecialization.kerml",
            "end c : C;",
            "",
        ),
        ("validateFeatureValueOverriding.kerml", "= 1", "default = 1"),
        ("validateFeatureValueOverriding.sysml", "= 1", "default = 1"),
        (
            "validateFeatureEndFeatureMultiplicity.kerml",
            "[0..*]",
            "[1]",
        ),
        ("validateMetadataFeatureBody.kerml", "z = 1", "x = 1"),
        (
            "validateMetadataFeatureAnnotatedElement.kerml",
            "KerML::Feature",
            "KerML::Class",
        ),
        (
            "validateOperatorExpressionBracketOperator.kerml",
            "xs[1]",
            "xs#(1)",
        ),
        (
            "validatePortDefinitionOwnedUsagesNotComposite.sysml",
            "part p : D",
            "ref part p : D",
        ),
        (
            "validatePortUsageNestedUsagesNotComposite.sysml",
            "part x : D",
            "ref part x : D",
        ),
        (
            "validatePortUsageIsReference.sysml",
            "variant port a",
            "variant ref port a",
        ),
        (
            "validateViewDefinitionOnlyOnvViewRendering.sysml",
            "render rendering r2 : R;",
            "",
        ),
        (
            "validateViewUsageOnlyOneRendering.sysml",
            "render rendering r2 : R;",
            "",
        ),
        ("validateInterfaceDefinitionEnd.sysml", "part", "port"),
        (
            "validateInterfaceUsageEnd.sysml",
            "end part ::> fuel",
            "end port ::> inPort",
        ),
        (
            "validateRequirementVerificationMembershipOwningType.sysml",
            "requirement def Q { verify requirement r : R; }",
            "verification def V { objective Q { verify requirement r : R; } }",
        ),
        (
            "validateConstructorExpressionNoDuplicateFeatureRedefinition.kerml",
            "x = t, x = t",
            "x = t",
        ),
        (
            "validateInvocationExpressionInstantiatedType.kerml",
            "class A;",
            "function A;",
        ),
        (
            "validateInstantiationExpressionInstantiatedType.kerml",
            "package Q;",
            "class Q;",
        ),
        (
            "validateFeatureReferenceExpressionReferentIsFeature.kerml",
            "= A",
            "= true",
        ),
        ("validateOperatorExpressionQuantity.sysml", "[3]", "[SI::m]"),
        (
            "validateBehaviorSpecialization.kerml",
            "struct S;",
            "behavior S;",
        ),
        (
            "validateClassSpecialization.kerml",
            "datatype D;",
            "class D;",
        ),
        (
            "validateDataTypeSpecialization.kerml",
            "class C;",
            "datatype C;",
        ),
        (
            "validateStructureSpecialization.kerml",
            "behavior B;",
            "struct B;",
        ),
        (
            "validateOwnedUnioningNotOne.kerml",
            "unions A",
            "unions A, B",
        ),
        (
            "validateOwnedIntersectingNotOne.kerml",
            "intersects A",
            "intersects A, B",
        ),
        (
            "validateOwnedDifferencingNotOne.kerml",
            "differences A",
            "differences A, B",
        ),
        (
            "validateTypeUnioningTypesNotSelf.kerml",
            "unions D, A",
            "unions A, B",
        ),
        (
            "validateTypeIntersectingTypesNotSelf.kerml",
            "intersects D, A",
            "intersects A, B",
        ),
        (
            "validateTypeDifferencingTypesNotSelf.kerml",
            "differences D, A",
            "differences A, B",
        ),
        ("validateFeatureIsVariable.kerml", "datatype D", "class D"),
        (
            "validateFeaturePortionNotVariable.kerml",
            "portion var",
            "portion",
        ),
        (
            "validateFeatureValueIsInitial.kerml",
            "feature f",
            "var feature f",
        ),
        (
            "validateFeatureConstantIsVariable.sysml",
            "attribute def",
            "part def",
        ),
        (
            "validateOccurrenceUsageIndividualDefinition.sysml",
            ": I1, I2",
            ": I1",
        ),
        (
            "validateOccurrenceUsageIndividualUsage.sysml",
            "part def D",
            "individual part def D",
        ),
        (
            "validateOccurrenceUsageIsPortion.sysml",
            "snapshot part",
            "part",
        ),
        (
            "validatePerformActionUsageReference.sysml",
            "part d : D",
            "action d",
        ),
        (
            "validateExhibitStateUsageReference.sysml",
            "action a : Act",
            "state a",
        ),
        (
            "validateIncludeUseCaseUsageReference.sysml",
            "part d : D",
            "use case d",
        ),
        (
            "validateSatisfyRequirementUsageReference.sysml",
            "part x : D",
            "requirement x",
        ),
        (
            "validateAssertConstraintUsageReference.sysml",
            "part x : D",
            "constraint x",
        ),
        (
            "validateEventOccurrenceUsageReferent.sysml",
            "attribute a : ScalarValues::Real",
            "part a",
        ),
        (
            "validateLibraryPackageNotStandard.kerml",
            "standard library",
            "library",
        ),
        (
            "validateMetadataFeatureMetadataNotAbstract.kerml",
            "abstract metaclass",
            "metaclass",
        ),
        (
            "validateFeatureOwnedReferenceSubsetting.kerml",
            "references a references b",
            "references a",
        ),
        (
            "validateFeatureOwnedCrossSubsetting.kerml",
            "crosses a.x crosses a.y",
            "crosses a.x",
        ),
        (
            "validateFeatureChainingFeatureNotOne.kerml",
            "chains a;",
            "chains a.b;",
        ),
        (
            "validateFeatureChainingFeaturesNotSelf.kerml",
            "chains a.b",
            "chains a.a",
        ),
        (
            "validateFunctionResultExpressionMembership.kerml",
            "specializes F1, F2",
            "specializes F1",
        ),
        (
            "validateExpressionResultExpressionMembership.kerml",
            ": F1, F2",
            ": F1",
        ),
        (
            "validateFunctionResultParameterMembership.kerml",
            "return r2 : ScalarValues::Integer;",
            "",
        ),
        (
            "validateExpressionResultParameterMembership.kerml",
            "return r2 : ScalarValues::Integer;",
            "",
        ),
        (
            "validateTypeOwnedMultiplicity.kerml",
            "multiplicity m2 [2];",
            "",
        ),
        (
            "validateStateDefinitionSubactionKind.sysml",
            "entry; do; exit; entry;",
            "entry; do; exit;",
        ),
        (
            "validateStateUsageSubactionKind.sysml",
            "entry; entry;",
            "entry;",
        ),
        (
            "validateStateDefinitionParallelSubactions.sysml",
            "parallel",
            "",
        ),
        ("validateStateUsageParallelSubactions.sysml", "parallel", ""),
        (
            "validateControlNodeOwningType.sysml",
            "constraint def C",
            "action def C",
        ),
        (
            "validateRedefinitionDirectionConformance.kerml",
            "out feature y",
            "in feature y",
        ),
        (
            "validateRedefinitionEndConformance.kerml",
            "feature c redefines",
            "end feature c redefines",
        ),
        (
            "validateRedefinitionFeaturingTypes.kerml",
            "feature y redefines x;",
            "class C { feature y redefines x; }",
        ),
        (
            "validateSubsettingConstantConformance.kerml",
            "var feature b",
            "const feature b",
        ),
        (
            "validateSubsettingUniquenessConformance.kerml",
            " nonunique",
            "",
        ),
        ("validateAssociationEndTypes.kerml", "a : A, B", "a : A"),
        (
            "validateAssociationRelatedTypes.kerml",
            "end a : T;",
            "end a : T; end b : T;",
        ),
    ];
    let library = sysmlv2_testkit::library_dir();
    assert!(library.is_dir());
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache = base.take_recorded_library_cache().unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/opensysml/probes");
    let contracts: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/opensysml/static-contracts.json")).unwrap();
    let contracts = contracts["contracts"].as_array().unwrap();
    assert_eq!(contracts.len(), cases.len());
    let mut failures = Vec::new();
    for (file, from, to) in cases {
        let contract = contracts
            .iter()
            .find(|c| c["fixture"] == file)
            .expect("registered rule contract");
        let source = fs::read_to_string(root.join(file)).unwrap();
        assert!(source.contains(from), "{file}: missing mutation {from}");
        let rule = file.split('.').next().unwrap();
        let tag = format!("[{rule}]");
        for (negative, source) in [(true, source.clone()), (false, source.replace(from, to))] {
            let source = if !negative
                && file == "validateTransitionFeatureMembershipGuardExpression.sysml"
            {
                source.replace("if 1 then", "if true then")
            } else {
                source
            };
            let source = if !negative && file == "validateFeatureCrossFeatureType.kerml" {
                source.replace("ax : A", "ax : B")
            } else {
                source
            };
            // The set-operation legal neighbors need a second distinct operand.
            let source = if !negative && file.contains("TypesNotSelf")
                || !negative && file.starts_with("validateOwned")
            {
                source.replace("class A;", "class A; class B;")
            } else {
                source
            };
            let mut model = Model::new();
            model.load_library_dir(&library).unwrap();
            model.set_library_cache(cache.clone());
            let unit = model.add_source(file, &source);
            assert!(
                unit.diagnostics.is_empty(),
                "{file}: {:?}",
                unit.diagnostics
            );
            let mut r = ResolvedModel::build(&model);
            let diagnostics = check::validate_semantics_with(&mut r, &model);
            if negative && !diagnostics.iter().any(|(_, d)| d.message.contains(&tag)) {
                failures.push(format!("{file}: missing intended rule: {diagnostics:?}"));
            }
            if negative {
                for (_, d) in diagnostics.iter().filter(|(_, d)| d.message.contains(&tag)) {
                    assert_eq!(
                        format!("{:?}", d.severity),
                        contract["severity"].as_str().unwrap(),
                        "{file}: diagnostic category"
                    );
                    assert!(
                        d.span.start < d.span.end && d.span.end <= source.len() as u32,
                        "{file}: invalid diagnostic span: {d:?}"
                    );
                    assert!(
                        d.span.start as usize >= source.find("package").unwrap_or(0),
                        "{file}: diagnostic points into fixture comments: {d:?}"
                    );
                }
            }
            let mut diagnostics = diagnostics;
            if !negative {
                diagnostics.extend(check::validate_model_with(&mut r, &model));
            }
            if !negative && !diagnostics.is_empty() {
                failures.push(format!("{file}: legal neighbor rejected: {diagnostics:?}"));
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn chains_and_static_contracts_preserve_edges_across_replay_and_file_order() {
    use sysmlv2_parser::json::model_to_compact_json;
    let types = "package Types { class A { feature b : ScalarValues::Integer = 1; } }";
    let uses = "package Uses {
        feature a : Types::A; feature b : ScalarValues::Boolean;
        feature c chains a.b;
        feature incomplete chains a.missing;
        feature text : ScalarValues::String;
        binding incomplete = text;
        class D specializes Types::A { feature redefines b = 2; }
    }";
    let mut baseline = None;
    for reverse in [false, true] {
        let build = |cache| {
            let mut m = Model::new();
            m.load_library_dir(&sysmlv2_testkit::library_dir()).unwrap();
            if let Some(cache) = cache {
                m.set_library_cache(cache);
            } else {
                m.record_library_cache();
            }
            let files = if reverse {
                [("uses.kerml", uses), ("types.kerml", types)]
            } else {
                [("types.kerml", types), ("uses.kerml", uses)]
            };
            for (name, src) in files {
                assert!(m.add_source(name, src).diagnostics.is_empty());
            }
            m
        };
        let cold = build(None);
        let mut r = ResolvedModel::build(&cold);
        let diags = check::validate_semantics_with(&mut r, &cold);
        assert_eq!(diags.len(), 1, "{diags:?}");
        assert!(
            diags[0]
                .1
                .message
                .contains("[validateFeatureValueOverriding]")
        );
        let diagnostics: Vec<_> = diags
            .iter()
            .map(|(u, d)| (cold.units()[*u].name.clone(), d.span, d.message.clone()))
            .collect();
        if let Some(baseline) = &baseline {
            assert_eq!(baseline, &diagnostics);
        } else {
            baseline = Some(diagnostics.clone());
        }
        let cache = cold.take_recorded_library_cache().unwrap();
        let warm = build(Some(cache));
        let mut r = ResolvedModel::build(&warm);
        let warm_diags: Vec<_> = check::validate_semantics_with(&mut r, &warm)
            .iter()
            .map(|(u, d)| (warm.units()[*u].name.clone(), d.span, d.message.clone()))
            .collect();
        assert_eq!(diagnostics, warm_diags);
        let graph = model_to_compact_json(&cold);
        assert_eq!(graph, model_to_compact_json(&warm));
        let elements = graph.as_array().unwrap();
        let named = |name: &str, ty: &str| {
            elements
                .iter()
                .find(|e| e["declaredName"] == name && e["@type"] == ty)
                .unwrap()
        };
        let a_type = named("A", "Class");
        let member_rel = &a_type["ownedRelationship"].as_array().unwrap()[0]["@id"];
        let nested_b = elements
            .iter()
            .find(|e| e["declaredName"] == "b" && e["owningRelationship"]["@id"] == *member_rel)
            .unwrap();
        let c = named("c", "Feature");
        let rel_id = &c["ownedRelationship"].as_array().unwrap()[1]["@id"];
        let link = elements.iter().find(|e| e["@id"] == *rel_id).unwrap();
        assert_eq!(
            link["chainingFeature"]["@id"], nested_b["@id"],
            "chain member captured the lexical Boolean feature"
        );
    }
}

#[test]
fn metadata_values_and_nested_members_require_model_level_contracts() {
    let sources = [
        (
            "package P { metaclass M { feature x : ScalarValues::Integer; }
           class C { feature runtime : ScalarValues::Integer; @M { x = runtime; } } }",
            Some("validateMetadataFeatureBody"),
        ),
        (
            "package P { metaclass M { feature x { feature y : ScalarValues::Integer; } }
           class C { @M { x { z = 1; } } } }",
            Some("validateMetadataFeatureBody"),
        ),
        (
            "package P { metaclass M { feature x { feature y : ScalarValues::Integer; } }
           class C { @M { x { y = 1; } } } }",
            None,
        ),
        ("package P { feature x; feature y; binding x = y; }", None),
        (
            "package P { class A; feature x : A; feature y : Missing; binding x = y; }",
            None,
        ),
    ];
    for (source, expected) in sources {
        let mut model = Model::new();
        model
            .load_library_dir(&sysmlv2_testkit::library_dir())
            .unwrap();
        assert!(
            model
                .add_source("contracts.kerml", source)
                .diagnostics
                .is_empty()
        );
        let diags = check::validate_semantics(&model);
        if let Some(rule) = expected {
            assert!(
                diags.iter().any(|(_, d)| d.message.contains(rule)),
                "{source}: {diags:?}"
            );
        } else {
            assert!(diags.is_empty(), "{source}: {diags:?}");
        }
    }
}

#[test]
fn additional_negative_contracts_have_legal_counterparts() {
    let contracts: serde_json::Value =
        serde_json::from_str(include_str!("fixtures/opensysml/negative-contracts.json")).unwrap();
    let library = sysmlv2_testkit::library_dir();
    let mut base = Model::new();
    base.load_library_dir(&library).unwrap();
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache = base.take_recorded_library_cache().unwrap();
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/opensysml");
    let mut failures = Vec::new();
    for c in contracts["contracts"].as_array().unwrap() {
        let name = c["fixture"].as_str().unwrap();
        let source = fs::read_to_string(root.join(name)).unwrap();
        let tag = format!("[{}]", c["rule"].as_str().unwrap());
        let from = c["from"].as_str().unwrap();
        assert!(source.contains(from));
        let mut legal = source.replace(from, c["to"].as_str().unwrap());
        if let Some(from) = c["extra_from"].as_str() {
            legal = legal.replace(from, c["extra_to"].as_str().unwrap());
        }
        for (negative, source) in [(true, source), (false, legal)] {
            let mut m = Model::new();
            m.load_library_dir(&library).unwrap();
            m.set_library_cache(cache.clone());
            let unit = m.add_source(name, &source);
            assert!(
                unit.diagnostics.is_empty(),
                "{name}: {:?}",
                unit.diagnostics
            );
            let mut r = ResolvedModel::build(&m);
            let mut diags = check::validate_semantics_with(&mut r, &m);
            if c["verdict"] == "accepted" {
                if !diags.is_empty() {
                    failures.push(format!(
                        "{name}: accepted enum-restriction model: {diags:?}"
                    ));
                }
            } else if negative {
                if !diags.iter().any(|(_, d)| {
                    d.message.contains(&tag)
                        && format!("{:?}", d.severity) == c["severity"].as_str().unwrap()
                        && d.span.start < d.span.end
                }) {
                    failures.push(format!("{name}: missing {tag}: {diags:?}"));
                }
            } else {
                diags.extend(check::validate_model_with(&mut r, &m));
                if !diags.is_empty() {
                    failures.push(format!("{name}: legal counterpart: {diags:?}"));
                }
            }
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn standalone_typing_participates_in_binding_conformance() {
    let source =
        "package P { class A; class B; feature x; feature y : B; typing x : A; binding x = y; }";
    for (bad, source) in [
        (true, source.to_owned()),
        (false, source.replace("y : B", "y : A")),
    ] {
        let mut m = Model::new();
        assert!(m.add_source("typing.kerml", &source).diagnostics.is_empty());
        let diags = check::validate_semantics(&m);
        assert_eq!(
            diags.iter().any(|(_, d)| d
                .message
                .contains("[validateBindingConnectorTypeConformance]")),
            bad,
            "{diags:?}"
        );
    }
}
