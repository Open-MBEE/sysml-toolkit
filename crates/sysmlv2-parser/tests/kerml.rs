//! Parser tests for the KerML dialect (`parse_kerml_source`).

use sysmlv2_parser::ast::*;
use sysmlv2_parser::parser::{Parse, parse_kerml_source};

fn parse_ok(src: &str) -> SourceUnit {
    let Parse { unit, diagnostics } = parse_kerml_source(src);
    assert!(
        diagnostics.is_empty(),
        "unexpected diagnostics for {src:?}:\n{diagnostics:#?}"
    );
    assert_eq!(unit.dialect, Dialect::Kerml);
    unit
}

fn package_body(src: &str) -> Vec<Member> {
    let mut unit = parse_ok(src);
    match unit.members.remove(0).kind {
        MemberKind::Package(p) => p.body.expect("package body"),
        other => panic!("expected package, got {other:?}"),
    }
}

fn first_usage(src: &str) -> Usage {
    match package_body(src).into_iter().next().unwrap().kind {
        MemberKind::Usage(u) => u,
        other => panic!("expected usage, got {other:?}"),
    }
}

fn first_def(src: &str) -> Definition {
    match package_body(src).into_iter().next().unwrap().kind {
        MemberKind::Definition(d) => d,
        other => panic!("expected definition, got {other:?}"),
    }
}

#[test]
fn every_kerml_type_kind() {
    for (kw, expected) in [
        ("type", DefKind::Type),
        ("classifier", DefKind::Classifier),
        ("class", DefKind::Class),
        ("struct", DefKind::Struct),
        ("datatype", DefKind::DataType),
        ("assoc", DefKind::Assoc),
        ("behavior", DefKind::Behavior),
        ("interaction", DefKind::Interaction),
        ("function", DefKind::Function),
        ("predicate", DefKind::Predicate),
        ("metaclass", DefKind::Metaclass),
    ] {
        let d = first_def(&format!("package P {{ {kw} X specializes Y; }}"));
        assert_eq!(d.kind, expected, "keyword {kw}");
    }
    let d = first_def("package P { assoc struct A specializes B; }");
    assert_eq!(d.kind, DefKind::AssocStruct);
}

#[test]
fn classifier_declaration_parts() {
    let d = first_def(
        "package P { abstract classifier all C [2] :> A, B disjoint from D unions E, F; }",
    );
    assert!(d.prefix.is_abstract);
    assert!(d.is_sufficient);
    assert!(d.multiplicity.is_some());
    assert_eq!(d.specializes.len(), 2);
    assert_eq!(d.disjoint_from.len(), 1);
    assert_eq!(d.unions.len(), 2);

    let d = first_def("package P { classifier C ~ D; }");
    assert_eq!(d.conjugates.len(), 1);
}

#[test]
fn kerml_features() {
    let u = first_usage(
        "package P { composite feature f : T[1..*] subsets g chains a.b redefines h; }",
    );
    assert_eq!(u.kind, UsageKind::Feature);
    assert!(u.prefix.is_composite);
    assert!(u.declaration.chains.is_some());
    assert_eq!(u.declaration.specializations.len(), 3);

    // `member` type-feature member; `var`; `typed by` synonym.
    let u = first_usage("package P { member var feature v typed by T; }");
    assert!(u.prefix.is_type_member);
    assert!(u.prefix.is_variable);
    assert!(matches!(
        u.declaration.specializations[0],
        FeatureSpecialization::TypedBy(_)
    ));

    // Keyword-less feature.
    let u = first_usage("package P { x : T = 1; }");
    assert_eq!(u.kind, UsageKind::Default);
}

#[test]
fn feature_relationship_parts() {
    let u = first_usage("package P { feature f : T inverse of g featured by H, I; }");
    assert!(u.declaration.inverse_of.is_some());
    assert_eq!(u.declaration.featured_by.len(), 2);
}

#[test]
fn function_with_return_and_result() {
    let body = package_body(
        "package P {
            function Square {
                in x : Real;
                return : Real;
                x * x
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    assert_eq!(d.kind, DefKind::Function);
    let items = d.body.as_ref().unwrap();
    assert!(matches!(&items[1].kind, MemberKind::Return(_)));
    assert!(matches!(&items[2].kind, MemberKind::Result(_)));
}

#[test]
fn expr_bool_inv_step() {
    let u = first_usage("package P { step s : B; }");
    assert_eq!(u.kind, UsageKind::Step);
    let u = first_usage("package P { expr e : F { 1 + 1 } }");
    assert_eq!(u.kind, UsageKind::Expr);
    let u = first_usage("package P { bool b : Pred; }");
    assert_eq!(u.kind, UsageKind::BoolExpr);
    let u = first_usage("package P { inv false notNegative { x >= 0 } }");
    assert_eq!(u.kind, UsageKind::Invariant);
    assert!(matches!(u.detail, UsageDetail::Assert { negated: true }));
}

#[test]
fn connectors_bindings_successions() {
    let u = first_usage("package P { connector c : CT from a.x to b.y; }");
    assert_eq!(u.kind, UsageKind::Connector);
    assert!(matches!(&u.detail, UsageDetail::Connector { ends } if ends.len() == 2));

    let u = first_usage("package P { connector [0..1] link to [1..*] trigger; }");
    assert!(matches!(&u.detail, UsageDetail::Connector { ends } if ends.len() == 2));

    let u = first_usage("package P { binding accept.receiver = triggerTarget; }");
    assert_eq!(u.kind, UsageKind::Binding);

    let u = first_usage("package P { binding [1] startShot = [1] endShot; }");
    assert!(matches!(&u.detail, UsageDetail::Binding { ends } if ends.len() == 2));

    let u = first_usage("package P { succession all [*] acceptable then [*] guard; }");
    assert_eq!(u.kind, UsageKind::Succession);
    assert!(u.declaration.is_sufficient);

    let u = first_usage("package P { succession s first a then b; }");
    assert!(matches!(
        &u.detail,
        UsageDetail::Succession {
            source: Some(_),
            ..
        }
    ));
}

#[test]
fn standalone_relationships() {
    let body = package_body(
        "package P {
            specialization Super subtype A specializes B;
            subclassifier C specializes D;
            typing f typed by T;
            subset g subsets h;
            redefinition i redefines j;
            conjugate X ~ Y;
            disjoint M from N;
            inverse p of q;
            featuring f by T;
        }",
    );
    let kinds: Vec<_> = body
        .iter()
        .filter_map(|m| match &m.kind {
            MemberKind::Relationship(r) => Some(r.kind),
            _ => None,
        })
        .collect();
    use RelationshipDeclKind::*;
    assert_eq!(
        kinds,
        vec![
            Specialization,
            Subclassification,
            FeatureTyping,
            Subsetting,
            Redefinition,
            Conjugation,
            Disjoining,
            FeatureInverting,
            TypeFeaturing
        ]
    );
    let MemberKind::Relationship(r) = &body[0].kind else {
        panic!()
    };
    assert_eq!(r.id.name.as_ref().unwrap().value, "Super");
}

#[test]
fn multiplicity_declarations() {
    let body = package_body(
        "package P {
            multiplicity M subsets N;
            multiplicity exactlyTwo [2];
        }",
    );
    let MemberKind::MultiplicityDecl(m) = &body[0].kind else {
        panic!()
    };
    assert!(m.subsets.is_some());
    let MemberKind::MultiplicityDecl(m) = &body[1].kind else {
        panic!()
    };
    assert!(m.range.is_some());
}

#[test]
fn namespaces_and_kerml_reserved_words() {
    let mut unit = parse_ok("namespace N { class C; }");
    let MemberKind::Package(p) = unit.members.remove(0).kind else {
        panic!()
    };
    assert!(p.is_namespace);

    // SysML-only keywords are ordinary names in KerML.
    let u = first_usage("package P { feature part : T; }");
    assert_eq!(u.declaration.id.name.as_ref().unwrap().value, "part");
    // ...and KerML keywords are not usable as names.
    let bad = parse_kerml_source("package P { feature struct; }");
    assert!(bad.has_errors());
}

#[test]
fn end_cross_feature() {
    let u = first_usage("package P { end [1] feature transferSource references source; }");
    assert!(u.prefix.is_end);
    assert!(u.prefix.end_cross.is_some());

    let u =
        first_usage("package P { end withinBoth subsets outer feature that redefines larger; }");
    let cross = u.prefix.end_cross.as_ref().unwrap();
    assert_eq!(cross.decl.id.name.as_ref().unwrap().value, "withinBoth");

    // The cross feature carries its own basic prefix, distinct from the
    // end feature's.
    let u = first_usage("package P { end in derived x : T feature y : U; }");
    assert!(u.prefix.is_end);
    assert!(u.prefix.direction.is_none());
    assert!(!u.prefix.is_derived);
    let cross = u.prefix.end_cross.as_ref().unwrap();
    assert_eq!(cross.direction, Some(FeatureDirection::In));
    assert!(cross.is_derived);
    assert_eq!(cross.decl.id.name.as_ref().unwrap().value, "x");

    // `const end` marks the end feature itself; `end const` marks the cross.
    let u = first_usage("package P { const end x : T feature y; }");
    assert!(u.prefix.is_constant);
    assert!(!u.prefix.end_cross.as_ref().unwrap().is_constant);
    let u = first_usage("package P { end const x : T feature y; }");
    assert!(!u.prefix.is_constant);
    assert!(u.prefix.end_cross.as_ref().unwrap().is_constant);
}

#[cfg(feature = "json")]
#[test]
fn kerml_json_metaclasses() {
    use serde_json::Value;
    use sysmlv2_parser::json::to_compact_json;

    let unit = parse_ok(
        "package P {
            classifier A;
            feature f : A;
            binding x = y;
            subclassifier A specializes B;
        }",
    );
    let Value::Array(elements) = to_compact_json(&unit) else {
        panic!()
    };
    let types: Vec<&str> = elements
        .iter()
        .map(|e| e["@type"].as_str().unwrap())
        .collect();
    assert!(types.contains(&"Classifier"));
    assert!(types.contains(&"Feature"));
    assert!(types.contains(&"BindingConnector"));
    assert!(types.contains(&"Subclassification"));
    // Dialect-dependent: `f` is a Feature, not a ReferenceUsage.
    assert!(!types.contains(&"ReferenceUsage"));
}

#[test]
fn metadata_body_implicit_redefinition() {
    // KerML.xtext `MetadataBodyFeature`: `'feature'? (':>>'|'redefines')?
    // OwnedRedefinition …` — a leading qualified name is an implicit
    // redefinition target, with or without the `feature` keyword.
    for spelling in ["M::kind = 1;", "feature M::kind = 1;", ":>> M::kind = 1;"] {
        let body = package_body(&format!(
            "package P {{
                metaclass M {{ feature kind; }}
                @M {{ {spelling} }}
            }}"
        ));
        let MemberKind::Usage(meta) = &body[1].kind else {
            panic!()
        };
        assert_eq!(meta.kind, UsageKind::Metadata);
        let MemberKind::Usage(inner) = &meta.body.as_ref().unwrap()[0].kind else {
            panic!()
        };
        assert!(inner.declaration.id.is_empty(), "{spelling}");
        let FeatureSpecialization::Redefines(targets) = &inner.declaration.specializations[0]
        else {
            panic!("{spelling}: expected a redefinition")
        };
        let [TargetRef::Name(qn)] = targets.as_slice() else {
            panic!("{spelling}")
        };
        assert_eq!(qn.to_display_string(), "M::kind", "{spelling}");
    }

    let body = package_body(
        "package P {
            metaclass M;
            @M { outer.inner = 1; }
        }",
    );
    let MemberKind::Usage(meta) = &body[1].kind else {
        panic!()
    };
    let MemberKind::Usage(inner) = &meta.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    let FeatureSpecialization::Redefines(targets) = &inner.declaration.specializations[0] else {
        panic!()
    };
    assert!(matches!(targets.as_slice(), [TargetRef::Chain(links)] if links.len() == 2));
}
