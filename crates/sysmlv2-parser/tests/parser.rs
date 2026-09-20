//! Parser tests for the currently-covered subset of the SysML v2 grammar.

use sysmlv2_parser::ast::*;
use sysmlv2_parser::parser::{Parse, parse_source};

fn parse_ok(src: &str) -> SourceUnit {
    let Parse { unit, diagnostics } = parse_source(src);
    assert!(
        diagnostics.is_empty(),
        "unexpected diagnostics for {src:?}:\n{diagnostics:#?}"
    );
    unit
}

fn single_member(src: &str) -> MemberKind {
    let mut unit = parse_ok(src);
    assert_eq!(unit.members.len(), 1, "expected one member");
    unit.members.remove(0).kind
}

fn package_body(src: &str) -> Vec<Member> {
    match single_member(src) {
        MemberKind::Package(p) => p.body.expect("package should have a body"),
        other => panic!("expected package, got {other:?}"),
    }
}

// ---------------------------------------------------------------------------
// Packages, imports, aliases, annotations
// ---------------------------------------------------------------------------

#[test]
fn empty_package() {
    let MemberKind::Package(p) = single_member("package P;") else {
        panic!()
    };
    assert_eq!(p.id.name.unwrap().value, "P");
    assert!(p.body.is_none());
    assert!(!p.is_library);
}

#[test]
fn library_package_with_short_name() {
    let MemberKind::Package(p) = single_member("standard library package <'1.1'> Base {}") else {
        panic!()
    };
    assert!(p.is_library && p.is_standard);
    assert_eq!(p.id.short_name.unwrap().value, "1.1");
    assert_eq!(p.id.name.unwrap().value, "Base");
    assert_eq!(p.body.unwrap().len(), 0);
}

#[test]
fn unrestricted_name_package() {
    let MemberKind::Package(p) = single_member("package 'My Model';") else {
        panic!()
    };
    assert_eq!(p.id.name.unwrap().value, "My Model");
}

#[test]
fn imports() {
    let body = package_body(
        "package P {
            private import ScalarValues::*;
            import PartsLib::Vehicle;
            import all Lib::**;
            public import A::B::*::**;
        }",
    );
    let MemberKind::Import(i0) = &body[0].kind else {
        panic!()
    };
    assert_eq!(body[0].visibility, Some(Visibility::Private));
    assert!(i0.is_namespace && !i0.is_recursive);
    assert_eq!(i0.target.to_display_string(), "ScalarValues");

    let MemberKind::Import(i1) = &body[1].kind else {
        panic!()
    };
    assert!(!i1.is_namespace);
    assert_eq!(i1.target.to_display_string(), "PartsLib::Vehicle");

    let MemberKind::Import(i2) = &body[2].kind else {
        panic!()
    };
    assert!(i2.is_import_all && i2.is_recursive);

    let MemberKind::Import(i3) = &body[3].kind else {
        panic!()
    };
    assert!(i3.is_namespace && i3.is_recursive);
    assert_eq!(body[3].visibility, Some(Visibility::Public));
}

#[test]
fn filtered_import() {
    let body = package_body("package P { private import Lib::*[@Safety][x > 1]; }");
    let MemberKind::Import(imp) = &body[0].kind else {
        panic!()
    };
    assert_eq!(imp.filters.len(), 2);
    assert!(matches!(
        imp.filters[0].kind,
        ExprKind::Classification {
            op: ClassificationOp::AtType,
            operand: None,
            ..
        }
    ));
}

#[test]
fn alias_member() {
    let body = package_body("package P { alias v for Vehicles::Vehicle; }");
    let MemberKind::Alias(a) = &body[0].kind else {
        panic!()
    };
    assert_eq!(a.id.name.as_ref().unwrap().value, "v");
    assert_eq!(a.target.to_display_string(), "Vehicles::Vehicle");
}

#[test]
fn filter_member() {
    let body = package_body("package P { filter @Approved; }");
    assert!(matches!(&body[0].kind, MemberKind::Filter(_)));
}

#[test]
fn annotations() {
    let body = package_body(
        r#"package P {
            doc /* documentation text */
            comment about X, Y locale "en_US" /* a comment */
            /* bare comment */
            rep asText language "json" /* {"x": 1} */
        }"#,
    );
    let MemberKind::Doc(d) = &body[0].kind else {
        panic!()
    };
    assert_eq!(d.body.trim(), "documentation text");

    let MemberKind::Comment(c) = &body[1].kind else {
        panic!()
    };
    assert_eq!(c.about.len(), 2);
    assert_eq!(c.locale.as_deref(), Some("en_US"));

    let MemberKind::Comment(bare) = &body[2].kind else {
        panic!()
    };
    assert!(bare.about.is_empty());
    assert_eq!(bare.body.trim(), "bare comment");

    let MemberKind::TextualRep(r) = &body[3].kind else {
        panic!()
    };
    assert_eq!(r.language, "json");
    assert_eq!(r.id.name.as_ref().unwrap().value, "asText");
}

// ---------------------------------------------------------------------------
// Definitions
// ---------------------------------------------------------------------------

#[test]
fn part_def_with_specialization() {
    let body = package_body("package P { part def Car :> Vehicle, Wheeled; }");
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    assert_eq!(d.kind, DefKind::Part);
    assert_eq!(d.id.name.as_ref().unwrap().value, "Car");
    assert_eq!(d.specializes.len(), 2);
}

#[test]
fn abstract_and_variation_defs() {
    let body = package_body(
        "package P {
            abstract part def A;
            variation attribute def V;
            individual def I;
            individual part def Napoleon;
        }",
    );
    let MemberKind::Definition(a) = &body[0].kind else {
        panic!()
    };
    assert!(a.prefix.is_abstract);
    let MemberKind::Definition(v) = &body[1].kind else {
        panic!()
    };
    assert!(v.prefix.is_variation);
    assert_eq!(v.kind, DefKind::Attribute);
    let MemberKind::Definition(i) = &body[2].kind else {
        panic!()
    };
    assert_eq!(i.kind, DefKind::Individual);
    assert!(i.prefix.is_individual);
    let MemberKind::Definition(n) = &body[3].kind else {
        panic!()
    };
    assert_eq!(n.kind, DefKind::Part);
    assert!(n.prefix.is_individual);
}

#[test]
fn every_simple_def_kind() {
    let kinds = [
        ("attribute", DefKind::Attribute),
        ("enum", DefKind::Enum),
        ("occurrence", DefKind::Occurrence),
        ("item", DefKind::Item),
        ("metadata", DefKind::Metadata),
        ("part", DefKind::Part),
        ("port", DefKind::Port),
        ("connection", DefKind::Connection),
        ("interface", DefKind::Interface),
        ("allocation", DefKind::Allocation),
        ("flow", DefKind::Flow),
        ("action", DefKind::Action),
        ("state", DefKind::State),
        ("calc", DefKind::Calc),
        ("constraint", DefKind::Constraint),
        ("requirement", DefKind::Requirement),
        ("concern", DefKind::Concern),
        ("case", DefKind::Case),
        ("analysis", DefKind::Analysis),
        ("verification", DefKind::Verification),
        ("view", DefKind::View),
        ("viewpoint", DefKind::Viewpoint),
        ("rendering", DefKind::Rendering),
    ];
    for (kw, expected) in kinds {
        let src = format!("package P {{ {kw} def X; }}");
        let body = package_body(&src);
        let MemberKind::Definition(d) = &body[0].kind else {
            panic!("no definition for {kw}")
        };
        assert_eq!(d.kind, expected, "keyword {kw}");
    }
}

#[test]
fn use_case_def_and_usage() {
    let body = package_body("package P { use case def Uc; }");
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    assert_eq!(d.kind, DefKind::UseCase);

    let unit = parse_source("package P { use case uc1 : Uc; }");
    let MemberKind::Package(p) = &unit.unit.members[0].kind else {
        panic!()
    };
    let MemberKind::Usage(u) = &p.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    assert_eq!(u.kind, UsageKind::UseCase);
}

#[test]
fn nested_definitions() {
    let body = package_body(
        "package P {
            part def Vehicle {
                part def Engine;
                part eng : Engine;
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let inner = d.body.as_ref().unwrap();
    assert!(matches!(&inner[0].kind, MemberKind::Definition(e) if e.kind == DefKind::Part));
    assert!(matches!(&inner[1].kind, MemberKind::Usage(u) if u.kind == UsageKind::Part));
}

// ---------------------------------------------------------------------------
// Usages
// ---------------------------------------------------------------------------

fn first_usage(src: &str) -> Usage {
    let body = package_body(src);
    match body.into_iter().next().unwrap().kind {
        MemberKind::Usage(u) => u,
        other => panic!("expected usage, got {other:?}"),
    }
}

#[test]
fn typed_usage_with_multiplicity() {
    let u = first_usage("package P { part wheels : Wheel[4] ordered nonunique; }");
    assert_eq!(u.kind, UsageKind::Part);
    assert_eq!(u.declaration.id.name.as_ref().unwrap().value, "wheels");
    let FeatureSpecialization::TypedBy(types) = &u.declaration.specializations[0] else {
        panic!()
    };
    assert!(matches!(&types[0].target, TargetRef::Name(qn) if qn.to_display_string() == "Wheel"));
    let mult = u.declaration.multiplicity.as_ref().unwrap();
    assert!(mult.lower.is_none());
    assert!(matches!(&mult.upper.kind, ExprKind::Literal(Literal::Integer(n)) if n == "4"));
    assert!(u.declaration.is_ordered && u.declaration.is_nonunique);
}

#[test]
fn multiplicity_range_with_star() {
    let u = first_usage("package P { part p : T[0..*]; }");
    let mult = u.declaration.multiplicity.as_ref().unwrap();
    assert!(matches!(
        mult.lower.as_ref().unwrap().kind,
        ExprKind::Literal(Literal::Integer(_))
    ));
    assert!(matches!(
        mult.upper.kind,
        ExprKind::Literal(Literal::Infinity)
    ));
}

#[test]
fn subsets_redefines_references() {
    let u = first_usage("package P { part fl :> wheels :>> baseWheel ::> hub; }");
    assert_eq!(u.declaration.specializations.len(), 3);
    assert!(matches!(
        u.declaration.specializations[0],
        FeatureSpecialization::Subsets(_)
    ));
    assert!(matches!(
        u.declaration.specializations[1],
        FeatureSpecialization::Redefines(_)
    ));
    assert!(matches!(
        u.declaration.specializations[2],
        FeatureSpecialization::References(_)
    ));
}

#[test]
fn keyword_synonyms() {
    let u =
        first_usage("package P { part fl defined by Wheel subsets wheels redefines baseWheel; }");
    assert_eq!(u.declaration.specializations.len(), 3);
    assert!(matches!(
        u.declaration.specializations[0],
        FeatureSpecialization::TypedBy(_)
    ));
}

#[test]
fn feature_chain_targets() {
    let u = first_usage("package P { ref r :> vehicle.engine.cylinder; }");
    let FeatureSpecialization::Subsets(targets) = &u.declaration.specializations[0] else {
        panic!()
    };
    let TargetRef::Chain(links) = &targets[0] else {
        panic!("expected chain")
    };
    assert_eq!(links.len(), 3);
}

#[test]
fn usage_prefixes() {
    let u = first_usage("package P { in derived abstract constant ref part x : T; }");
    assert_eq!(u.prefix.direction, Some(FeatureDirection::In));
    assert!(u.prefix.is_derived && u.prefix.is_abstract && u.prefix.is_constant && u.prefix.is_ref);
}

#[test]
fn end_and_portion_usages() {
    let u = first_usage("package P { end part e : T; }");
    assert!(u.prefix.is_end);

    let u = first_usage("package P { timeslice t :> occ; }");
    assert_eq!(u.prefix.portion, Some(PortionKind::Timeslice));
    assert_eq!(u.kind, UsageKind::Occurrence);

    let u = first_usage("package P { individual snapshot s : X; }");
    assert!(u.prefix.is_individual);
    assert_eq!(u.prefix.portion, Some(PortionKind::Snapshot));
}

#[test]
fn keyword_less_usage() {
    let u = first_usage("package P { x : Real = 42; }");
    assert_eq!(u.kind, UsageKind::Default);
    assert_eq!(u.value.as_ref().unwrap().kind, ValueKind::Bound);
}

#[test]
fn conjugated_port_typing() {
    let u = first_usage("package P { port p : ~PowerPort; }");
    let FeatureSpecialization::TypedBy(types) = &u.declaration.specializations[0] else {
        panic!()
    };
    assert!(types[0].is_conjugated);
}

#[test]
fn value_kinds() {
    for (src, expected) in [
        ("package P { attribute a : Real = 1; }", ValueKind::Bound),
        ("package P { attribute a : Real := 1; }", ValueKind::Initial),
        (
            "package P { attribute a : Real default = 1; }",
            ValueKind::Default,
        ),
        (
            "package P { attribute a : Real default 1; }",
            ValueKind::Default,
        ),
        (
            "package P { attribute a : Real default := 1; }",
            ValueKind::DefaultInitial,
        ),
    ] {
        let u = first_usage(src);
        assert_eq!(u.value.unwrap().kind, expected, "{src}");
    }
}

#[test]
fn variant_member() {
    let body = package_body(
        "package P {
            variation part def W {
                variant part w18 : W;
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let MemberKind::Usage(u) = &d.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    assert!(u.prefix.is_variant);
}

#[test]
fn enum_def_with_bare_values() {
    let body = package_body(
        "package P {
            enum def SignalKind {
                mid;
                caution;
                halt;
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    assert_eq!(d.kind, DefKind::Enum);
    let values = d.body.as_ref().unwrap();
    assert_eq!(values.len(), 3);
    assert!(
        values
            .iter()
            .all(|m| matches!(&m.kind, MemberKind::Usage(u) if u.kind == UsageKind::Default))
    );
}

// ---------------------------------------------------------------------------
// Expressions
// ---------------------------------------------------------------------------

fn value_expr(src_expr: &str) -> Expr {
    let src = format!("package P {{ attribute a = {src_expr}; }}");
    let u = first_usage(&src);
    u.value.unwrap().expr
}

#[test]
fn literals() {
    assert!(matches!(
        value_expr("true").kind,
        ExprKind::Literal(Literal::Bool(true))
    ));
    assert!(
        matches!(value_expr("42").kind, ExprKind::Literal(Literal::Integer(ref n)) if n == "42")
    );
    assert!(
        matches!(value_expr("1.5").kind, ExprKind::Literal(Literal::Real(ref r)) if r == "1.5")
    );
    assert!(
        matches!(value_expr("1.5e-3").kind, ExprKind::Literal(Literal::Real(ref r)) if r == "1.5e-3")
    );
    assert!(
        matches!(value_expr("2e10").kind, ExprKind::Literal(Literal::Real(ref r)) if r == "2e10")
    );
    assert!(
        matches!(value_expr(r#""hi""#).kind, ExprKind::Literal(Literal::String(ref s)) if s == "hi")
    );
    assert!(matches!(value_expr("null").kind, ExprKind::Null));
    assert!(matches!(value_expr("()").kind, ExprKind::Null));
}

#[test]
fn precedence_additive_multiplicative() {
    // 1 + 2 * 3 => 1 + (2 * 3)
    let ExprKind::Binary {
        op: BinaryOp::Add,
        rhs,
        ..
    } = value_expr("1 + 2 * 3").kind
    else {
        panic!()
    };
    assert!(matches!(
        rhs.kind,
        ExprKind::Binary {
            op: BinaryOp::Mul,
            ..
        }
    ));
}

#[test]
fn exponentiation_is_right_associative() {
    // 2 ** 3 ** 2 => 2 ** (3 ** 2)
    let ExprKind::Binary {
        op: BinaryOp::Pow,
        rhs,
        ..
    } = value_expr("2 ** 3 ** 2").kind
    else {
        panic!()
    };
    assert!(matches!(
        rhs.kind,
        ExprKind::Binary {
            op: BinaryOp::Pow,
            ..
        }
    ));
}

#[test]
fn unary_binds_tighter_than_exponentiation() {
    // -2 ** 3 parses as (-2) ** 3 per the grammar.
    let ExprKind::Binary {
        op: BinaryOp::Pow,
        lhs,
        ..
    } = value_expr("-2 ** 3").kind
    else {
        panic!()
    };
    assert!(matches!(
        lhs.kind,
        ExprKind::Unary {
            op: UnaryOp::Minus,
            ..
        }
    ));
}

#[test]
fn logical_chain() {
    // a or b and c => or(a, and(b, c)) — `and` binds tighter.
    let ExprKind::Binary {
        op: BinaryOp::CondOr,
        rhs,
        ..
    } = value_expr("a or b and c").kind
    else {
        panic!()
    };
    assert!(matches!(
        rhs.kind,
        ExprKind::Binary {
            op: BinaryOp::CondAnd,
            ..
        }
    ));
}

#[test]
fn implies_and_null_coalescing() {
    let e = value_expr("x ?? y implies z");
    // implies is lower: (x ?? y) implies z... no — ?? is *lower* than implies
    // per the grammar (NullCoalescing contains Implies).
    let ExprKind::Binary {
        op: BinaryOp::NullCoalescing,
        rhs,
        ..
    } = e.kind
    else {
        panic!("expected ?? at top: {e:?}")
    };
    assert!(matches!(
        rhs.kind,
        ExprKind::Binary {
            op: BinaryOp::Implies,
            ..
        }
    ));
}

#[test]
fn conditional_expression() {
    let ExprKind::Conditional { cond, .. } = value_expr("if x > 1 ? a else b").kind else {
        panic!()
    };
    assert!(matches!(
        cond.kind,
        ExprKind::Binary {
            op: BinaryOp::Gt,
            ..
        }
    ));
}

#[test]
fn range_expression() {
    assert!(matches!(
        value_expr("1..n").kind,
        ExprKind::Binary {
            op: BinaryOp::Range,
            ..
        }
    ));
}

#[test]
fn classification_and_cast() {
    let ExprKind::Classification { op, operand, .. } = value_expr("v istype Vehicle").kind else {
        panic!()
    };
    assert_eq!(op, ClassificationOp::IsType);
    assert!(operand.is_some());

    let ExprKind::Classification { op, operand, .. } = value_expr("@Safety").kind else {
        panic!()
    };
    assert_eq!(op, ClassificationOp::AtType);
    assert!(operand.is_none());

    assert!(matches!(
        value_expr("x as Integer").kind,
        ExprKind::Classification {
            op: ClassificationOp::As,
            ..
        }
    ));
}

#[test]
fn classification_chains() {
    // A cast result can itself be classified: implicit-self
    // `as T istype U` …
    let ExprKind::Classification { op, operand, .. } =
        value_expr("as Definition istype Definition").kind
    else {
        panic!()
    };
    assert_eq!(op, ClassificationOp::IsType);
    let inner = operand.expect("cast operand");
    let ExprKind::Classification { op, operand, .. } = inner.kind else {
        panic!()
    };
    assert_eq!(op, ClassificationOp::As);
    assert!(operand.is_none());

    // … and with an explicit operand.
    let ExprKind::Classification { op, operand, .. } =
        value_expr("v as Connection hastype Connection").kind
    else {
        panic!()
    };
    assert_eq!(op, ClassificationOp::HasType);
    assert!(matches!(
        operand.expect("cast operand").kind,
        ExprKind::Classification {
            op: ClassificationOp::As,
            operand: Some(_),
            ..
        }
    ));
}

#[test]
fn multiplicity_parenthesized_sequence_bound() {
    // Interop: cardinality choices as a parenthesized
    // sequence bound.
    let body = package_body("package P { part p[(0, 2, 4)]; part a[(1, 2)] : A; }");
    let mults: Vec<_> = body
        .iter()
        .filter_map(|m| match &m.kind {
            MemberKind::Usage(u) => u.declaration.multiplicity.as_ref(),
            _ => None,
        })
        .collect();
    assert_eq!(mults.len(), 2);
    assert!(matches!(&mults[0].upper.kind, ExprKind::Sequence(items) if items.len() == 3));
    assert!(mults[0].lower.is_none());
}

#[test]
fn filter_with_classification_chain() {
    let body = package_body(
        "package P { filter as Definition istype Definition; filter (as C hastype C or @M); }",
    );
    let filters: Vec<_> = body
        .iter()
        .filter(|m| matches!(m.kind, MemberKind::Filter(_)))
        .collect();
    assert_eq!(filters.len(), 2);
}

#[test]
fn feature_chains_and_invocations() {
    assert!(matches!(
        value_expr("engine.cylinders").kind,
        ExprKind::ChainStep { .. }
    ));

    let ExprKind::Invocation { args, .. } = value_expr("TotalMass(parts, 3)").kind else {
        panic!()
    };
    assert_eq!(args.len(), 2);

    let ExprKind::Invocation { args, .. } = value_expr("Point(x = 1, y = 2)").kind else {
        panic!()
    };
    assert!(args.iter().all(|a| a.name.is_some()));
}

#[test]
fn arrow_and_body_expressions() {
    let ExprKind::Arrow { args, .. } = value_expr("list->select {in x; x > 1}").kind else {
        panic!()
    };
    let ArrowArgs::Body(body) = args else {
        panic!()
    };
    let ExprKind::Body { members } = body.kind else {
        panic!()
    };
    // One `in` parameter member and one result-expression member.
    assert_eq!(members.len(), 2);
    assert!(matches!(
        &members[0].kind,
        MemberKind::Usage(u) if u.prefix.direction == Some(FeatureDirection::In)
    ));
    assert!(matches!(&members[1].kind, MemberKind::Result(_)));

    assert!(matches!(
        value_expr("s->including(4)").kind,
        ExprKind::Arrow {
            args: ArrowArgs::List(_),
            ..
        }
    ));
}

#[test]
fn body_expression_with_typed_params_and_members() {
    // SysML expression bodies are full calculation bodies.
    let e = value_expr(
        "(1..n-1)->forAll {in i : Integer; \
            private s : Rec = samples#(i); \
            s.t > 0}",
    );
    let ExprKind::Arrow {
        args: ArrowArgs::Body(body),
        ..
    } = e.kind
    else {
        panic!()
    };
    let ExprKind::Body { members } = body.kind else {
        panic!()
    };
    assert_eq!(members.len(), 3);
    assert_eq!(members[1].visibility, Some(Visibility::Private));
    assert!(matches!(&members[2].kind, MemberKind::Result(_)));
}

#[test]
fn collect_select_index() {
    assert!(matches!(
        value_expr("parts.{in p; p.mass}").kind,
        ExprKind::Collect { .. }
    ));
    assert!(matches!(
        value_expr("parts.?{in p; p.m > 1}").kind,
        ExprKind::Select { .. }
    ));
    assert!(matches!(value_expr("row#(2)").kind, ExprKind::Index { .. }));
    assert!(matches!(
        value_expr("10 [SI::kg]").kind,
        ExprKind::Bracket { .. }
    ));
}

#[test]
fn constructor_and_metadata_access() {
    assert!(matches!(
        value_expr("new Pt(1, 2)").kind,
        ExprKind::Constructor { .. }
    ));
    assert!(matches!(
        value_expr("x.metadata").kind,
        ExprKind::MetadataAccess { .. }
    ));
    let ExprKind::MetadataAccess { target } = value_expr("P::Q::x.metadata").kind else {
        panic!()
    };
    assert_eq!(target.to_display_string(), "P::Q::x");
    // A left operand that is not an element reference is diagnosed, and the
    // operand itself survives in the tree.
    let Parse { unit, diagnostics } = parse_source("package P { attribute a = (1 + 2).metadata; }");
    assert!(
        diagnostics
            .iter()
            .any(|d| d.message.contains("element reference")),
        "{diagnostics:#?}"
    );
    let MemberKind::Package(pkg) = &unit.members[0].kind else {
        panic!()
    };
    let MemberKind::Usage(u) = &pkg.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    assert!(matches!(
        u.value.as_ref().unwrap().expr.kind,
        ExprKind::Binary { .. }
    ));
}

#[test]
fn sequence_expression() {
    let ExprKind::Sequence(items) = value_expr("(1, 2, 3)").kind else {
        panic!()
    };
    assert_eq!(items.len(), 3);
    // Trailing comma allowed.
    let ExprKind::Sequence(items) = value_expr("(1, 2,)").kind else {
        panic!()
    };
    assert_eq!(items.len(), 2);
}

// ---------------------------------------------------------------------------
// Connectors, flows, allocations, bindings
// ---------------------------------------------------------------------------

#[test]
fn connection_with_connect_part() {
    let u = first_usage(
        "package P { connection c : DriveJoint connect frontAxle.hub to frontWheel.mount; }",
    );
    assert_eq!(u.kind, UsageKind::Connection);
    let UsageDetail::Connector { ends } = &u.detail else {
        panic!()
    };
    assert_eq!(ends.len(), 2);
    assert!(matches!(&ends[0].target, TargetRef::Chain(links) if links.len() == 2));
}

#[test]
fn standalone_connect_and_nary() {
    let u = first_usage("package P { connect a to b; }");
    assert_eq!(u.kind, UsageKind::Connection);

    let u = first_usage("package P { connect (a, b, c); }");
    let UsageDetail::Connector { ends } = &u.detail else {
        panic!()
    };
    assert_eq!(ends.len(), 3);

    let direct = first_usage("package P { interface (a, b, c); }");
    let declared = first_usage("package P { interface connect (a, b, c); }");
    assert_eq!(direct.kind, UsageKind::Interface);
    let UsageDetail::Connector { ends } = &direct.detail else {
        panic!()
    };
    assert_eq!(ends.len(), 3);
    let UsageDetail::Connector {
        ends: declared_ends,
    } = &declared.detail
    else {
        panic!()
    };
    let names = |ends: &[ConnectorEnd]| {
        ends.iter()
            .map(|end| match &end.target {
                TargetRef::Name(qn) => qn.to_display_string(),
                TargetRef::Chain(_) => panic!(),
            })
            .collect::<Vec<_>>()
    };
    assert_eq!(names(ends), names(declared_ends));
}

#[test]
fn connector_end_with_name_and_multiplicity() {
    let u = first_usage("package P { connect [1] mount ::> axle.hub to [4] w ::> wheel; }");
    let UsageDetail::Connector { ends } = &u.detail else {
        panic!()
    };
    assert_eq!(ends[0].name.as_ref().unwrap().value, "mount");
    assert!(ends[0].multiplicity.is_some());
}

#[test]
fn binding_and_bind() {
    let u = first_usage("package P { bind seat.occupant = driver; }");
    assert_eq!(u.kind, UsageKind::Binding);
    let UsageDetail::Binding { ends } = &u.detail else {
        panic!()
    };
    assert_eq!(ends.len(), 2);

    let u = first_usage("package P { binding fuelBinding bind tank.fuelOut = engine.fuelIn; }");
    assert_eq!(u.declaration.id.name.as_ref().unwrap().value, "fuelBinding");
}

#[test]
fn allocation_and_allocate() {
    let u = first_usage("package P { allocate logical.fn to physical.cpu; }");
    assert_eq!(u.kind, UsageKind::Allocation);
    let u = first_usage("package P { allocation a : A allocate x to y; }");
    assert!(matches!(u.detail, UsageDetail::Connector { .. }));
}

#[test]
fn flow_declarations() {
    let u = first_usage("package P { flow of Fuel from tank.fuelOut to engine.fuelIn; }");
    assert_eq!(u.kind, UsageKind::Flow);
    let UsageDetail::Flow {
        payload,
        source,
        target,
    } = &u.detail
    else {
        panic!()
    };
    assert!(payload.is_some());
    assert!(source.is_some() && target.is_some());

    // Shorthand and named forms.
    let u = first_usage("package P { flow tank.fuelOut to engine.fuelIn; }");
    assert!(matches!(
        &u.detail,
        UsageDetail::Flow {
            source: Some(_),
            ..
        }
    ));
    let u = first_usage("package P { flow f : FuelFlow; }");
    assert!(matches!(u.detail, UsageDetail::None));
}

#[test]
fn succession_flow_and_message() {
    let u = first_usage("package P { succession flow focus.result to shoot.scene; }");
    assert_eq!(u.kind, UsageKind::SuccessionFlow);

    let u = first_usage("package P { message of Order from buyer to seller; }");
    assert_eq!(u.kind, UsageKind::Message);
}

#[test]
fn interface_with_ends() {
    let body = package_body(
        "package P {
            interface def WaterDelivery {
                end suppliedBy : Spigot;
                end deliveredTo : Faucet;
            }
            interface w : WaterDelivery connect supplier.spigot to consumer.faucet;
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let ends = d.body.as_ref().unwrap();
    assert!(matches!(&ends[0].kind, MemberKind::Usage(u) if u.prefix.is_end));
    let MemberKind::Usage(u) = &body[1].kind else {
        panic!()
    };
    assert!(matches!(u.detail, UsageDetail::Connector { .. }));
}

#[test]
fn end_with_cross_feature() {
    let u = first_usage("package P { end [0..1] item cart : ShoppingCart[1]; }");
    assert!(u.prefix.is_end);
    assert!(u.prefix.end_cross.is_some());
    assert_eq!(u.kind, UsageKind::Item);

    let u = first_usage("package P { end inCart[0..1] item cart : ShoppingCart[1]; }");
    let cross = u.prefix.end_cross.as_ref().unwrap();
    assert_eq!(cross.decl.id.name.as_ref().unwrap().value, "inCart");

    // A cross feature needs no multiplicity, and may carry its own basic
    // prefix (`ref`, direction, `derived`, …) distinct from the end usage's.
    let u = first_usage("package P { end inCart : InCart item cart : ShoppingCart; }");
    let cross = u.prefix.end_cross.as_ref().unwrap();
    assert_eq!(cross.decl.id.name.as_ref().unwrap().value, "inCart");

    let u = first_usage("package P { end derived ref inCart[0..1] part cart : C; }");
    assert!(u.prefix.is_end);
    assert!(!u.prefix.is_derived);
    assert!(!u.prefix.is_ref);
    let cross = u.prefix.end_cross.as_ref().unwrap();
    assert!(cross.is_derived);
    assert!(cross.is_ref);

    // Without a following kind keyword there is no cross feature: the
    // declaration belongs to the end usage itself.
    let u = first_usage("package P { end ref x : C; }");
    assert!(u.prefix.end_cross.is_none());
    assert!(u.prefix.is_ref);
    assert_eq!(u.declaration.id.name.as_ref().unwrap().value, "x");
}

// ---------------------------------------------------------------------------
// Actions, states, transitions
// ---------------------------------------------------------------------------

#[test]
fn action_body_successions() {
    let body = package_body(
        "package P {
            action def Brake {
                first start;
                then action a1 : A;
                first a1 then a2;
                action a2 : A;
                then done;
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let items = d.body.as_ref().unwrap();
    assert!(
        matches!(&items[0].kind, MemberKind::InitialNode(qn) if qn.to_display_string() == "start")
    );
    assert!(items[1].leading_then, "leading `then` before action member");
    assert!(matches!(&items[2].kind, MemberKind::Usage(u) if u.kind == UsageKind::Succession));
    assert!(matches!(&items[4].kind, MemberKind::Usage(u) if u.kind == UsageKind::Succession));
}

#[test]
fn member_prefixed_target_succession_source_multiplicity() {
    let body = package_body(
        "package P {
            action def A {
                private [1] then next;
            }
        }",
    );
    let MemberKind::Definition(action) = &body[0].kind else {
        panic!()
    };
    let member = &action.body.as_ref().unwrap()[0];
    assert_eq!(member.visibility, Some(Visibility::Private));
    let MemberKind::Usage(succession) = &member.kind else {
        panic!()
    };
    let UsageDetail::Succession {
        source: Some(source),
        target,
    } = &succession.detail
    else {
        panic!()
    };
    assert!(source.multiplicity.is_some());
    assert!(source.target.is_unspelled());
    assert!(matches!(&target.target, TargetRef::Name(qn) if qn.to_display_string() == "next"));
}

/// The reference of an end the text does not spell has a name of its own,
/// is recognised by it, and carries no span because it covers no text.
#[test]
fn an_unspelled_reference_is_named_and_spanless() {
    let unspelled = TargetRef::unspelled();
    assert!(unspelled.is_unspelled());
    assert_eq!(unspelled.span(), sysmlv2_parser::Span::default());
    let spelled = first_usage("package P { connect a to b; }");
    let UsageDetail::Connector { ends } = &spelled.detail else {
        panic!()
    };
    assert!(ends.iter().all(|e| !e.target.is_unspelled()));
}

#[test]
fn perform_and_event_forms() {
    let u = first_usage("package P { perform takePicture.focus; }");
    assert_eq!(u.kind, UsageKind::Perform);
    assert!(matches!(
        &u.declaration.specializations[0],
        FeatureSpecialization::References(TargetRef::Chain(_))
    ));

    let u = first_usage("package P { perform action focus : Focus; }");
    assert_eq!(u.declaration.id.name.as_ref().unwrap().value, "focus");

    let u = first_usage("package P { event occurrence launch; }");
    assert_eq!(u.kind, UsageKind::Event);
}

#[test]
fn accept_send_assign_terminate() {
    let u = first_usage("package P { action a { accept sig : Signal via port1; } }");
    let MemberKind::Usage(a) = &u.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    assert_eq!(a.kind, UsageKind::Accept);
    let UsageDetail::Accept { via, .. } = &a.detail else {
        panic!()
    };
    assert!(via.is_some());

    let u = first_usage("package P { action a { accept when temperature > 90; } }");
    let MemberKind::Usage(a) = &u.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    let UsageDetail::Accept { trigger, .. } = &a.detail else {
        panic!()
    };
    assert_eq!(trigger.as_ref().unwrap().kind, TriggerKind::When);

    let u = first_usage("package P { action a { accept sig at clock; } }");
    let MemberKind::Usage(a) = &u.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    let UsageDetail::Accept {
        payload, trigger, ..
    } = &a.detail
    else {
        panic!()
    };
    assert_eq!(payload.id.name.as_ref().unwrap().value, "sig");
    assert!(payload.specializations.is_empty());
    assert_eq!(trigger.as_ref().unwrap().kind, TriggerKind::At);

    let u = first_usage("package P { action a { send Ping() via chan to receiver; } }");
    let MemberKind::Usage(s) = &u.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    let UsageDetail::Send { payload, via, to } = &s.detail else {
        panic!()
    };
    assert!(payload.is_some() && via.is_some() && to.is_some());

    let u = first_usage("package P { action a { assign x.count := x.count + 1; } }");
    let MemberKind::Usage(s) = &u.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    assert_eq!(s.kind, UsageKind::Assign);

    let u = first_usage("package P { action a { terminate self; } }");
    let MemberKind::Usage(t) = &u.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    assert_eq!(t.kind, UsageKind::Terminate);
}

#[test]
fn control_and_structured_nodes() {
    let u = first_usage(
        "package P {
            action a {
                fork f1;
                join j1;
                merge m1;
                decide d1;
                if x > 1 { action inner; } else { action other; }
                while not done { perform work; } until x > 10;
                for i : Integer in 1..10 { send Tick() to t; }
            }
        }",
    );
    let items = u.body.as_ref().unwrap();
    let kinds: Vec<_> = items
        .iter()
        .filter_map(|m| match &m.kind {
            MemberKind::Usage(u) => Some(u.kind),
            _ => None,
        })
        .collect();
    assert_eq!(
        kinds,
        vec![
            UsageKind::Fork,
            UsageKind::Join,
            UsageKind::Merge,
            UsageKind::Decide,
            UsageKind::IfNode,
            UsageKind::WhileLoop,
            UsageKind::ForLoop
        ]
    );
}

#[test]
fn nested_if_node_action_prefix_shape() {
    let body = package_body(
        "package P {
            action def A {
                if true { } else individual action nested if false { }
            }
        }",
    );
    let MemberKind::Definition(action) = &body[0].kind else {
        panic!()
    };
    let MemberKind::Usage(outer_if) = &action.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    let UsageDetail::IfNode {
        else_body: Some(inner_if),
        ..
    } = &outer_if.detail
    else {
        panic!()
    };
    assert_eq!(inner_if.kind, UsageKind::IfNode);
    assert!(inner_if.prefix.is_individual);
    assert_eq!(
        inner_if.declaration.id.name.as_ref().unwrap().value,
        "nested"
    );
}

#[test]
fn state_machine() {
    let body = package_body(
        "package P {
            state def Operating parallel {
                entry action init;
                do action monitor;
                exit;
                state off;
                transition off_to_on
                    first off
                    accept SwitchOn
                    if power > 0
                    then on;
                state on;
                exhibit powerState;
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let items = d.body.as_ref().unwrap();
    assert!(matches!(
        &items[0].kind,
        MemberKind::StateSubaction {
            kind: StateSubactionKind::Entry,
            action: Some(_)
        }
    ));
    assert!(matches!(
        &items[2].kind,
        MemberKind::StateSubaction {
            kind: StateSubactionKind::Exit,
            action: None
        }
    ));
    let MemberKind::Usage(t) = &items[4].kind else {
        panic!()
    };
    assert_eq!(t.kind, UsageKind::Transition);
    let UsageDetail::Transition {
        source,
        trigger,
        guard,
        target,
        ..
    } = &t.detail
    else {
        panic!()
    };
    assert!(source.is_some() && trigger.is_some() && guard.is_some() && target.is_some());
    let MemberKind::Usage(ex) = &items[6].kind else {
        panic!()
    };
    assert_eq!(ex.kind, UsageKind::Exhibit);
}

#[test]
fn target_transition_shorthands() {
    let body = package_body(
        "package P {
            state def S {
                state s1;
                if go then s2;
                else s3;
                state s2;
                state s3;
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let items = d.body.as_ref().unwrap();
    let MemberKind::Usage(t1) = &items[1].kind else {
        panic!()
    };
    assert!(matches!(
        &t1.detail,
        UsageDetail::Transition { guard: Some(_), .. }
    ));
    let MemberKind::Usage(t2) = &items[2].kind else {
        panic!()
    };
    assert!(matches!(
        &t2.detail,
        UsageDetail::Transition {
            is_default: true,
            ..
        }
    ));
}

// ---------------------------------------------------------------------------
// Calculations, constraints, requirements, cases
// ---------------------------------------------------------------------------

#[test]
fn calculation_with_return_and_result() {
    let body = package_body(
        "package P {
            calc def TotalMass {
                in parts : Part[0..*];
                return : MassValue;
                sum(parts.mass)
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let items = d.body.as_ref().unwrap();
    assert!(matches!(&items[1].kind, MemberKind::Return(_)));
    assert!(matches!(&items[2].kind, MemberKind::Result(_)));
}

#[test]
fn constraint_with_result_expression() {
    let body = package_body("package P { constraint massLimit { mass <= maxMass } }");
    let MemberKind::Usage(c) = &body[0].kind else {
        panic!()
    };
    assert!(matches!(
        &c.body.as_ref().unwrap()[0].kind,
        MemberKind::Result(_)
    ));
}

#[test]
fn assert_constraint_forms() {
    let u = first_usage("package P { assert constraint c { x > 0 } }");
    assert_eq!(u.kind, UsageKind::AssertConstraint);
    let u = first_usage("package P { assert not violated; }");
    assert!(matches!(u.detail, UsageDetail::Assert { negated: true }));
}

#[test]
fn requirement_members() {
    let body = package_body(
        "package P {
            requirement def MassReq {
                subject vehicle : Vehicle;
                actor driver;
                stakeholder customer;
                assume constraint { fuel > 0 }
                require constraint { mass <= limit }
                frame concern safety;
                verify parentReq;
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let items = d.body.as_ref().unwrap();
    assert!(matches!(&items[0].kind, MemberKind::Subject(_)));
    assert!(matches!(&items[1].kind, MemberKind::Actor(_)));
    assert!(matches!(&items[2].kind, MemberKind::Stakeholder(_)));
    assert!(matches!(
        &items[3].kind,
        MemberKind::RequirementConstraint {
            kind: RequirementConstraintKind::Assumption,
            ..
        }
    ));
    assert!(matches!(
        &items[4].kind,
        MemberKind::RequirementConstraint {
            kind: RequirementConstraintKind::Requirement,
            ..
        }
    ));
    assert!(matches!(&items[5].kind, MemberKind::FramedConcern(_)));
    assert!(matches!(
        &items[6].kind,
        MemberKind::RequirementVerification(_)
    ));
}

#[test]
fn satisfy_forms() {
    let u = first_usage("package P { satisfy massRequirement by vehicle_c1; }");
    assert_eq!(u.kind, UsageKind::Satisfy);
    let UsageDetail::Satisfy { by, negated, .. } = &u.detail else {
        panic!()
    };
    assert!(by.is_some() && !negated);

    let u = first_usage("package P { assert not satisfy r1 by p; }");
    assert!(matches!(
        &u.detail,
        UsageDetail::Satisfy {
            asserted: true,
            negated: true,
            ..
        }
    ));
    let u = first_usage("package P { not satisfy r2 by q; }");
    assert!(matches!(
        &u.detail,
        UsageDetail::Satisfy { negated: true, .. }
    ));
}

#[test]
fn case_members_and_include() {
    let body = package_body(
        "package P {
            use case def Drive {
                subject v : Vehicle;
                objective { require constraint { arrived } }
                include use case park;
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let items = d.body.as_ref().unwrap();
    assert!(matches!(&items[1].kind, MemberKind::Objective(_)));
    let MemberKind::Usage(inc) = &items[2].kind else {
        panic!()
    };
    assert_eq!(inc.kind, UsageKind::Include);
}

// ---------------------------------------------------------------------------
// Metadata, dependencies, views
// ---------------------------------------------------------------------------

#[test]
fn metadata_usage_and_prefix() {
    let body = package_body(
        r#"package P {
            metadata def Safety { level : Integer; }
            @Safety about Engine { level = 3; }
            #Safety part def Brake;
        }"#,
    );
    let MemberKind::Usage(m) = &body[1].kind else {
        panic!()
    };
    assert_eq!(m.kind, UsageKind::Metadata);
    let UsageDetail::Metadata { about } = &m.detail else {
        panic!()
    };
    assert_eq!(about.len(), 1);
    let MemberKind::Definition(d) = &body[2].kind else {
        panic!()
    };
    assert_eq!(d.prefix.metadata[0].to_display_string(), "Safety");
}

/// The single usage inside the metadata annotation of the first part in `P`.
fn metadata_body_usage(src: &str) -> Usage {
    let body = package_body(src);
    let MemberKind::Usage(part) = &body[1].kind else {
        panic!()
    };
    let MemberKind::Usage(meta) = &part.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    assert_eq!(meta.kind, UsageKind::Metadata);
    let MemberKind::Usage(inner) = &meta.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    inner.clone()
}

#[test]
fn metadata_body_implicit_redefinition() {
    // SysML.xtext `MetadataBodyUsage`: `'ref'? (':>>'|'redefines')?
    // OwnedRedefinition …` — the redefines token is optional, so a leading
    // *qualified* name is an implicit redefinition target. All spellings
    // must produce the same declaration.
    let spellings = [
        "ref M::kind = 1;",
        "M::kind = 1;",
        ":>> M::kind = 1;",
        "redefines M::kind = 1;",
        "ref :>> M::kind = 1;",
    ];
    for spelling in spellings {
        let u = metadata_body_usage(&format!(
            "package P {{
                metadata def M {{ kind : Integer; }}
                part a {{ @M {{ {spelling} }} }}
            }}"
        ));
        assert!(u.declaration.id.is_empty(), "{spelling}: no declared name");
        assert_eq!(u.declaration.specializations.len(), 1, "{spelling}");
        let FeatureSpecialization::Redefines(targets) = &u.declaration.specializations[0] else {
            panic!(
                "{spelling}: expected a redefinition, got {:?}",
                u.declaration
            )
        };
        let [TargetRef::Name(qn)] = targets.as_slice() else {
            panic!("{spelling}")
        };
        assert_eq!(qn.to_display_string(), "M::kind", "{spelling}");
        assert!(u.value.is_some(), "{spelling}: value part");
    }
}

#[test]
fn metadata_body_owned_feature_chain_redefinition() {
    let u = metadata_body_usage(
        "package P {
            metadata def M;
            part a { @M { outer.inner = 1; } }
        }",
    );
    assert!(u.declaration.id.is_empty());
    let FeatureSpecialization::Redefines(targets) = &u.declaration.specializations[0] else {
        panic!()
    };
    let [TargetRef::Chain(links)] = targets.as_slice() else {
        panic!()
    };
    assert_eq!(links.len(), 2);
    assert_eq!(links[0].to_display_string(), "outer");
    assert_eq!(links[1].to_display_string(), "inner");
}

#[test]
fn metadata_body_nested_and_typed_redefinition() {
    // The nested body of a `MetadataBodyUsage` is itself a `MetadataBody`,
    // and a `FeatureSpecializationPart` may follow the implicit target.
    let u = metadata_body_usage(
        "package P {
            metadata def M { kind : Integer; sub : Integer; }
            part a { @M { M::kind : Integer { M::sub = 2; } } }
        }",
    );
    assert!(matches!(
        u.declaration.specializations[0],
        FeatureSpecialization::Redefines(_)
    ));
    assert!(matches!(
        u.declaration.specializations[1],
        FeatureSpecialization::TypedBy(_)
    ));
    let MemberKind::Usage(nested) = &u.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    let FeatureSpecialization::Redefines(targets) = &nested.declaration.specializations[0] else {
        panic!("nested metadata body member should be an implicit redefinition")
    };
    let [TargetRef::Name(qn)] = targets.as_slice() else {
        panic!()
    };
    assert_eq!(qn.to_display_string(), "M::sub");
}

#[test]
fn metadata_body_sequence_value_trailing_comma() {
    // The Verification-method idiom (SysML intro tutorial): a sequence
    // value with a trailing comma (KerMLExpressions `SequenceExpression`).
    let u = metadata_body_usage(
        "package P {
            metadata def M { kind : Integer; }
            part a { @M { ref M::kind = (1, 2,); } }
        }",
    );
    let ExprKind::Sequence(items) = &u.value.as_ref().unwrap().expr.kind else {
        panic!("expected a sequence value")
    };
    assert_eq!(items.len(), 2);
}

#[test]
fn metadata_body_simple_name_still_declares() {
    // A bare simple name keeps its existing parse: an identification,
    // not a redefinition target.
    let u = metadata_body_usage(
        "package P {
            metadata def M { kind : Integer; }
            part a { @M { kind = 1; } }
        }",
    );
    assert_eq!(u.declaration.id.name.as_ref().unwrap().value, "kind");
    assert!(u.declaration.specializations.is_empty());
}

#[test]
fn qualified_name_member_only_in_metadata_bodies() {
    // Outside metadata bodies the implicit-redefinition rule must not
    // apply: a qualified name is not a member declaration there…
    let parse = sysmlv2_parser::parser::parse_source("package P { part a { M::kind = 1; } }");
    assert!(!parse.diagnostics.is_empty());
    // …and a calc body's trailing qualified-name result expression still
    // parses as a result member.
    let body = package_body(
        "package P {
            calc def C { M::kind }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    assert!(matches!(
        d.body.as_ref().unwrap()[0].kind,
        MemberKind::Result(_)
    ));
}

#[test]
fn extended_definition_and_usage() {
    let body = package_body(
        "package P {
            #command def Focus;
            #command focus1 : Focus;
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    assert_eq!(d.kind, DefKind::Extended);
    let MemberKind::Usage(u) = &body[1].kind else {
        panic!()
    };
    assert_eq!(u.kind, UsageKind::Extended);
}

#[test]
fn dependency_member() {
    let body = package_body(
        "package P {
            dependency Use from 'Application Layer' to 'Service Layer';
            dependency from a to b, c;
            dependency x to y;
        }",
    );
    let MemberKind::Dependency(d) = &body[0].kind else {
        panic!()
    };
    assert_eq!(d.id.name.as_ref().unwrap().value, "Use");
    let MemberKind::Dependency(d) = &body[1].kind else {
        panic!()
    };
    assert_eq!(d.suppliers.len(), 2);
    let MemberKind::Dependency(d) = &body[2].kind else {
        panic!()
    };
    assert_eq!(d.clients[0].to_display_string(), "x");
}

#[test]
fn view_members() {
    let body = package_body(
        "package P {
            view def SafetyView {
                filter @Safety;
                render asTreeDiagram;
            }
            view v : SafetyView {
                expose Vehicle::*;
            }
        }",
    );
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!()
    };
    let items = d.body.as_ref().unwrap();
    assert!(matches!(&items[0].kind, MemberKind::Filter(_)));
    assert!(matches!(&items[1].kind, MemberKind::Render(_)));
    let MemberKind::Usage(v) = &body[1].kind else {
        panic!()
    };
    let MemberKind::Expose(exp) = &v.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    assert!(exp.is_namespace);
}

// ---------------------------------------------------------------------------
// Error handling and recovery
// ---------------------------------------------------------------------------

#[test]
fn error_recovery_continues_after_bad_member() {
    let Parse { unit, diagnostics } = parse_source(
        "package P {
            part good1 : T;
            part bad : ;
            part good2 : T;
        }",
    );
    assert!(!diagnostics.is_empty());
    let MemberKind::Package(p) = &unit.members[0].kind else {
        panic!()
    };
    let names: Vec<_> = p
        .body
        .as_ref()
        .unwrap()
        .iter()
        .filter_map(|m| match &m.kind {
            MemberKind::Usage(u) => u.declaration.id.name.as_ref().map(|n| n.value.clone()),
            _ => None,
        })
        .collect();
    assert!(names.contains(&"good1".to_string()));
    assert!(names.contains(&"good2".to_string()));
}

#[test]
fn reserved_word_needs_quoting() {
    // `part part;` is illegal (reserved), `part 'part';` is fine.
    let bad = parse_source("package P { part part; }");
    assert!(bad.has_errors());
    let good = parse_source("package P { part 'part'; }");
    assert!(!good.has_errors(), "{:?}", good.diagnostics);
}

#[test]
fn missing_semicolon_reported() {
    let p = parse_source("package P { part x : T }");
    assert!(p.has_errors());
}

#[test]
fn missing_semicolon_repair_keeps_both_members() {
    // The `;` missing at the end of a line is reported there (zero-width
    // span at the insertion point) and both the unterminated member and
    // the one on the next line survive in the tree.
    let src = "package P {\n    part q : D\n    part r : D;\n}";
    let Parse { unit, diagnostics } = parse_source(src);
    let errors: Vec<_> = diagnostics
        .iter()
        .filter(|d| d.severity == sysmlv2_parser::diag::Severity::Error)
        .collect();
    assert_eq!(errors.len(), 1, "{diagnostics:#?}");
    assert!(
        errors[0].message.contains("missing `;`"),
        "{diagnostics:#?}"
    );
    let end_of_line2 = src.find("part q : D").unwrap() + "part q : D".len();
    assert_eq!(errors[0].span.start as usize, end_of_line2);
    assert!(errors[0].span.is_empty());
    let MemberKind::Package(p) = &unit.members[0].kind else {
        panic!()
    };
    let body = p.body.as_ref().unwrap();
    let names: Vec<_> = body
        .iter()
        .filter_map(|m| match &m.kind {
            MemberKind::Usage(u) => u.declaration.id.name.as_ref().map(|n| n.value.clone()),
            _ => None,
        })
        .collect();
    assert_eq!(names, ["q", "r"], "both members kept");
}

#[test]
fn missing_semicolon_before_brace_defers_to_result_expression() {
    // `calc c { x }` keeps its trailing result expression — the repair
    // must not reinterpret it as an unterminated usage member — while a
    // keyword-led member before `}` is repaired in place.
    let ok = parse_source("package P { calc c {\n    x\n} }");
    assert!(!ok.has_errors(), "{:?}", ok.diagnostics);
    let repaired = parse_source("package P {\n    part def D {\n        part q : D\n    }\n}");
    let errors: Vec<_> = repaired
        .diagnostics
        .iter()
        .filter(|d| d.severity == sysmlv2_parser::diag::Severity::Error)
        .collect();
    assert_eq!(errors.len(), 1, "{:#?}", repaired.diagnostics);
    assert!(errors[0].message.contains("missing `;`"));
    let MemberKind::Package(p) = &repaired.unit.members[0].kind else {
        panic!()
    };
    let MemberKind::Definition(d) = &p.body.as_ref().unwrap()[0].kind else {
        panic!()
    };
    assert_eq!(d.body.as_ref().unwrap().len(), 1, "repaired member kept");
}

#[test]
fn spans_are_meaningful() {
    let src = "package P { part x : T; }";
    let Parse { unit, .. } = parse_source(src);
    let m = &unit.members[0];
    assert_eq!(m.span.slice(src), src.trim_end());
}

// ---------------------------------------------------------------------------
// Member-start lookahead
// ---------------------------------------------------------------------------

fn state_body(src: &str) -> Vec<Member> {
    let body = package_body(src);
    let MemberKind::Definition(d) = &body[0].kind else {
        panic!("expected a state definition, got {:?}", body[0].kind)
    };
    let MemberKind::Usage(s) = &d.body.as_ref().unwrap()[0].kind else {
        panic!("expected a state usage")
    };
    s.body.clone().expect("state body")
}

/// The lookahead that tells an accept *node* from the accept-transition
/// shorthand balances braces, so a trigger carrying a body-expression
/// argument keeps its `then` target, and it scans the whole member, so a
/// trigger of any length does too.
#[test]
fn accept_transition_shorthand_keeps_its_target() {
    let items = state_body(
        "package P {
            state def S {
                state s1 {
                    accept sig when xs->exists { in x; x > 0 } then s2;
                }
                state s2;
            }
        }",
    );
    assert_eq!(items.len(), 1, "{items:#?}");
    let MemberKind::Usage(t) = &items[0].kind else {
        panic!("{:?}", items[0].kind)
    };
    assert_eq!(t.kind, UsageKind::Transition);
    let UsageDetail::Transition {
        trigger, target, ..
    } = &t.detail
    else {
        panic!()
    };
    assert!(trigger.is_some() && target.is_some());

    // A trigger far longer than any fixed scan window.
    let guard = (0..250)
        .map(|i| format!("a{i} > 0"))
        .collect::<Vec<_>>()
        .join(" and ");
    let items = state_body(&format!(
        "package P {{
            state def S {{
                state s1 {{
                    accept sig when {guard} then s2;
                }}
                state s2;
            }}
        }}"
    ));
    assert_eq!(items.len(), 1, "{items:#?}");
    let MemberKind::Usage(t) = &items[0].kind else {
        panic!("{:?}", items[0].kind)
    };
    assert_eq!(t.kind, UsageKind::Transition);

    // An accept node with a body is still a node, not a transition.
    let items = state_body(
        "package P {
            state def S {
                state s1 {
                    accept sig : Signal { assign x := 1; }
                }
            }
        }",
    );
    let MemberKind::Usage(a) = &items[0].kind else {
        panic!("{:?}", items[0].kind)
    };
    assert_eq!(a.kind, UsageKind::Accept);
    assert!(a.body.is_some());
}

/// A `{` that follows a complete trigger or payload expression opens the
/// accept node's own body and ends the lookahead, so a following member
/// starting with `then`, `if` or `do` is neither consumed nor able to turn
/// the node into a transition shorthand.
#[test]
fn accept_node_body_ends_the_lookahead() {
    fn action_body(src: &str) -> Vec<Member> {
        let body = package_body(src);
        let MemberKind::Usage(a) = &body[0].kind else {
            panic!("expected an action usage, got {:?}", body[0].kind)
        };
        a.body.clone().expect("action body")
    }

    for trigger in ["via p", "at t1", "when c", ": Signal"] {
        for tail in ["then b;", "if g then b;", "do b;"] {
            let src = format!(
                "package P {{ action a {{ accept sig {trigger} {{ }} {tail} action b; }} }}"
            );
            let items = action_body(&src);
            let MemberKind::Usage(node) = &items[0].kind else {
                panic!("{src}: {:?}", items[0].kind)
            };
            assert_eq!(node.kind, UsageKind::Accept, "{src}");
            assert!(node.body.is_some(), "{src}");
            // The tail and the following declaration both survive as their
            // own members.
            assert_eq!(items.len(), 3, "{src}: {items:#?}");
        }
    }
}

/// A trigger, a `via` clause and a payload's value are parsed as full
/// expressions, and a conditional is one of them: its `if` stands where an
/// operand is expected, so it opens the conditional rather than the guard
/// of the transition shorthand. The parenthesized and bare spellings
/// classify alike, and the guard that really is one still reads as a
/// guard.
#[test]
fn a_conditional_in_a_trigger_is_not_the_shorthands_guard() {
    fn only_member(src: &str) -> Usage {
        let items = state_body(src);
        assert_eq!(items.len(), 1, "{src}: {items:#?}");
        let MemberKind::Usage(u) = &items[0].kind else {
            panic!("{src}: {:?}", items[0].kind)
        };
        u.clone()
    }

    for trigger in [
        "when (if a ? b else c)",
        "when if a ? b else c",
        "when if a ? b else if c ? d else e",
        "via if a ? p else q",
        "when if g ? b else c",
    ] {
        let src = format!(
            "package P {{
                state def S {{
                    state s1 {{
                        accept sig : Sig {trigger};
                    }}
                    state s2;
                }}
            }}"
        );
        assert_eq!(only_member(&src).kind, UsageKind::Accept, "{src}");
    }

    // The shorthand's guard is still a guard — after a payload, after a
    // trigger expression, and after one that ends in a conditional.
    for head in [
        "accept sig : Sig if g",
        "accept sig when c if g",
        "accept sig when if a ? b else c if g",
    ] {
        let src = format!(
            "package P {{
                state def S {{
                    state s1 {{
                        {head} then s2;
                    }}
                    state s2;
                }}
            }}"
        );
        let member = only_member(&src);
        assert_eq!(member.kind, UsageKind::Transition, "{src}");
        let UsageDetail::Transition { guard, target, .. } = &member.detail else {
            panic!("{src}: {:?}", member.detail)
        };
        assert!(guard.is_some() && target.is_some(), "{src}");
    }
}

/// The word-spelled operators take an operand the way their symbolic
/// spellings do, and an expression may spell an operand as a body. A
/// brace after one therefore opens that operand, not the accept node's
/// own body — so the scan reads on to the `then` beyond it and classifies
/// the member as the transition it is.
#[test]
fn a_brace_after_a_word_operator_is_an_operand() {
    fn only_member(src: &str) -> Usage {
        let items = state_body(src);
        assert_eq!(items.len(), 1, "{src}: {items:#?}");
        let MemberKind::Usage(u) = &items[0].kind else {
            panic!("{src}: {:?}", items[0].kind)
        };
        u.clone()
    }

    fn state(member: &str) -> String {
        format!(
            "package P {{
                state def S {{
                    state s1 {{
                        {member}
                    }}
                    state s2;
                }}
            }}"
        )
    }

    for expr in [
        "a and { b }",
        "a or { b }",
        "a xor { b }",
        "a implies { b }",
        "not { b }",
    ] {
        let src = state(&format!("accept sig : Sig when {expr} then s2;"));
        let member = only_member(&src);
        assert_eq!(member.kind, UsageKind::Transition, "{src}");
        let UsageDetail::Transition {
            trigger, target, ..
        } = &member.detail
        else {
            panic!("{src}: {:?}", member.detail)
        };
        assert!(trigger.is_some() && target.is_some(), "{src}");

        // Without the tail the same head is the node itself, and its
        // own body still reads as a body.
        let src = state(&format!("accept sig : Sig when {expr};"));
        assert_eq!(only_member(&src).kind, UsageKind::Accept, "{src}");
        let src = state(&format!("accept sig : Sig when {expr} {{ action q; }}"));
        let member = only_member(&src);
        assert_eq!(member.kind, UsageKind::Accept, "{src}");
        assert!(member.body.is_some(), "{src}");
    }
}

/// The lookahead stops at the member it is classifying, so a body holding
/// many accept members costs time linear in its size rather than
/// quadratic — including when those members are malformed, which is when
/// a scan looking for a balanced terminator would run away.
///
/// Measured in tokens read rather than in wall-clock time: the count is
/// exactly the work the scan does, and does not depend on the machine.
///
/// A member that never closes its brace nests a body per member, so the
/// probe runs on a thread with room for the nesting bound itself — the
/// count it reads is kept per thread, so the parsing has to happen there
/// too.
#[test]
fn accept_lookahead_is_linear_in_the_body_size() {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(accept_lookahead_probe)
        .unwrap()
        .join()
        .unwrap();
}

fn accept_lookahead_probe() {
    fn lookahead_tokens(member: &str, count: usize) -> u64 {
        let members = (0..count)
            .map(|i| member.replace('#', &i.to_string()))
            .collect::<Vec<_>>()
            .join(" ");
        let src = format!("package P {{ action a {{ {members} }} }}");
        sysmlv2_parser::parser::take_accept_lookahead_tokens();
        let _ = parse_source(&src);
        sysmlv2_parser::parser::take_accept_lookahead_tokens()
    }

    for member in [
        // Well formed, and each shape of unbalanced opener: a member that
        // never closes its bracket, its parenthesis, or its brace.
        "accept sig# via p { }",
        "accept sig# when (x;",
        "accept sig# when x[1;",
        "accept sig# when { x;",
    ] {
        let small = lookahead_tokens(member, 1_000);
        let large = lookahead_tokens(member, 4_000);
        assert!(
            large <= small * 5,
            "{member:?}: 4000 members read {large} lookahead tokens \
             against {small} for 1000"
        );
    }

    // A well-formed member's classification reads its own tokens and no
    // more; a malformed one stops at its terminator all the same.
    for (member, ceiling) in [
        ("accept sig# via p { }", 8),
        ("accept sig# when (x;", 8),
        ("accept sig# when x[1;", 8),
    ] {
        let per_member = lookahead_tokens(member, 1_000) / 1_000;
        assert!(
            per_member <= ceiling,
            "{member:?} read {per_member} lookahead tokens per member"
        );
    }
}

/// Nested `else action { … }` levels are each parsed once: the branch is
/// decided by lookahead instead of by parsing a whole subtree and rolling
/// back, which cost one full re-parse of everything below per level.
#[test]
fn nested_else_action_bodies_parse_in_linear_time() {
    const DEPTH: usize = 8;
    const INNER_MEMBERS: usize = 3000;
    let innermost = (0..INNER_MEMBERS)
        .map(|i| format!("part p{i};"))
        .collect::<Vec<_>>()
        .join(" ");
    let mut nested = format!("if c {{ }} else action {{ {innermost} }}");
    for _ in 0..DEPTH {
        nested = format!("if c {{ }} else action {{ {nested} }}");
    }
    let src = format!("package P {{ action a {{ {nested} }} }}");
    let start = std::time::Instant::now();
    let body = package_body(&src);
    assert!(
        start.elapsed() < std::time::Duration::from_secs(3),
        "{DEPTH} nested else-action levels took {:?}",
        start.elapsed()
    );

    // The nesting is still what it says: each level is an if-node whose
    // else branch is an anonymous action body holding the next one.
    let MemberKind::Usage(action) = &body[0].kind else {
        panic!("{:?}", body[0].kind)
    };
    let mut members = action.body.clone().expect("action body");
    let mut level = 0;
    loop {
        let MemberKind::Usage(node) = &members[0].kind else {
            panic!("{:?}", members[0].kind)
        };
        assert_eq!(node.kind, UsageKind::IfNode);
        let UsageDetail::IfNode { else_body, .. } = &node.detail else {
            panic!()
        };
        let else_body = else_body.as_ref().expect("else branch");
        assert_eq!(else_body.kind, UsageKind::Action);
        members = else_body.body.clone().expect("else action body");
        level += 1;
        if members.len() == INNER_MEMBERS {
            break;
        }
    }
    assert_eq!(level, DEPTH + 1);
}

/// A declared nested if-node after `else` is still recognised through its
/// action head.
#[test]
fn else_action_declaration_before_if_is_a_nested_node() {
    let body = package_body("package P { action a { if c { } else action alt if d { } } }");
    let MemberKind::Usage(action) = &body[0].kind else {
        panic!()
    };
    let members = action.body.as_ref().unwrap();
    let MemberKind::Usage(node) = &members[0].kind else {
        panic!()
    };
    let UsageDetail::IfNode { else_body, .. } = &node.detail else {
        panic!()
    };
    let alt = else_body.as_ref().expect("else branch");
    assert_eq!(alt.kind, UsageKind::IfNode);
    assert_eq!(alt.declaration.id.name.as_ref().unwrap().value, "alt");
}

/// Syntax-tree nodes stay small. Every member of a body, every usage and
/// every expression is stored by value in a `Vec` and moved through the
/// parser's call chain, so one oversized payload — a multiplicity's two
/// expressions, an accept node's payload part — is paid for by every node
/// of that kind in the file and by every stack frame that carries one.
/// Ceilings are for a 64-bit target and leave a little room; a real
/// increase should be a deliberate one.
#[test]
fn syntax_tree_nodes_stay_small() {
    use std::mem::size_of;
    for (name, size, ceiling) in [
        ("Member", size_of::<Member>(), 576),
        ("MemberKind", size_of::<MemberKind>(), 552),
        ("Usage", size_of::<Usage>(), 544),
        ("UsageDetail", size_of::<UsageDetail>(), 96),
        ("Definition", size_of::<Definition>(), 288),
        ("Expr", size_of::<Expr>(), 80),
        ("Multiplicity", size_of::<Multiplicity>(), 144),
        ("FeatureDeclaration", size_of::<FeatureDeclaration>(), 352),
        ("ConnectorEnd", size_of::<ConnectorEnd>(), 88),
        ("PayloadPart", size_of::<PayloadPart>(), 120),
    ] {
        assert!(
            size <= ceiling,
            "{name} is {size} bytes, over its {ceiling}-byte ceiling"
        );
    }
}
