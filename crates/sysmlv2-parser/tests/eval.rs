//! Expression evaluator: operator semantics, feature references,
//! Kernel Function Library intrinsics, lambdas, featuring contexts — plus
//! a corpus smoke gate (every feature value must evaluate or fail cleanly,
//! never panic).

use sysmlv2_parser::eval::{EvalError, Value};
use sysmlv2_parser::json::{ElementRef, ResolvedModel};
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::parse_expression;
use sysmlv2_parser::rational::Rational;

/// Evaluate `expr` as `attribute result = <expr>;` inside a package with
/// `decls` alongside it.
fn eval_with(decls: &str, expr: &str) -> Result<Value, EvalError> {
    let mut model = Model::new();
    let unit = model.add_source(
        "t.sysml",
        &format!("package T {{ {decls} attribute result = {expr}; }}"),
    );
    assert!(
        unit.diagnostics.is_empty(),
        "test source must parse cleanly: {:?} in {decls} / {expr}",
        unit.diagnostics[0]
    );
    let mut r = ResolvedModel::build(&model);
    let e = r.resolve_qualified("T::result").expect("result resolves");
    r.evaluate(e)
}

fn eval(expr: &str) -> Result<Value, EvalError> {
    eval_with("", expr)
}

fn int(i: i128) -> Value {
    Value::Integer(i)
}

fn rat(n: i128, d: i128) -> Value {
    Value::Rational(Rational::new(n, d).unwrap())
}

#[test]
fn unknown_member_provenance_survives_value_operations() {
    let decls = "
        part def Child { attribute flag default = false; }
        part def SpecializedChild :> Child { attribute :>> flag; }
        part def Parent { part child : SpecializedChild; part children : Child[0..*]; }
        part installed : Child[1];
        requirement def R { subject unit : Parent[1]; }
        calc def Identity { in x; return result = x; }
    ";
    for expr in [
        "R::unit.child.flag",
        "Identity(R::unit.child).flag",
        "(if true ? R::unit.child else installed).flag",
        "(R::unit.child, installed)#(1).flag",
        "R::unit.child#(1).flag",
        "(R::unit.child, installed)->forAll { in x; x.flag }",
        "size(R::unit.children) == 1",
        "notEmpty(R::unit.children)",
    ] {
        let value = eval_with(decls, expr);
        // forAll includes an independently false concrete item, so it
        // can refute even with an unknown item in the same collection.
        let expected = if expr.contains("forAll") {
            Value::Boolean(false)
        } else {
            Value::Indeterminate
        };
        assert_eq!(value, Ok(expected), "{expr}");
    }
    assert_eq!(
        eval_with(decls, "(R::unit.child, installed).flag"),
        Ok(Value::Sequence(vec![
            Value::Indeterminate,
            Value::Boolean(false)
        ]))
    );
    assert_eq!(eval_with(decls, "size(R::unit.child)"), Ok(int(1)));
    assert_eq!(
        eval_with(decls, "Identity(installed).flag"),
        Ok(Value::Boolean(false))
    );
}

#[test]
fn library_calls_preserve_unknown_receiver_members() {
    let mut model = Model::new();
    let lib = model.add_library_source(
        "library.sysml",
        "package L {
            calc def Read { in x; return result = x.child.flag; }
            calc def LocalDefault { in x default = true; return result = x; }
        }",
    );
    assert!(lib.diagnostics.is_empty(), "{:?}", lib.diagnostics);
    let user = model.add_source(
        "t.sysml",
        "package P {
            part def Child { attribute flag default = false; }
            part def Parent {
                part child : Child;
                attribute independent = L::LocalDefault();
            }
            requirement def R { subject unit : Parent[1]; }
            part installed : Parent[1];
            attribute unknownResult = L::Read(R::unit);
            attribute knownResult = L::Read(installed);
            attribute localDefault = R::unit.independent;
        }",
    );
    assert!(user.diagnostics.is_empty(), "{:?}", user.diagnostics);
    let mut r = ResolvedModel::build(&model);
    for (name, expected) in [
        ("unknownResult", Value::Indeterminate),
        ("knownResult", Value::Boolean(false)),
        ("localDefault", Value::Boolean(true)),
    ] {
        let e = r.resolve_qualified(&format!("P::{name}")).unwrap();
        assert_eq!(r.evaluate(e), Ok(expected), "{name}");
    }
}

#[test]
fn unknown_receivers_agree_across_evaluation_entry_points() {
    use sysmlv2_parser::ast::{Name, QualifiedName};
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package P {
            part def Child { attribute flag default = false; }
            part def Parent { part child : Child; attribute flag default = false; }
            requirement def R {
                subject unit : Parent[1];
                ref part aliasUnit : Parent = unit;
            }
            part installed : Parent[1];
        }",
    );
    let mut r = ResolvedModel::build(&model);
    let member = |value: &str| QualifiedName {
        is_global: false,
        segments: vec![Name {
            value: value.into(),
            span: Default::default(),
        }],
        span: Default::default(),
    };
    for name in ["P::R::unit", "P::R::aliasUnit"] {
        let root = r.resolve_qualified(name).unwrap();
        assert_eq!(
            r.evaluate_chain(root, &[&member("child"), &member("flag")]),
            Ok(Value::Indeterminate)
        );
        assert_eq!(
            r.evaluate_qualified(&format!("{name}::flag")),
            Ok(Value::Indeterminate)
        );
    }
    let installed = r.resolve_qualified("P::installed").unwrap();
    assert_eq!(
        r.evaluate_chain(installed, &[&member("child"), &member("flag")]),
        Ok(Value::Boolean(false))
    );
}

#[test]
fn statement_calculations_never_return_unexecuted_initializers() {
    for statement in [
        "assign i := i / 2;",
        "loop { assign i := i / 2; } until i <= 1;",
        "while i > 1 { assign i := i / 2; }",
        "if i > 1 { assign i := 1; }",
        "for x in (1, 2) { assign i := x; }",
        "action update { assign i := 1; }",
    ] {
        let decl = format!(
            "calc def Halve {{ in n; attribute i = n; {statement} return result = i; }}
             calc halve : Halve;"
        );
        for expression in ["Halve(9)", "halve(9)", "Halve::result", "Halve::i"] {
            let result = eval_with(&decl, expression);
            assert!(
                matches!(&result, Err(EvalError::Unsupported(reason)) if reason.contains("statement execution")),
                "{statement} / {expression}: {result:?}"
            );
        }
        let mut model = Model::new();
        model.add_source("t.sysml", &decl);
        let mut resolved = ResolvedModel::build(&model);
        let calc = resolved.resolve_qualified("Halve").unwrap();
        // Solver clients must not inline the return expression either.
        assert!(resolved.calc_body(calc).is_none());
    }
    assert_eq!(
        eval_with(
            "calc half { in n; attribute i = n / 2; return result = i; }",
            "half(9)"
        ),
        Ok(rat(9, 2))
    );
}

#[test]
fn calculation_arguments_cannot_bind_a_parameter_twice() {
    let decl = "calc f { in x; in y; x + y }";
    for expr in ["f(x = 1, x = 2, y = 3)", "f(1, x = 2, y = 3)"] {
        let value = eval_with(decl, expr);
        assert!(
            matches!(&value, Err(EvalError::Type(m)) if m.contains("bound more than once")),
            "{expr}: {value:?}"
        );
    }
    assert_eq!(eval_with(decl, "f(y = 3, x = 2)"), Ok(int(5)));
}

#[test]
fn calculation_defaults_and_missing_inputs_do_not_capture_caller_parameters() {
    let declarations = "calc f { in x; x } calc g { in x; f() }";
    assert!(
        matches!(eval_with(declarations, "g(9)"), Err(EvalError::Unresolved(m)) if m.contains("unbound parameter `x`"))
    );
    assert_eq!(
        eval_with("calc f { in x = 2; x } calc g { in x; f() }", "g(9)"),
        Ok(int(2))
    );
    assert_eq!(
        eval_with(
            "calc f { in x = y; in y = 3; x + y } calc g { in y; f() }",
            "g(9)"
        ),
        Ok(int(6))
    );
    assert_eq!(
        eval_with("calc f { in x; in y = x + 1; x + y }", "f(4)"),
        Ok(int(9))
    );
    assert_eq!(
        eval_with("calc f { in x; x + 1 } calc g { in x; f(2) + x }", "g(9)"),
        Ok(int(12))
    );
}

#[test]
fn lambdas_and_constructors_do_not_ignore_invalid_bindings_or_statements() {
    assert!(
        matches!(eval("(1, 2)->collect { in x; in y; x }"), Err(EvalError::Type(m)) if m.contains("lambda expects"))
    );
    assert!(
        matches!(eval("(1, 2)->collect { in x; assign x := 9; x }"), Err(EvalError::Unsupported(m)) if m.contains("statement execution"))
    );
    assert!(matches!(
        eval_with(
            "attribute y = 7;",
            "(1, 2)->collect { in x; attribute y = x + 1; y }"
        ),
        Err(EvalError::Unsupported(_))
    ));
    for expression in ["new P(x = 1, x = 2)", "new P(1, x = 2)"] {
        assert!(
            matches!(eval_with("part def P { attribute x; }", expression), Err(EvalError::Type(m)) if m.contains("bound more than once"))
        );
    }
}

#[test]
fn arithmetic_and_precedence() {
    assert_eq!(eval("1 + 2 * 3"), Ok(int(7)));
    assert_eq!(eval("(1 + 2) * 3"), Ok(int(9)));
    assert_eq!(eval("2 ** 10"), Ok(int(1024)));
    // KFL `IntegerFunctions::'/'` returns Rational: true division.
    assert_eq!(eval("7 / 2"), Ok(rat(7, 2)));
    assert_eq!(eval("7.0 / 2"), Ok(rat(7, 2)));
    assert_eq!(eval("9 ** (1/2)"), Ok(int(3)));
    assert_eq!(eval("ln(exp(2.0))"), Ok(Value::Real(2.0)));
    assert_eq!(eval("7 % 3"), Ok(int(1)));
    assert_eq!(eval("-5 + 3"), Ok(int(-2)));
    assert_eq!(eval("1 / 0"), Err(EvalError::DivisionByZero));
}

#[test]
fn comparisons_and_logic() {
    assert_eq!(eval("3 < 4 and 4 <= 4"), Ok(Value::Boolean(true)));
    assert_eq!(eval("3 > 4 or 4 >= 5"), Ok(Value::Boolean(false)));
    assert_eq!(eval("not (1 == 2)"), Ok(Value::Boolean(true)));
    assert_eq!(eval("1 != 2 xor false"), Ok(Value::Boolean(true)));
    assert_eq!(eval("false implies (1/0 == 1)"), Ok(Value::Boolean(true)));
    assert_eq!(eval("3 == 3.0"), Ok(Value::Boolean(true)));
    assert_eq!(eval("\"a\" < \"b\""), Ok(Value::Boolean(true)));
}

#[test]
fn conditionals_ranges_sequences() {
    assert_eq!(eval("if 2 > 1 ? 10 else 20"), Ok(int(10)));
    assert_eq!(
        eval("1..4"),
        Ok(Value::Sequence(vec![int(1), int(2), int(3), int(4)]))
    );
    assert_eq!(
        eval("(1, (2, 3))"),
        Ok(Value::Sequence(vec![int(1), int(2), int(3)]))
    );
    assert_eq!(eval("null ?? 5"), Ok(int(5)));
    assert_eq!(eval("3 ?? 5"), Ok(int(3)));
    assert_eq!(eval("(10, 20, 30)#(2)"), Ok(int(20)));
}

#[test]
fn feature_references_and_cycles() {
    assert_eq!(eval_with("attribute x = 2;", "x + 1"), Ok(int(3)));
    assert_eq!(
        eval_with("attribute a = b + 1; attribute b = a + 1;", "a"),
        Err(EvalError::Cycle("a".into()))
    );
    assert!(matches!(eval("nosuch"), Err(EvalError::Unresolved(_))));
}

#[test]
fn intrinsics() {
    assert_eq!(eval("sum((1, 2, 3))"), Ok(int(6)));
    assert_eq!(eval("sum((1, 2.5))"), Ok(rat(7, 2)));
    assert_eq!(eval("product(2..4)"), Ok(int(24)));
    assert_eq!(eval("size((7, 8))"), Ok(int(2)));
    assert_eq!(eval("isEmpty(null)"), Ok(Value::Boolean(true)));
    assert_eq!(eval("notEmpty((1))"), Ok(Value::Boolean(true)));
    assert_eq!(eval("includes((1, 2), 2)"), Ok(Value::Boolean(true)));
    assert_eq!(eval("head((4, 5, 6))"), Ok(int(4)));
    assert_eq!(eval("last((4, 5, 6))"), Ok(int(6)));
    assert_eq!(eval("max((3, 9, 5))"), Ok(int(9)));
    assert_eq!(eval("min(3, 9)"), Ok(int(3)));
    assert_eq!(eval("abs(-7)"), Ok(int(7)));
    assert_eq!(eval("floor(2.9)"), Ok(int(2)));
    assert_eq!(eval("Length(\"abc\")"), Ok(int(3)));
    assert_eq!(
        eval("Substring(\"hello\", 2, 4)"),
        Ok(Value::String("ell".into()))
    );
    assert_eq!(eval("\"a\" + ToString(1)"), Ok(Value::String("a1".into())));
    assert_eq!(eval("ToInteger(\"42\")"), Ok(int(42)));
    // TrigFunctions / RationalFunctions / NumericalFunctions /
    // ComplexFunctions-on-reals.
    assert_eq!(eval("sin(0)"), Ok(Value::Real(0.0)));
    assert_eq!(eval("cos(0)"), Ok(Value::Real(1.0)));
    assert_eq!(eval("rat(1, 4)"), Ok(rat(1, 4)));
    assert_eq!(eval("isZero(0)"), Ok(Value::Boolean(true)));
    assert_eq!(eval("isUnit(2)"), Ok(Value::Boolean(false)));
    assert_eq!(eval("re(7)"), Ok(int(7)));
    // Body-taking control functions: selectOne, minimize, maximize.
    assert_eq!(eval("(1..9)->selectOne { in x; x > 4 }"), Ok(int(5)));
    assert_eq!(eval("(1..3)->minimize { in x; 10 - x }"), Ok(int(7)));
    assert_eq!(eval("(1..3)->maximize { in x; 10 - x }"), Ok(int(9)));
}

#[test]
fn lambdas() {
    assert_eq!(
        eval("(1..6)->select { in x; x % 2 == 0 }"),
        Ok(Value::Sequence(vec![int(2), int(4), int(6)]))
    );
    assert_eq!(
        eval("(1..3)->collect { in x; x * x }"),
        Ok(Value::Sequence(vec![int(1), int(4), int(9)]))
    );
    assert_eq!(
        eval("(1..3)->reject { in x; x == 2 }"),
        Ok(Value::Sequence(vec![int(1), int(3)]))
    );
    assert_eq!(
        eval("(1..4)->forAll { in x; x < 5 }"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval("(1..4)->exists { in x; x == 3 }"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(eval("(1..5)->reduce { in a; in b; a + b }"), Ok(int(15)));
}

#[test]
fn featuring_context_redefinition() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package T {
             part def Vehicle {
                 attribute baseMass = 1000;
                 attribute extra = 100;
                 attribute total = baseMass + extra;
             }
             part car : Vehicle[1] { attribute :>> baseMass = 1200; }
             attribute carTotal = car.total;
             attribute defTotal = Vehicle::total;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let car_total = r.resolve_qualified("T::carTotal").unwrap();
    assert_eq!(r.evaluate(car_total), Ok(Value::Integer(1300)));
    let def_total = r.resolve_qualified("T::defTotal").unwrap();
    assert_eq!(r.evaluate(def_total), Ok(Value::Integer(1100)));
    // Qualified-name evaluation reaching an inherited feature through a
    // usage establishes the usage as featuring context, exactly like
    // the chain form `car.total`; through the definition it stays in
    // the definition's own scope.
    assert_eq!(
        r.evaluate_qualified("T::car::total"),
        Ok(Value::Integer(1300))
    );
    assert_eq!(
        r.evaluate_qualified("T::Vehicle::total"),
        Ok(Value::Integer(1100))
    );
}

/// A feature with no value of its own takes the value of a feature it
/// subsets when the two cannot differ: it has at least one value and the
/// subsetted feature at most one, so its one value is the subsetted
/// feature's. A multiplicity read from the subsetted feature counts. The
/// feature's own value still wins, and so does its own reading when it says
/// more than the subsetted feature (members of its own, a narrower type);
/// an optional subsetting feature, or a collection-valued subsetted one,
/// stays unknown; a receiver's redefinition of the subsetted feature is
/// read through the receiver; and a subsetting cycle settles nothing.
#[test]
fn singleton_subsettings_take_the_subsetted_value() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package T {
             part def Crawler { attribute m; }
             part def Racer :> Crawler { attribute speed = 3; }
             part def Ctx {
                 part tiny : Crawler { attribute :>> m = 4; }
                 part crowd : Crawler[0..*];
                 part other : Crawler { attribute :>> m = 9; }
                 part single[1] :> tiny;
                 part implied :> tiny;
                 part optional[0..1] :> tiny;
                 part fromCrowd[1] :> crowd;
                 part pinned[1] :> tiny = other;
                 part bodied[1] :> tiny { attribute :>> m = 6; }
                 part narrower[1] : Racer :> tiny;
                 part ping[1] :> pong;
                 part pong[1] :> ping;
             }
             part ctx : Ctx[1];
             part special : Ctx[1] { part :>> tiny { attribute :>> m = 7; } }
             attribute rSingle = ctx.single.m;
             attribute rImplied = ctx.implied.m;
             attribute rOptional = ctx.optional.m;
             attribute rFromCrowd = ctx.fromCrowd.m;
             attribute rPinned = ctx.pinned.m;
             attribute rBodied = ctx.bodied.m;
             attribute rNarrower = ctx.narrower.speed;
             attribute rCycle = ctx.ping.m;
             attribute rSpecial = special.single.m;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let mut eval = |name: &str| {
        let e = r.resolve_qualified(&format!("T::{name}")).unwrap();
        r.evaluate(e)
    };
    assert_eq!(eval("rSingle"), Ok(Value::Integer(4)));
    assert_eq!(eval("rImplied"), Ok(Value::Integer(4)));
    assert_eq!(eval("rPinned"), Ok(Value::Integer(9)));
    assert_eq!(eval("rBodied"), Ok(Value::Integer(6)));
    assert_eq!(eval("rNarrower"), Ok(Value::Integer(3)));
    assert_eq!(eval("rSpecial"), Ok(Value::Integer(7)));
    for name in ["rOptional", "rFromCrowd", "rCycle"] {
        let value = eval(name);
        assert!(
            !matches!(value, Ok(Value::Integer(_))),
            "{name} must stay unknown: {value:?}"
        );
    }
}

/// An analysis performed once whose subject subsets a single part reads that
/// part: under singletons `subject :>> c :> tiny;` is `c = tiny`, so the
/// result evaluates. Without `[1]` the analysis usage stands for any number
/// of performances, and its result stays unknown.
#[test]
fn analysis_results_read_a_singleton_subsetted_subject() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package P {
             part def Crawler { attribute m; }
             analysis def MassAnalysis {
                 subject c : Crawler;
                 return result = c.m;
             }
             part def Ctx {
                 part tiny : Crawler { attribute :>> m = 4; }
                 analysis once[1] : MassAnalysis { subject :>> c :> tiny; }
                 analysis any : MassAnalysis { subject :>> c :> tiny; }
                 attribute viaOnce = once.result;
                 attribute viaAny = any.result;
             }
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let once = r.resolve_qualified("P::Ctx::viaOnce").unwrap();
    assert_eq!(r.evaluate(once), Ok(Value::Integer(4)));
    let any = r.resolve_qualified("P::Ctx::viaAny").unwrap();
    assert_eq!(r.evaluate(any), Ok(Value::Indeterminate));
}

/// A featuring instance may redefine a chain of names as a whole
/// (`attribute :>> chassis.mass = 25;`). Reading the chain through that
/// instance takes the redefinition's value — directly, inside an
/// inherited formula, from a specialization of the instance, and from a
/// navigation-site chain — while the definition and the other instances
/// keep their own values.
#[test]
fn chain_redefinitions_supply_the_chained_feature_value() {
    use sysmlv2_parser::ast::{Name, QualifiedName};
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package T {
             part def Chassis { attribute mass; }
             part def Crawler {
                 part chassis : Chassis { attribute :>> mass default 1; }
                 attribute vehicleMass = chassis.mass;
             }
             part plain : Crawler[1];
             part nested : Crawler[1] { part :>> chassis { attribute :>> mass = 4; } }
             part chained : Crawler[1] { attribute :>> chassis.mass = 25; }
             part special[1] :> chained;
             attribute direct = chained.chassis.mass;
             attribute rolled = chained.vehicleMass;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    for (name, expected) in [
        ("T::Crawler::vehicleMass", 1),
        ("T::plain::vehicleMass", 1),
        ("T::nested::vehicleMass", 4),
        ("T::chained::vehicleMass", 25),
        ("T::special::vehicleMass", 25),
    ] {
        assert_eq!(
            r.evaluate_qualified(name),
            Ok(Value::Integer(expected)),
            "{name}"
        );
    }
    for name in ["T::direct", "T::rolled"] {
        let e = r.resolve_qualified(name).unwrap();
        assert_eq!(r.evaluate(e), Ok(Value::Integer(25)), "{name}");
    }
    let member = |value: &str| QualifiedName {
        is_global: false,
        segments: vec![Name {
            value: value.into(),
            span: Default::default(),
        }],
        span: Default::default(),
    };
    for (root, expected) in [("T::chained", 25), ("T::plain", 1)] {
        let root = r.resolve_qualified(root).unwrap();
        assert_eq!(
            r.evaluate_chain(root, &[&member("chassis"), &member("mass")]),
            Ok(Value::Integer(expected))
        );
    }
}

/// A chain step landing on an overriding usage (`part :>> c : N;`) must
/// resolve the next member through the override's declared type as well
/// as the redefinition target's: `d` is inherited both ways (the original
/// through the target's type, the redefining `:>> d` through `N`), and
/// the redefining feature shadows its target instead of making the name
/// ambiguous. All three overriding spellings, chained directly and through
/// an inherited body expression.
#[test]
fn chain_member_through_overriding_usage() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package T {
             part def L { attribute d; }
             part def N :> L { attribute :>> d = 5; }
             part def D { part c : L; attribute v = c.d; }
             part unnamed : D[1] { part :>> c : N; }
             part named : D[1] { part c :>> c : N; }
             part subset : D[1] { part :> c : N; }
             attribute chainUnnamed = unnamed.c.d;
             attribute chainNamed = named.c.d;
             attribute chainSubset = subset.c.d;
             attribute bodyUnnamed = unnamed.v;
             attribute bodyNamed = named.v;
             attribute bodySubset = subset.v;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    for probe in [
        "T::chainUnnamed",
        "T::chainNamed",
        "T::chainSubset",
        "T::bodyUnnamed",
        "T::bodyNamed",
    ] {
        let e = r.resolve_qualified(probe).unwrap();
        assert_eq!(r.evaluate(e), Ok(Value::Integer(5)), "{probe}");
    }
    // Subsetting is not redefinition: the subsetter is a *distinct*
    // feature alongside `c`, so `v = c.d` written in the definition's
    // body still reads the inherited `c : L`, whose `d` is unbound. Only
    // the chain access collects the subsetter as a member populating `c`.
    let e = r.resolve_qualified("T::bodySubset").unwrap();
    assert!(
        matches!(r.evaluate(e), Ok(Value::Unbound(..))),
        "bodySubset stays unbound"
    );
}

/// Implicit redefinition by name (SysML usage semantics): a usage owned
/// by a type that specializes another candidate's owning type shadows
/// the same-named inherited feature even without a spelled `:>>` — the
/// diamond `f` (via the redefinition target's type and via the
/// override's) resolves to the more specific redeclaration. Owners with
/// no strict one-way conformance stay ambiguous: multiple classification
/// makes both same-named features legitimate members, and neither
/// overrides the other.
#[test]
fn implicit_redefinition_by_name_shadows_in_diamonds() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package T {
             part def Base { attribute f; }
             part def Base2 :> Base { attribute f = 7; }
             part def C { part p : Base; }
             part c1 : C[1] { part :>> p : Base2; }
             attribute probe = c1.p.f;

             part def A1 { attribute g = 1; }
             part def A2 { attribute g = 2; }
             part q[1] { part x : A1, A2; }
             attribute unrelated = q.x.g;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let probe = r.resolve_qualified("T::probe").unwrap();
    assert_eq!(r.evaluate(probe), Ok(Value::Integer(7)));
    let unrelated = r.resolve_qualified("T::unrelated").unwrap();
    assert!(
        matches!(r.evaluate(unrelated), Err(EvalError::Unresolved(_))),
        "unrelated same-named features stay ambiguous"
    );
}

/// KerML `that` — `Base::things::that`, "the featuring instance": a
/// feature's `that` is the instance of its owner, `x.that` chains one
/// hop up, and `that.that` walks two. The library declares it on the
/// implied root feature `things` (an implied specialization the
/// resolver does not materialize), so the bare unresolved spelling
/// falls back in the evaluator; a resolved declaration named `that`
/// always wins.
#[test]
fn that_denotes_the_featuring_instance() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package T {
             part def Boxy;
             part outer : Boxy[1] {
                 part inner {
                     attribute me = that;
                 }
             }
             attribute probeMe = outer.inner.me istype Boxy;
             attribute probeChain = outer.inner.that istype Boxy;
             part shadow[1] { attribute that = 42; attribute reads = that; }
             attribute probeShadow = shadow.reads;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    // `that` inside inner's body is the outer instance (typed Boxy),
    // both as a bare reference and as a chain member.
    let me = r.resolve_qualified("T::probeMe").unwrap();
    assert_eq!(r.evaluate(me), Ok(Value::Boolean(true)));
    let chain = r.resolve_qualified("T::probeChain").unwrap();
    assert_eq!(r.evaluate(chain), Ok(Value::Boolean(true)));
    // A declared `that` shadows the fallback.
    let sh = r.resolve_qualified("T::probeShadow").unwrap();
    assert_eq!(r.evaluate(sh), Ok(Value::Integer(42)));
}

/// Function references where a lambda body would go: `->reduce '+'`
/// folds through the arithmetic core (empty folds to null — the
/// library spells `coll->reduce '+' ?? zero`), intrinsic names
/// dispatch (`->reduce min`), user calculations apply per item, and a
/// chained callee (`nested.calc(…)`) resolves through the chain
/// machinery. Unknown items still degrade instead of deciding.
#[test]
fn function_reference_arguments_apply() {
    let decls = "
        calc def Double { in x; return r = 2 * x; }
        part holder { calc dbl { in x; return r = 2 * x; } }
        attribute u;
    ";
    assert_eq!(eval("(1..4)->reduce '+'"), Ok(int(10)));
    assert_eq!(eval("(2, 3, 4)->reduce '*'"), Ok(int(24)));
    assert_eq!(eval("null->reduce '+' ?? 0"), Ok(int(0)));
    assert_eq!(eval("(7)->reduce '+'"), Ok(int(7)));
    assert_eq!(eval("(3, 9, 5)->reduce min"), Ok(int(3)));
    assert_eq!(eval("(3, 9, 5)->reduce max"), Ok(int(9)));
    assert_eq!(
        eval_with(decls, "(1, 2, 3)->collect Double"),
        Ok(Value::Sequence(vec![int(2), int(4), int(6)]))
    );
    // Chained callee.
    assert_eq!(eval_with(decls, "holder.dbl(21)"), Ok(int(42)));
    // Unknown items degrade, never decide.
    assert_eq!(
        eval_with(decls, "(1, u, 3)->reduce '+'"),
        Ok(Value::Indeterminate)
    );
}

/// Invoking a bodiless *calculation* — abstract, a declaration shell,
/// or a function-typed parameter whose actual is unknown — yields an
/// indeterminate result; invoking a non-callable target stays an error
/// (degrading it would mask a genuine model defect).
#[test]
fn bodiless_calculation_invocation_is_indeterminate() {
    let decls = "
        abstract calc def Estimate { in x; return : ScalarValues::Real; }
        calc def Double :> Estimate { in x; return r = 2 * x; }
        abstract calc estimate : Estimate;
        calc def Wrap {
            in fn : Estimate;
            in y;
            return r = fn(y) + 0;
        }
        part def NotCallable;
    ";
    assert_eq!(
        eval_with(decls, "Estimate(3)"),
        Ok(Value::Indeterminate),
        "abstract calc def"
    );
    assert_eq!(
        eval_with(decls, "estimate(3)"),
        Ok(Value::Indeterminate),
        "a bodiless calc usage inherits its definition's parameters"
    );
    assert_eq!(
        eval_with(decls, "Wrap(Estimate, 3)"),
        Ok(Value::Indeterminate),
        "function-typed parameter"
    );
    assert_eq!(
        eval_with(decls, "Wrap(Double, 3)"),
        Ok(int(6)),
        "a known function-typed actual is invoked"
    );
    assert!(matches!(
        eval_with(decls, "Estimate(1, 2)"),
        Err(EvalError::Type(_))
    ));
    assert!(matches!(
        eval_with(decls, "Estimate(noSuch = 1)"),
        Err(EvalError::Unresolved(_))
    ));
    assert!(matches!(
        eval_with(decls, "NotCallable(3)"),
        Err(EvalError::Unsupported(_))
    ));
}

/// Operations over an unbound feature degrade to an *indeterminate*
/// value instead of a type error: the formula is parametric, its value
/// simply is not determined. Decided short-circuit sides still decide
/// (`false and …` never looks right), an unknown side never fabricates
/// a boolean, and closed non-numeric values (enum literals) still
/// type-error.
#[test]
fn unbound_operands_degrade_to_indeterminate() {
    let u = "attribute u;";
    for expr in [
        "u + 5",
        "u > 3",
        "u == 5",
        "not (u == 5)",
        "-u",
        "(u > 3) and true",
        "false or (u == 1)",
        "true implies (u == 1)",
        "if u > 0 ? 1 else 2",
        "(10, 20, 30)#(u)",
    ] {
        assert_eq!(eval_with(u, expr), Ok(Value::Indeterminate), "{expr}");
    }
    // A decided left side still decides without touching the right.
    assert_eq!(eval_with(u, "false and (u > 3)"), Ok(Value::Boolean(false)));
    assert_eq!(eval_with(u, "(u > 3) and false"), Ok(Value::Boolean(false)));
    assert_eq!(eval_with(u, "true or (u == 1)"), Ok(Value::Boolean(true)));
    assert_eq!(eval_with(u, "(u == 1) or true"), Ok(Value::Boolean(true)));
    assert_eq!(
        eval_with(u, "false implies (u == 1)"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(u, "(u == 1) implies true"),
        Ok(Value::Boolean(true))
    );
    // Collection membership is three-valued. An indeterminate tuple
    // constituent may denote a collection of unknown arity, so the tuple
    // stays indeterminate even when another constituent is a known match.
    assert_eq!(
        eval_with(u, "includes((1, 2), u + 1)"),
        Ok(Value::Indeterminate)
    );
    assert_eq!(
        eval_with(u, "excludes((1, 2), u + 1)"),
        Ok(Value::Indeterminate)
    );
    assert_eq!(
        eval_with(u, "includes((1, u + 1), 1)"),
        Ok(Value::Indeterminate)
    );
    assert_eq!(
        eval_with(u, "excludes((1, u + 1), 1)"),
        Ok(Value::Indeterminate)
    );
    // Indeterminate propagates through further arithmetic.
    assert_eq!(eval_with(u, "(u + 5) * 2"), Ok(Value::Indeterminate));
    // Closed non-numeric values still type-error.
    assert!(matches!(
        eval_with("enum def L { a; b; }", "L::a + 1"),
        Err(EvalError::Type(_))
    ));
}

#[test]
fn enum_values_compare_as_elements() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package T {
             enum def Level { low; medium; high; }
             attribute chosen = Level::medium;
             attribute isMedium = chosen == Level::medium;
             attribute isHigh = chosen == Level::high;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let is_medium = r.resolve_qualified("T::isMedium").unwrap();
    assert_eq!(r.evaluate(is_medium), Ok(Value::Boolean(true)));
    let is_high = r.resolve_qualified("T::isHigh").unwrap();
    assert_eq!(r.evaluate(is_high), Ok(Value::Boolean(false)));
}

/// Build the `Unit` for a probe expression so tests can compare quantities
/// structurally (`Unit` equality is dimensional). The declarations must
/// match the test's own — unit identity is the resolved element.
fn unit_probe_with(decls: &str, unit_expr: &str) -> sysmlv2_parser::eval::Unit {
    match eval_with(decls, &format!("1 [{unit_expr}]")) {
        Ok(Value::Quantity(_, u)) => u,
        other => panic!("unit probe failed: {other:?}"),
    }
}

fn unit_probe(unit_expr: &str) -> sysmlv2_parser::eval::Unit {
    unit_probe_with(
        "attribute mm; attribute kg; attribute m; attribute s;",
        unit_expr,
    )
}

#[test]
fn quantity_brackets() {
    let units = "attribute mm; attribute kg; attribute m; attribute s;";
    // Same-unit arithmetic and comparison work on the numbers.
    assert_eq!(
        eval_with(units, "10 [mm] + 5 [mm]"),
        Ok(Value::Quantity(Box::new(int(15)), unit_probe("mm")))
    );
    assert_eq!(
        eval_with(units, "10 [mm] < 20 [mm]"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(units, "10 [mm] == 10.0 [mm]"),
        Ok(Value::Boolean(true))
    );
    // Scalars scale; same-unit division cancels to a ratio.
    assert_eq!(
        eval_with(units, "3 * (10 [mm])"),
        Ok(Value::Quantity(Box::new(int(30)), unit_probe("mm")))
    );
    assert_eq!(eval_with(units, "30 [mm] / (10 [mm])"), Ok(int(3)));
    // Different units never mix silently — `kg` vs `mm` is an error, not
    // `false` (no unit conversion happens either way).
    assert!(matches!(
        eval_with(units, "1 [kg] + 1 [mm]"),
        Err(EvalError::Type(_))
    ));
    assert!(matches!(
        eval_with(units, "1 [kg] == 1 [mm]"),
        Err(EvalError::Type(_))
    ));
    assert!(matches!(
        eval_with(units, "1 [kg] < 2"),
        Err(EvalError::Type(_))
    ));
    // Compound units compare structurally.
    assert_eq!(
        eval_with(units, "9.81 [m/s**2] <= 9.82 [m/s**2]"),
        Ok(Value::Boolean(true))
    );
    assert!(matches!(
        eval_with(units, "1 [m/s**2] == 1 [m]"),
        Err(EvalError::Type(_))
    ));
    // The same unit through different spellings is one unit.
    assert_eq!(
        eval_with(
            "package SI { attribute kg; } attribute total = 1 [SI::kg] + 2 [SI::kg];",
            "total == 3 [T::SI::kg]"
        ),
        Ok(Value::Boolean(true))
    );
    // max/abs respect units.
    assert_eq!(
        eval_with(units, "max((3 [mm], 7 [mm], 5 [mm]))"),
        Ok(Value::Quantity(Box::new(int(7)), unit_probe("mm")))
    );
    assert_eq!(
        eval_with(units, "abs(-4 [mm])"),
        Ok(Value::Quantity(Box::new(int(4)), unit_probe("mm")))
    );
}

#[test]
fn user_defined_calculations() {
    let calc = "calc def Torque { in force; in radius; force * radius }";
    assert_eq!(eval_with(calc, "Torque(10, 3)"), Ok(int(30)));
    // Named arguments, in any order.
    assert_eq!(
        eval_with(calc, "Torque(radius = 3, force = 10)"),
        Ok(int(30))
    );
    // Calculations can call other calculations…
    assert_eq!(
        eval_with(
            "calc def Double { in x; x * 2 } calc def Quad { in x; Double(Double(x)) }",
            "Quad(5)"
        ),
        Ok(int(20))
    );
    // …and themselves (recursion is bounded, not forbidden).
    assert_eq!(
        eval_with(
            "calc def Fib { in n; if n < 2 ? n else Fib(n - 1) + Fib(n - 2) }",
            "Fib(10)"
        ),
        Ok(int(55))
    );
    // A non-terminating recursion exhausts the call-depth budget — not
    // the stack, and not the feature-value cycle guard, which sees a new
    // invocation each time.
    let loop_calc = eval_with("calc def Loop { in n; Loop(n) }", "Loop(1)");
    assert!(
        matches!(&loop_calc, Err(EvalError::Budget(m)) if m.contains("calculation calls")),
        "{loop_calc:?}"
    );
    // Wrong arguments error cleanly.
    assert!(matches!(
        eval_with(calc, "Torque(1, 2, 3)"),
        Err(EvalError::Type(_))
    ));
    assert!(matches!(
        eval_with(calc, "Torque(lever = 3, force = 10)"),
        Err(EvalError::Unresolved(_))
    ));
    // A declared calculation takes precedence over an intrinsic spelling.
    assert_eq!(
        eval_with("calc def sum { in x; 0 }", "sum((1, 2, 3))"),
        Ok(int(0))
    );
    // The `return x = expr;` spelling (a bound return parameter) also
    // yields the calculation's result — the rocket equation, no less.
    assert_eq!(
        eval_with(
            "calc def DeltaV {
                 in isp; in g0; in m0; in mf;
                 return dv = isp * g0 * ln(m0 / mf);
             }",
            "DeltaV(300, 9.8, 100, 50) > 2037 & DeltaV(300, 9.8, 100, 50) < 2038"
        ),
        Ok(Value::Boolean(true))
    );
}

#[test]
fn constructors() {
    let defs = "attribute def Date {
                    attribute val;
                    attribute precision = \"day\";
                }";
    // Positional args bind the public features in declaration order;
    // equality is structural; chain steps read bound fields.
    assert_eq!(
        eval_with(defs, "new Date(\"1969-07-20\") == new Date(\"1969-07-20\")"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(defs, "new Date(\"1969-07-20\") == new Date(\"1969-07-21\")"),
        Ok(Value::Boolean(false))
    );
    assert_eq!(
        eval_with(
            defs,
            "new Date(\"1969-07-20\") != new Date(val = \"1969-07-20\")"
        ),
        Ok(Value::Boolean(false))
    );
    assert_eq!(
        eval_with(defs, "new Date(\"1969-07-20\").val"),
        Ok(Value::String("1969-07-20".into()))
    );
    // Different types never compare equal.
    assert_eq!(
        eval_with(
            "attribute def A { attribute v; } attribute def B { attribute v; }",
            "new A(1) == new B(1)"
        ),
        Ok(Value::Boolean(false))
    );
    // Errors stay clean: unknown field, an argument landing on a feature
    // whose value is not a default (`precision = "day"`), unbound field.
    assert!(matches!(
        eval_with(defs, "new Date(moment = \"x\")"),
        Err(EvalError::Unresolved(_))
    ));
    assert!(matches!(
        eval_with(defs, "new Date(\"a\", \"b\")"),
        Err(EvalError::Type(m)) if m.contains("cannot override the non-default value of `precision`")
    ));
    assert!(matches!(
        eval_with(defs, "new Date().val"),
        Err(EvalError::Type(_))
    ));
    // Unresolved constructor type.
    assert!(matches!(
        eval("new Missing(1)"),
        Err(EvalError::Unresolved(_))
    ));
}

#[test]
fn constructor_arguments_bind_the_public_feature_sequence() {
    // The sequence is the type's own public features in declaration
    // order, then the inherited ones a nearer feature does not redefine
    // or hide; a feature already carrying a value keeps its position, so
    // a default is positionally overridable and a bound value is not.
    let defs = "attribute def Stamp {
                    attribute val;
                    attribute precision default \"day\";
                    private attribute hidden;
                    attribute zone;
                }
                attribute def Local :> Stamp {
                    attribute :>> zone = \"here\";
                    attribute offset;
                }";
    assert_eq!(
        eval_with(defs, "new Stamp(\"x\", \"month\").precision"),
        Ok(Value::String("month".into()))
    );
    assert_eq!(
        eval_with(defs, "new Stamp(\"x\", \"month\", \"Z\").zone"),
        Ok(Value::String("Z".into()))
    );
    assert!(matches!(
        eval_with(defs, "new Stamp(\"x\").precision"),
        Err(EvalError::Type(m)) if m.contains("is not bound")
    ));
    assert!(matches!(
        eval_with(defs, "new Stamp(\"x\", \"month\", \"Z\", 4)"),
        Err(EvalError::Type(m)) if m.contains("too many constructor arguments")
    ));
    // `Local`: its own `zone` (bound) and `offset`, then `val` and
    // `precision` from `Stamp` — `zone` is redefined, `hidden` private.
    assert_eq!(
        eval_with(defs, "new Local(offset = 2, val = \"x\").offset"),
        Ok(Value::Integer(2))
    );
    assert!(matches!(
        eval_with(defs, "new Local(\"UTC\")"),
        Err(EvalError::Type(m)) if m.contains("cannot override the non-default value of `zone`")
    ));
    assert_eq!(
        eval_with(defs, "new Local(zone = \"UTC\")").map(|_| ()),
        Err(EvalError::Type(
            "constructor field `zone` cannot override the non-default value of `zone`".into()
        ))
    );
    // An inherited defaulted field is positionally bindable too; a
    // short-name-only feature is bound and read by that name; a feature
    // nothing can name (an invariant) takes no argument.
    let more = "attribute def Sub :> Stamp { attribute extra; }
                attribute def Short { attribute <s>; attribute a; }
                attribute def Checked { attribute items[*]; assert constraint { true } }";
    let defs = format!("{defs} {more}");
    assert_eq!(
        eval_with(&defs, "new Sub(9, \"x\", \"month\").precision"),
        Ok(Value::String("month".into()))
    );
    assert_eq!(eval_with(&defs, "new Short(1).s"), Ok(Value::Integer(1)));
    assert!(matches!(
        eval_with(&defs, "new Checked(1, 2)"),
        Err(EvalError::Type(m)) if m.contains("that nothing can name")
    ));
    assert_eq!(
        eval_with(&defs, "new Checked((1, 2)).items"),
        Ok(Value::Sequence(vec![Value::Integer(1), Value::Integer(2)]))
    );
}

#[test]
fn unsupported_constructs_error_cleanly() {
    // `all T` extents stay outside the evaluator.
    assert!(matches!(
        eval_with("part def T;", "all T"),
        Err(EvalError::Unsupported(_))
    ));
}

/// A library collection the receiver populates evaluates to the
/// populating members: `p.performedActions` collects p's perform
/// usages (each standing for its referenced action, so `as` filters
/// and member access work on the actions), and the rollup reduces.
#[test]
fn implied_collections_roll_up() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_source(
        "t.sysml",
        "package T {
            private import ScalarValues::*;
            action def Step { attribute cost : Real default 0; }
            action a1 : Step[1] { attribute :>> cost = 5; }
            action a2 : Step[1] { attribute :>> cost = 7; }
            action a3 : Step[1] { attribute :>> cost = 10; }
            part p[1] { perform a1; perform a2; }
            part rollup {
                attribute total : Real = RealFunctions::sum((p.performedActions as Step).cost);
            }
        }",
    );
    let mut r = ResolvedModel::build(&model);
    let e = r.resolve_qualified("T::rollup::total").expect("resolves");
    assert_eq!(r.evaluate(e), Ok(Value::Integer(12)));
}

/// A query of a feature that a part redefines answers as the redefining
/// part does: the part's owned parts do not stand in for it, and a part
/// that owns none does not answer empty. Feature values read the same way.
/// The receivers are single instances (`[1]`) so that the redefinition,
/// not an unknown receiver, decides each answer where unbound collections
/// answer indeterminate.
#[test]
fn a_redefined_feature_answers_as_its_redefining_part() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_source(
        "t.sysml",
        "package P {
            part def Wheel;
            part def Car { part wheels : Wheel[0..*]; }
            part car : Car[1] {
                part frontWheels :>> wheels {
                    part left : Wheel;
                    part right : Wheel;
                }
            }
            part car2 : Car[1] {
                part frontWheels :>> wheels {
                    attribute mass = 12;
                }
            }
            attribute viaRedefined = car2.wheels.mass;
            attribute viaRedefining = car2.frontWheels.mass;
        }",
    );
    let mut r = ResolvedModel::build(&model);
    let root = r.root_scope();
    let query = |r: &mut ResolvedModel, text: &str| {
        let parsed = parse_expression(text);
        r.query(root, &parsed.expr.expect("expression"))
    };
    for (redefined, redefining) in [
        ("P::car.wheels", "P::car.frontWheels"),
        ("P::car2.wheels", "P::car2.frontWheels"),
        ("P::car2.wheels.mass", "P::car2.frontWheels.mass"),
    ] {
        let answer = query(&mut r, redefined);
        assert!(answer.is_ok(), "{redefined}: {answer:?}");
        assert_eq!(
            answer,
            query(&mut r, redefining),
            "{redefined} answers as {redefining}"
        );
    }
    let value = |r: &mut ResolvedModel, name: &str| {
        let e = r.resolve_qualified(name).expect(name);
        r.evaluate(e)
    };
    let via_redefined = value(&mut r, "P::viaRedefined");
    assert!(via_redefined.is_ok(), "{via_redefined:?}");
    assert_eq!(via_redefined, value(&mut r, "P::viaRedefining"));
}

/// Corpus smoke gate: every feature value in the full corpus (with the
/// standard library loaded) either evaluates or returns a clean error —
/// no panics, and a healthy fraction actually computes.
#[test]
fn corpus_feature_values_evaluate_or_fail_cleanly() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(
            sysmlv2_testkit::relative_source_name(&sysmlv2_testkit::corpus_root(), f.as_path()),
            &src,
        );
    }
    let mut r = ResolvedModel::build(&model);
    let features = r.features_with_values();
    let mut ok = 0usize;
    for e in &features {
        if r.evaluate(*e).is_ok() {
            ok += 1;
        }
    }
    assert!(features.len() > 3000, "expected many corpus feature values");
    // Ratchet: at least this fraction must evaluate successfully
    // (currently 81.4% — quantity brackets, user-defined calculation
    // invocation, and `new` constructors).
    assert!(
        ok * 100 >= features.len() * 80,
        "only {ok}/{} corpus feature values evaluated",
        features.len()
    );
}

/// The parameters an invocation binds, read off a callable's heritage
/// alone, are the parameters among the model's own view of its features
/// (implied heritage included), for every type of the library and the
/// corpus but a few the inherited view reads differently: a performed
/// action reached through a feature chain, whose parameters the walk pairs
/// by position where the inherited view keeps both; a state's performed
/// action, whose inherited view also lists an accept action's payload
/// registered in the enclosing scope; and a requirement's subject that
/// redefines its general's subject explicitly, which the inherited view
/// gives none.
#[test]
fn corpus_callable_parameters_agree_with_the_inherited_view() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    for f in sysmlv2_testkit::user_files() {
        let src = std::fs::read_to_string(&f).unwrap();
        model.add_source(
            sysmlv2_testkit::relative_source_name(&sysmlv2_testkit::corpus_root(), f.as_path()),
            &src,
        );
    }
    let mut r = ResolvedModel::build(&model);
    let mut checked = 0;
    let mut differ = Vec::new();
    for callee in r.elements().collect::<Vec<_>>() {
        if r.inheritance_incomplete(callee, true) {
            continue;
        }
        let inherited: Vec<_> = r
            .effective_features(callee, true)
            .into_iter()
            .filter(|&f| {
                r.is_parameter(f)
                    && r.owning_membership_type(f) != Some("ReturnParameterMembership")
            })
            .collect();
        let Some(parameters) = r.callable_parameters(callee) else {
            let name = r.element_qualified_name(callee).unwrap_or_default();
            panic!("no signature for {} {name}", r.element_type(callee));
        };
        let parameters: Vec<_> = parameters.into_iter().map(|p| p.element).collect();
        if parameters.is_empty() && inherited.is_empty() {
            continue;
        }
        checked += 1;
        if parameters != inherited {
            let metaclass = r.element_type(callee);
            let name = r.element_qualified_name(callee).unwrap_or_default();
            let spell = |r: &mut ResolvedModel, list: &[ElementRef]| {
                list.iter()
                    .map(|&p| r.element_qualified_name(p).unwrap_or_default())
                    .collect::<Vec<_>>()
            };
            let (walk, view) = (spell(&mut r, &parameters), spell(&mut r, &inherited));
            let difference = format!("{metaclass} {name}: walk {walk:?}, view {view:?}");
            assert!(
                matches!(metaclass, "PerformActionUsage" | "Step" | "ReferenceUsage"),
                "{difference}"
            );
            differ.push(difference);
        }
    }
    assert!(checked > 6000, "only {checked} types with parameters");
    assert!(differ.len() <= 13, "{differ:#?}");
}

/// Arguments bind inherited parameters by position, whatever the
/// specialization names its own: `Swapped`'s first parameter `b` stands
/// for `Diff::a`.
#[test]
fn arguments_bind_by_position_not_by_name() {
    let decls = "calc def Diff { in a; in b; a - b }
                 calc def Swapped :> Diff { in b; in a; }
                 calc def Renamed :> Diff { in x; in y; }";
    assert_eq!(eval_with(decls, "Swapped(10, 3)"), Ok(int(7)));
    assert_eq!(eval_with(decls, "Swapped(b = 10, a = 3)"), Ok(int(7)));
    assert_eq!(eval_with(decls, "Renamed(10, 3)"), Ok(int(7)));
    assert_eq!(eval_with(decls, "Renamed(y = 3, x = 10)"), Ok(int(7)));
}

/// Units normalize to exponent maps: derived-unit definitions expand,
/// `*`/`/`/`**` combine exponents and cancel, reciprocals and rational
/// powers work — still with zero unit *conversion*.
#[test]
fn unit_normalization() {
    let units = "attribute mm; attribute kg; attribute m; attribute s;
                 attribute mps = m / s; attribute N = kg * m / s ** 2;";
    // A derived unit is dimensionally equal to its definition.
    assert_eq!(
        eval_with(units, "1 [mps] + 1 [m/s]"),
        Ok(Value::Quantity(
            Box::new(int(2)),
            unit_probe_with(units, "m/s")
        ))
    );
    assert_eq!(
        eval_with(units, "1 [N] == 1 [kg*m/s**2]"),
        Ok(Value::Boolean(true))
    );
    // Multiplication and division cancel dimensions.
    assert_eq!(
        eval_with(units, "(4 [m/s]) * (2 [s])"),
        Ok(Value::Quantity(
            Box::new(int(8)),
            unit_probe_with(units, "m")
        ))
    );
    assert_eq!(
        eval_with(units, "(10 [m]) / (5 [m/s])"),
        Ok(Value::Quantity(
            Box::new(int(2)),
            unit_probe_with(units, "s")
        ))
    );
    // A scalar over a quantity has the reciprocal unit.
    assert_eq!(
        eval_with(units, "2 / (4 [s])"),
        Ok(Value::Quantity(
            Box::new(rat(1, 2)),
            // `m/(m*s)` cancels to the reciprocal second.
            unit_probe_with(units, "m/(m*s)")
        ))
    );
    // Rational powers scale the exponents (`^(1/2)` is a root); sqrt is
    // the same operation.
    assert_eq!(
        eval_with(units, "(9 [m**2]) ** (1/2)"),
        Ok(Value::Quantity(
            Box::new(int(3)),
            unit_probe_with(units, "m")
        ))
    );
    assert_eq!(
        eval_with(units, "sqrt(9 [m**2])"),
        Ok(Value::Quantity(
            Box::new(int(3)),
            unit_probe_with(units, "m")
        ))
    );
    // Full cancellation leaves a plain number.
    assert_eq!(
        eval_with(units, "(6 [m/s]) * (2 [s]) / (4 [m])"),
        Ok(int(3))
    );
    // Base units stay distinct — normalization is erasure, not conversion.
    assert!(matches!(
        eval_with(units, "1 [mm] + 1 [m]"),
        Err(EvalError::Type(_))
    ));
}

/// A quoted unit name that *spells* a power product (`'m³⋅s⁻²'`)
/// expands by parsing the spelling when the element has no definition
/// or conversion of its own — so it converts against the units it is
/// spelled from. Enabled by default; the opt-out lives in its own test
/// binary (the switch is process-wide).
#[test]
fn unit_spelling_expansion() {
    let units = "attribute m; attribute s; attribute kg;
                 attribute <'m³⋅s⁻²'> 'metre cubed per second squared';
                 attribute <'m⋅s⁻¹'> 'metre per second';
                 attribute <'kg/m³'> 'kilogram per metre cubed';
                 attribute <'x⋅y⁻¹'> 'x per y';";
    // The spelled product is dimensionally the spelled-out expression.
    assert_eq!(
        eval_with(units, "1 ['m³⋅s⁻²'] == 1 [m**3/s**2]"),
        Ok(Value::Boolean(true))
    );
    // Mixed spellings of one dimension combine (the Apollo LOI shape:
    // a squared speed plus a gravitational parameter over a length).
    assert_eq!(
        eval_with(units, "(2 ['m⋅s⁻¹']) ** 2 + 1 ['m³⋅s⁻²'] / (1 [m])"),
        Ok(Value::Quantity(
            Box::new(int(5)),
            unit_probe_with(units, "m**2/s**2"),
        ))
    );
    // Slash spellings divide the following factor.
    assert_eq!(
        eval_with(units, "1 ['kg/m³'] == 1 [kg/m**3]"),
        Ok(Value::Boolean(true))
    );
    // A spelling that fails to resolve a component stays an opaque
    // base — distinct from everything else.
    assert!(matches!(
        eval_with(units, "1 ['x⋅y⁻¹'] + 1 [m/s]"),
        Err(EvalError::Type(_))
    ));
}

/// A plain zero is the additive identity of every dimension (empty
/// rollups produce it); any other plain number still refuses to mix.
#[test]
fn quantity_zero_identity() {
    let units = "attribute kg;";
    let kg = || unit_probe_with(units, "kg");
    assert_eq!(
        eval_with(units, "0 + 5 [kg]"),
        Ok(Value::Quantity(Box::new(int(5)), kg()))
    );
    assert_eq!(
        eval_with(units, "5 [kg] - 0"),
        Ok(Value::Quantity(Box::new(int(5)), kg()))
    );
    assert_eq!(
        eval_with(units, "0 - 5 [kg]"),
        Ok(Value::Quantity(Box::new(int(-5)), kg()))
    );
    assert!(matches!(
        eval_with(units, "1 + 5 [kg]"),
        Err(EvalError::Type(_))
    ));
    // sum/product fold through quantity arithmetic.
    assert_eq!(
        eval_with(units, "sum((1 [kg], 2 [kg]))"),
        Ok(Value::Quantity(Box::new(int(3)), kg()))
    );
    assert_eq!(
        eval_with("attribute m;", "product((2 [m], 3 [m]))"),
        Ok(Value::Quantity(
            Box::new(int(6)),
            unit_probe_with("attribute m;", "m**2")
        ))
    );
}

/// Chain steps over a multi-valued source map the member access and keep
/// every value, per KFL `'.'` (its `source` and `target` are declared
/// nonunique): three parts with one value read as three values, so a
/// rollup over equal values counts each of them.
#[test]
fn chain_over_sequence_maps_and_keeps_duplicates() {
    let decls = "part def E { attribute v = 304; }
                 part def P { attribute m; }
                 part e1 : E[1]; part e2 : E[1]; part e3 : E[1];
                 part a : P[1] { attribute :>> m = 1; }
                 part b : P[1] { attribute :>> m = 2; }
                 part c : P[1] { attribute :>> m = 1; }
                 part s[1] { part es = (e1, e2, e3); part ps = (a, b, c); }";
    assert_eq!(
        eval_with(decls, "s.es.v"),
        Ok(Value::Sequence(vec![int(304), int(304), int(304)]))
    );
    assert_eq!(eval_with(decls, "sum(s.es.v)"), Ok(int(912)));
    assert_eq!(
        eval_with(decls, "s.ps.m"),
        Ok(Value::Sequence(vec![int(1), int(2), int(1)]))
    );
    assert_eq!(eval_with(decls, "sum(s.ps.m)"), Ok(int(4)));
    assert_eq!(eval_with(decls, "size((a, a).m)"), Ok(int(2)));
}

/// Featuring contexts persist through nested simple-name references:
/// an inherited expression chain re-resolves each step against the
/// instance it was reached through, and a recursive rollup re-enters
/// the same feature under each subcomponent's context.
#[test]
fn featuring_context_depth_and_recursive_rollup() {
    let deep = "part def V {
                    attribute total = m2 + 1;
                    attribute m2 = base * 2;
                    attribute base;
                }
                part car : V[1] { attribute :>> base = 10; }";
    assert_eq!(eval_with(deep, "car.total"), Ok(int(21)));
    let rollup = "part def M {
                      part subs : M [*] default null;
                      attribute mass;
                      attribute totalMass = mass + sum(subs.totalMass);
                  }
                  part leaf1 : M[1] { attribute :>> mass = 1; }
                  part leaf2 : M[1] { attribute :>> mass = 2; }
                  part root : M[1] {
                      attribute :>> mass = 5;
                      part :>> subs = (leaf1, leaf2);
                  }";
    assert_eq!(eval_with(rollup, "root.totalMass"), Ok(int(8)));
}

/// Unit conversion via measurement references: a unit with a
/// Quantity brackets over non-scalar magnitudes: re-tagging an existing
/// quantity converts within its dimension (`(2 [min]) [s]` = 120 [s]);
/// across dimensions the explicit annotation wins (see
/// `bracket_over_quantity` for the precedence rationale); a sequence
/// magnitude is a *vector* quantity (`(1670, 720, 80) [f]` — the
/// coordinate-frame spelling of the geometry examples), keeping
/// components that already carry their own unit verbatim; an unknown
/// component makes the vector indeterminate; non-numeric components
/// stay type errors.
#[test]
fn quantity_brackets_convert_and_take_vectors() {
    let units = "attribute s; attribute m; attribute f; attribute u;
                 attribute min {
                     attribute unitConversion {
                         attribute referenceUnit = s;
                         attribute conversionFactor = 60;
                     }
                 }";
    // Same-unit re-tag is the identity.
    assert_eq!(
        eval_with(units, "(10 [s] + 5 [s]) [s]"),
        Ok(Value::Quantity(
            Box::new(int(15)),
            unit_probe_with(units, "s")
        ))
    );
    // Same-dimension re-tags convert both ways.
    assert_eq!(
        eval_with(units, "(2 [min]) [s]"),
        Ok(Value::Quantity(
            Box::new(int(120)),
            unit_probe_with(units, "s")
        ))
    );
    assert_eq!(
        eval_with(units, "(120 [s]) [min]"),
        Ok(Value::Quantity(
            Box::new(int(2)),
            unit_probe_with(units, "min")
        ))
    );
    // Vector magnitudes convert component-wise rather than merely changing
    // the displayed unit.
    assert_eq!(
        eval_with(units, "((2, 3) [min]) [s]"),
        Ok(Value::Quantity(
            Box::new(Value::Sequence(vec![int(120), int(180),])),
            unit_probe_with(units, "s")
        ))
    );
    // Across dimensions the annotation wins — the magnitude as written.
    assert_eq!(
        eval_with(units, "(1 [m]) [s]"),
        Ok(Value::Quantity(
            Box::new(int(1)),
            unit_probe_with(units, "s")
        ))
    );
    // A sequence magnitude is a vector quantity.
    assert_eq!(
        eval_with(units, "(1670, 720, 80) [f]"),
        Ok(Value::Quantity(
            Box::new(Value::Sequence(vec![int(1670), int(720), int(80)])),
            unit_probe_with(units, "f")
        ))
    );
    // Components carrying their own unit stay verbatim.
    assert_eq!(
        eval_with(units, "(0, 7.5 [m], 0) [f]"),
        Ok(Value::Quantity(
            Box::new(Value::Sequence(vec![
                int(0),
                Value::Quantity(Box::new(rat(15, 2)), unit_probe_with(units, "m")),
                int(0),
            ])),
            unit_probe_with(units, "f")
        ))
    );
    // An unknown component makes the vector indeterminate; a non-numeric
    // one is still a type error.
    assert_eq!(eval_with(units, "(1, u, 0) [f]"), Ok(Value::Indeterminate));
    assert!(matches!(
        eval_with(units, "(1, \"x\") [f]"),
        Err(EvalError::Type(_))
    ));
}

/// library-shaped `unitConversion` (factor + reference, or prefix)
/// normalizes to its reference dimensions with the factor as scale, so
/// same-dimension quantities convert at operation boundaries. Combined
/// results fold their scales into the number; different dimensions
/// still refuse to mix.
#[test]
fn unit_conversion_via_measurement_references() {
    let units = "attribute s; attribute m;
                 attribute kilo { attribute conversionFactor = 1000; }
                 attribute min {
                     attribute unitConversion {
                         attribute referenceUnit = s;
                         attribute conversionFactor = 60;
                     }
                 }
                 attribute km {
                     attribute unitConversion {
                         attribute prefix = kilo;
                         attribute referenceUnit = m;
                     }
                 }";
    // Additive ops convert into the left operand's unit.
    assert_eq!(
        eval_with(units, "30 [min] + 30 [s]"),
        Ok(Value::Quantity(
            Box::new(rat(61, 2)),
            unit_probe_with(units, "min")
        ))
    );
    // Comparisons and equality convert.
    assert_eq!(
        eval_with(units, "1 [min] == 60 [s]"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(units, "1 [km] > 999 [m]"),
        Ok(Value::Boolean(true))
    );
    // Multiplied results fold the scales into the number and take the
    // reference spelling.
    assert_eq!(
        eval_with(units, "2 [km] * (2 [m])"),
        Ok(Value::Quantity(
            Box::new(int(4000)),
            unit_probe_with(units, "m**2")
        ))
    );
    // Division cancels dimensions across scales.
    assert_eq!(eval_with(units, "1 [km] / (500 [m])"), Ok(int(2)));
    // Different dimensions are still a type error — conversion applies
    // only within one dimension.
    assert!(matches!(
        eval_with(units, "1 [km] + 1 [s]"),
        Err(EvalError::Type(_))
    ));
}

/// An absent name is a null property: a reference unit with only a
/// declared name still spells the results it reaches, and an enum
/// literal with only a short name renders by it.
#[test]
fn names_fall_back_past_absent_properties() {
    let units = "attribute s; attribute m;
                 attribute 'in' {
                     attribute unitConversion {
                         attribute referenceUnit = m;
                         attribute conversionFactor = 0.0254;
                     }
                 }";
    assert_eq!(
        eval_with(units, "10 ['in'] / (2 [s])").unwrap().to_string(),
        "0.127 [m/s]"
    );
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        "package T { enum def Level { enum <lo>; enum <hi> high; }
             attribute a = Level::lo; attribute b = Level::hi; }",
    );
    let mut r = ResolvedModel::build(&model);
    for (name, shown) in [("T::a", "lo"), ("T::b", "high")] {
        let e = r.resolve_qualified(name).unwrap();
        let v = r.evaluate(e).unwrap();
        assert_eq!(r.render_value(&v), shown, "{name}");
    }
}

/// Library-shaped units in two systems for the as-written tests: SI
/// bases with `kg` prefixed from `g` and `N` defined from them, inches,
/// feet, miles and pounds converting to SI, and hours and minutes.
const WRITTEN_UNITS: &str = "attribute s; attribute m; attribute g;
     attribute kilo { attribute conversionFactor = 1000; }
     attribute kg {
         attribute unitConversion { attribute prefix = kilo; attribute referenceUnit = g; }
     }
     attribute km {
         attribute unitConversion { attribute prefix = kilo; attribute referenceUnit = m; }
     }
     attribute N = kg*m/s^2;
     attribute 'in' {
         attribute unitConversion { attribute referenceUnit = m; attribute conversionFactor = 0.0254; }
     }
     attribute ft {
         attribute unitConversion { attribute referenceUnit = 'in'; attribute conversionFactor = 12; }
     }
     attribute mi {
         attribute unitConversion { attribute referenceUnit = ft; attribute conversionFactor = 5280; }
     }
     attribute lb {
         attribute unitConversion { attribute referenceUnit = kg; attribute conversionFactor = 0.45359237; }
     }
     attribute lbf {
         attribute unitConversion { attribute referenceUnit = N; attribute conversionFactor = 4.4482216152605; }
     }
     attribute h {
         attribute unitConversion { attribute referenceUnit = s; attribute conversionFactor = 3600; }
     }
     attribute min {
         attribute unitConversion { attribute referenceUnit = s; attribute conversionFactor = 60; }
     }";

/// `expr` (as `attribute result = <expr>;` beside the units), evaluated,
/// and its value re-expressed in the units it was written in.
fn eval_written(expr: &str) -> (Value, Option<Value>) {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        &format!("package T {{ {WRITTEN_UNITS} attribute result = {expr}; }}"),
    );
    let mut r = ResolvedModel::build(&model);
    let e = r.resolve_qualified("T::result").expect("result resolves");
    let v = r.evaluate(e).unwrap_or_else(|e| panic!("{expr}: {e:?}"));
    let as_written = r.value_as_written(&v);
    (v, as_written)
}

/// `expr`'s value as the evaluator renders it, then re-expressed in the
/// units it was written in (the same string when it already is).
fn written(expr: &str) -> (String, String) {
    let (v, as_written) = eval_written(expr);
    let shown = as_written.map_or_else(|| v.to_string(), |w| w.to_string());
    (v.to_string(), shown)
}

/// `quantities_as_written` reaches the quantities inside a sequence and an
/// instance's fields, and leaves every other value as it is.
#[test]
fn nested_quantities_re_express_in_their_written_units() {
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        &format!(
            "package T {{ {WRITTEN_UNITS}
                attribute d = 10 ['in'];
                attribute pair = (d / (2 [s]), d * d, 3, \"x\");
                attribute def Box {{ attribute speed; attribute label; }}
                attribute box = new Box(d / (2 [s]), \"b\");
            }}"
        ),
    );
    let mut r = ResolvedModel::build(&model);
    let eval = |r: &mut ResolvedModel, name: &str| {
        let e = r.resolve_qualified(name).expect("resolves");
        r.evaluate(e).unwrap_or_else(|e| panic!("{name}: {e:?}"))
    };
    let pair = eval(&mut r, "T::pair");
    assert_eq!(pair.to_string(), "(0.127 [m/s], 0.064516 [m**2], 3, \"x\")");
    assert_eq!(
        r.quantities_as_written(&pair).to_string(),
        "(5 [in/s], 100 [in**2], 3, \"x\")"
    );
    let boxed = eval(&mut r, "T::box");
    assert_eq!(
        r.quantities_as_written(&boxed).to_string(),
        boxed.to_string().replace("0.127 [m/s]", "5 [in/s]")
    );
    assert!(boxed.to_string().contains("0.127 [m/s]"), "{boxed}");
    // Already as written, and not a quantity at all: unchanged.
    let d = eval(&mut r, "T::d");
    assert_eq!(r.quantities_as_written(&d), d);
    assert_eq!(
        r.quantities_as_written(&Value::Integer(3)),
        Value::Integer(3)
    );
}

/// Products, quotients and powers fold into the reference units; the
/// written units they came from re-express them: a written unit (or a
/// power of one) with the result's dimensions first, then a named
/// compound unit with written units for the rest, then a written unit
/// per dimension.
#[test]
fn quantities_re_express_in_their_written_units() {
    // One written unit per dimension.
    assert_eq!(
        written("10 ['in'] / (2 [s])"),
        ("0.127 [m/s]".into(), "5 [in/s]".into())
    );
    assert_eq!(written("60 [mi] / (1 [h])").1, "60 [mi/h]");
    assert_eq!(
        written("2 [lb] * (32 [ft]) / (1 [s])**2").1,
        "64 [ft*lb/s**2]"
    );
    assert_eq!(written("2 [kg] * (3 [m/s^2])").1, "6 [kg*m/s**2]");
    // A written unit with the result's dimensions, or a power of one.
    assert_eq!(written("60 [mi] / (1 [h]) * (30 [min])").1, "30 [mi]");
    assert_eq!(written("10 ['in'] * (10 ['in'])").1, "100 [in**2]");
    assert_eq!(
        written("2 ['in'] * (3 ['in']) * (4 ['in'])").1,
        "24 [in**3]"
    );
    assert_eq!(written("2 / (4 [h])").1, "0.5 [1/h]");
    assert_eq!(written("(3 [km/h]) ** 2").1, "9 [(km/h)**2]");
    // A named compound unit with written units for what it leaves.
    assert_eq!(written("10 [N] * (2 [m])").1, "20 [N*m]");
    assert_eq!(written("10 [N] / (2 [m^2])").1, "5 [N/m**2]");
    assert_eq!(
        written("10 [lbf] / (2 ['in'] * (1 ['in']))").1,
        "5 [lbf/in**2]"
    );
    assert_eq!(written("10 [N] / (5 [lb])").1, "2 [N/lb]");
    // Each dimension takes the first unit written for it.
    assert_eq!(written("60 [km/h] / (10 [s])").1, "21600 [km/h**2]");
    assert_eq!(written("1 [ft] * (12 ['in'])").1, "1 [ft**2]");
}

/// Units the evaluator already keeps as written stay as they are:
/// brackets, additive and scalar operations (which convert into the left
/// operand's unit), explicit conversions, and reference units nothing
/// else was written for. Dimensionless results are plain numbers.
#[test]
fn written_units_already_shown_stay() {
    for expr in [
        "10 ['in']",
        "10 ['in'] + 1 [ft]",
        "1 [ft] + 12 ['in']",
        "10 ['in'] / 2",
        "-(10 ['in'])",
        "(10 ['in'] / (2 [s])) [m/s]",
        "(10 ['in'] / (2 [s])) [km/h]",
        "2 [m] * (3 [m])",
        "3 [km/h] * 2",
        // `N/kg` is exactly the reference `m/s**2`: an equal unit keeps
        // the evaluator's spelling.
        "10 [N] / (5 [kg])",
    ] {
        let (v, as_written) = eval_written(expr);
        assert_eq!(as_written, None, "{expr} is already as written: {v}");
    }
    assert_eq!(eval_with(WRITTEN_UNITS, "12 ['in'] / (1 [ft])"), Ok(int(1)));
    // A sum whose left operand was folded takes a written unit of its
    // dimensions from either side.
    assert_eq!(
        written("10 ['in'] * (10 ['in']) + 1 [ft^2]").1,
        "244 [in**2]"
    );
}

/// The renderer picks the unit display per call, recursing through
/// sequences, and leaves everything else to the number format.
#[test]
fn render_value_in_chooses_the_unit_display() {
    use sysmlv2_parser::eval::UnitDisplay;
    use sysmlv2_parser::numfmt::NumberFormat;
    let mut model = Model::new();
    model.add_source(
        "t.sysml",
        &format!(
            "package T {{ {WRITTEN_UNITS}
                 attribute d = 10 ['in'];
                 attribute t = 3 [s];
                 attribute pair = (d / t, d * d);
             }}"
        ),
    );
    let mut r = ResolvedModel::build(&model);
    let e = r.resolve_qualified("T::pair").unwrap();
    let v = r.evaluate(e).unwrap();
    let exact = NumberFormat::exact();
    assert_eq!(
        r.render_value_in(&v, &exact, UnitDisplay::Si),
        r.render_value_as(&v, &exact)
    );
    assert_eq!(
        r.render_value_in(&v, &exact, UnitDisplay::Si),
        "(127/1500 [m/s], 0.064516 [m**2])"
    );
    assert_eq!(
        r.render_value_in(&v, &exact, UnitDisplay::AsWritten),
        "(10/3 [in/s], 100 [in**2])"
    );
    assert_eq!(
        r.render_value_in(&v, &NumberFormat::approx(), UnitDisplay::AsWritten),
        "(≈3.3333333333333335 [in/s], 100 [in**2])"
    );
    assert_eq!(UnitDisplay::parse("asWritten"), Ok(UnitDisplay::AsWritten));
    assert_eq!(UnitDisplay::parse("si"), Ok(UnitDisplay::Si));
    assert!(UnitDisplay::parse("SI").is_err());
}

/// A bracket over an already-dimensioned value: same dimensions convert
/// across scales; different dimensions take the magnitude as written —
/// the explicit annotation wins. The normative precedence binds a
/// trailing unit to the last primary, so `mass / rho [kg]` annotates
/// `rho`, and a hard error there would poison every downstream value.
#[test]
fn bracket_over_quantity() {
    let units = "attribute s; attribute m;
                 attribute kg;
                 attribute min {
                     attribute unitConversion {
                         attribute referenceUnit = s;
                         attribute conversionFactor = 60;
                     }
                 }";
    // Same dimensions: a real conversion.
    assert_eq!(
        eval_with(units, "(90 [s]) [min]"),
        Ok(Value::Quantity(
            Box::new(rat(3, 2)),
            unit_probe_with(units, "min")
        ))
    );
    assert_eq!(
        eval_with(units, "(1.5 [min]) [s]"),
        Ok(Value::Quantity(
            Box::new(int(90)),
            unit_probe_with(units, "s")
        ))
    );
    // The same unit again is a no-op.
    assert_eq!(
        eval_with(units, "(5 [kg]) [kg]"),
        Ok(Value::Quantity(
            Box::new(int(5)),
            unit_probe_with(units, "kg")
        ))
    );
    // Different dimensions: the annotation retags the magnitude.
    assert_eq!(
        eval_with(units, "(2 [m]) [kg]"),
        Ok(Value::Quantity(
            Box::new(int(2)),
            unit_probe_with(units, "kg")
        ))
    );
    // The motivating idiom: dividing by an annotated quantity keeps the
    // whole expression computable (`100 [kg] / rho [kg]` cancels).
    assert_eq!(eval_with(units, "100 [kg] / (50 [m] [kg])"), Ok(int(2)));
}

/// Classification operators (KFL BaseFunctions): `istype` walks the
/// explicit specialization closure, `hastype` tests direct typing,
/// `as` filters a sequence to the conforming values. Open-world rules
/// for model features: a conformance hit is a definite true, a miss —
/// and any hastype — is undecided (the instance may be more specific
/// than declared); constructed instances and scalar literals are
/// closed and answer false.
#[test]
fn classification_operators() {
    let decls = "part def Component;
                 part def Engine :> Component;
                 part def Wheel :> Component;
                 part e : Engine[1];
                 part w : Wheel[1];
                 part parts = (e, w);";
    // Declared conformance is a guaranteed true.
    assert_eq!(
        eval_with(decls, "e istype Engine"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(decls, "e istype Component"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(decls, "parts istype Component"),
        Ok(Value::Boolean(true))
    );
    // A miss on a model feature is undecided, never false — e's
    // instance could be classified more specifically than `Engine`.
    // Undecided is a first-class indeterminate value, not an error.
    assert_eq!(eval_with(decls, "e istype Wheel"), Ok(Value::Indeterminate));
    // hastype asks about the instance's direct type — undecided for
    // model features even when the declared typing matches.
    assert_eq!(
        eval_with(decls, "e hastype Engine"),
        Ok(Value::Indeterminate)
    );
    // An undecided cast keeps the value (the annotation asserts, it
    // does not test): `e as Wheel` still stands for e.
    assert_eq!(eval_with(decls, "size(e as Wheel)"), Ok(int(1)));
    // Constructed instances are closed values: both answers work.
    let data = "attribute def A; attribute def B :> A;
                attribute a = new A(); attribute b = new B();";
    assert_eq!(eval_with(data, "b istype A"), Ok(Value::Boolean(true)));
    assert_eq!(eval_with(data, "a istype B"), Ok(Value::Boolean(false)));
    assert_eq!(eval_with(data, "b hastype B"), Ok(Value::Boolean(true)));
    assert_eq!(eval_with(data, "b hastype A"), Ok(Value::Boolean(false)));
    // `as` filters closed values to the conforming ones.
    assert_eq!(eval_with(data, "size((a, b) as B)"), Ok(int(1)));
    assert_eq!(eval_with(data, "size((a, b) as A)"), Ok(int(2)));
    // Scalar literals classify by the ScalarValues hierarchy.
    let sv = "attribute def Integer; attribute def Real; attribute def MyType;";
    assert_eq!(eval_with(sv, "2 istype Integer"), Ok(Value::Boolean(true)));
    assert_eq!(eval_with(sv, "2 istype Real"), Ok(Value::Boolean(true)));
    assert_eq!(
        eval_with(sv, "2.5 istype Integer"),
        Ok(Value::Boolean(false))
    );
    assert_eq!(eval_with(sv, "2 hastype Real"), Ok(Value::Boolean(false)));
    assert_eq!(eval_with(sv, "2 istype MyType"), Ok(Value::Boolean(false)));
}

/// A redefining feature with no value of its own inherits the redefinition
/// target's `default` value expression, re-evaluated in the redefining
/// context so redefined sub-features shadow — the configured-variant
/// roll-up pattern (`attribute :>> weight;` under a narrowed structure
/// recomputes the general default from the narrowed values). Non-default
/// inherited values do NOT propagate: whether a plain `=` binding survives
/// redefinition is spec-ambiguous, so those features stay unbound.
#[test]
fn redefinition_inherits_default_value_expressions() {
    let decls = "
        part def Weighed { attribute weight; }
        part def Bundle :> Weighed {
            attribute :>> weight default lhs.weight + rhs.weight;
            part lhs : Weighed;
            part rhs : Weighed;
        }
        part def Trimmed :> Bundle {
            attribute :>> weight;
            part :>> lhs { attribute :>> weight = 3; }
            part :>> rhs { attribute :>> weight = 4; }
        }
        attribute base = 1;
        part def P { attribute x = base; }
        part def Q :> P { attribute :>> x; }
    ";
    // The bare `:>> weight` computes the inherited default over the
    // narrowed structure.
    assert_eq!(eval_with(decls, "Trimmed::weight"), Ok(int(7)));
    // A non-default inherited binding stays unbound (a placeholder).
    assert!(matches!(eval_with(decls, "Q::x"), Ok(Value::Unbound(..))));
}

/// Lib-gated: `performedActions` roll-ups. A `perform x;` member
/// implicitly subsets the library `performedActions` feature of the
/// owning part, so the *general* collection form — filter the performed
/// actions by type, then collect and fold an attribute — evaluates
/// without spelling out each performance.
#[test]
fn performed_actions_rollup_evaluates() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "rollup.sysml",
        "package Tally {
            private import ScalarValues::*;
            action def Chore { attribute effort : Real default 0; }
            action c1 : Chore[1] { attribute :>> effort = 4.0; }
            action c2 : Chore[1] { attribute :>> effort = 9.0; }
            action c3 : Chore[1] { attribute :>> effort = 100.0; }
            part worker[1] {
                perform c1;
                perform c2;
            }
            part audit {
                attribute total : Real =
                    RealFunctions::sum((worker.performedActions as Chore).effort);
            }
        }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let e = r
        .resolve_qualified("Tally::audit::total")
        .expect("total resolves");
    // c1 + c2 are performed (4 + 9); c3 exists but is not performed.
    assert_eq!(r.evaluate(e), Ok(int(13)));
}

/// A bare unbound feature is a placeholder for an *unknown* sequence:
/// counting answers come from the declared multiplicity — an exact
/// `[n]` answers n, a lower bound settles non-emptiness, everything
/// else answers *indeterminate* rather than fabricating (the
/// placeholder used to count as one element, silently mis-measuring
/// every multi-valued feature and making `(1..size(xs)-1)->forAll`
/// bodies vacuously true). Sequence literals cannot establish the arity
/// of unknown collections, and enum literals stay closed one-element values.
#[test]
fn unbound_cardinality_comes_from_declared_multiplicity() {
    let decls = "
        part def D;
        part rack[1] {
            part slots[3] : D;
            part gear[1..*] : D;
            part loose[0..2] : D;
            part lone : D;
        }
        enum def Mode { ON; OFF; }
    ";
    // Exact declared multiplicity answers.
    assert_eq!(eval_with(decls, "size(rack.slots)"), Ok(int(3)));
    // A structural usage inside a usage has implicit multiplicity `[1..1]`.
    assert_eq!(eval_with(decls, "size(rack.lone)"), Ok(int(1)));
    // A lower bound settles non-emptiness; the size stays unknown.
    assert_eq!(
        eval_with(decls, "notEmpty(rack.gear)"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(decls, "size(rack.gear)"),
        Ok(Value::Indeterminate)
    );
    // A `[0..u]` range settles neither.
    assert_eq!(
        eval_with(decls, "isEmpty(rack.loose)"),
        Ok(Value::Indeterminate)
    );
    // Flat sequences cannot wrap unknown collections into scalar placeholders.
    assert_eq!(
        eval_with(decls, "size((rack.gear, rack.loose))"),
        Ok(Value::Indeterminate)
    );
    // Enum literals stay closed single values.
    assert_eq!(eval_with(decls, "size(Mode::ON)"), Ok(int(1)));

    // Indexing an unknown collection answers from the same declared
    // bounds: an admitted index is an unknown item (indeterminate — a
    // whole-collection placeholder would mis-answer cardinality
    // questions downstream), a declared singleton's `#(1)` is the value
    // itself, and an index beyond a finite upper bound is out of bounds
    // like a concrete sequence.
    assert_eq!(eval_with(decls, "rack.slots#(2)"), Ok(Value::Indeterminate));
    assert_eq!(
        eval_with(decls, "rack.gear#(7)"),
        Ok(Value::Indeterminate),
        "no finite upper bound admits any index"
    );
    assert!(matches!(
        eval_with(decls, "rack.lone#(1)"),
        Ok(Value::Unbound(..))
    ));
    assert!(matches!(
        eval_with(decls, "rack.slots#(5)"),
        Err(EvalError::Type(_))
    ));
    assert!(matches!(
        eval_with(decls, "rack.slots#(0)"),
        Err(EvalError::Type(_))
    ));
}

#[test]
fn cardinality_inherits_redefinitions_without_rounding_or_guessing() {
    let decls = "
        part def Rack { part slots[4]; }
        part def Middle :> Rack { part :>> slots; }
        part rack : Middle[1] { part :>> slots; }
        part huge[9007199254740993];
        part optional[0..1];
        part def Left { part slots[2..5]; }
        part def Right { part slots[4..7]; }
        part both[1] { part slots :>> Left::slots, Right::slots; }
        part missing[1] { part slots :>> Left::slots, absent; }
        part cyclic :>> cyclic;
        part a :>> b; part b :>> a;
        attribute count = size(recursive);
        part recursive[count];
        attribute unknown;
        part invalid[unknown] :>> Rack::slots;
        attribute neg = -1; part negative[neg];
    ";
    assert_eq!(eval_with(decls, "size(rack.slots)"), Ok(int(4)));
    assert_eq!(eval_with(decls, "size(huge)"), Ok(int(9007199254740993)));
    assert!(matches!(
        eval_with(decls, "huge#(9007199254740994)"),
        Err(EvalError::Type(_))
    ));
    assert_eq!(eval_with(decls, "optional#(1)"), Ok(Value::Indeterminate));
    assert_eq!(
        eval_with(decls, "notEmpty(both.slots)"),
        Ok(Value::Boolean(true))
    );
    for expr in [
        "size(both.slots)",
        "size(missing.slots)",
        "size(cyclic)",
        "size(a)",
        "size(recursive)",
        "size(invalid)",
        "size(negative)",
    ] {
        assert_eq!(eval_with(decls, expr), Ok(Value::Indeterminate), "{expr}");
    }
}

#[test]
fn cardinality_defaults_follow_usage_kind_owner_and_subsetting() {
    let mut model = Model::new();
    model.add_source(
        "defaults.sysml",
        r#"
        package P {
            attribute a; item i; part p; port q;
            part def D {
                attribute a; item i; part p; port q;
                ref item reference; in attribute input;
                connection c; interface face; allocation alloc;
                action act; occurrence occ; ref generic;
                package Nested { attribute a; part p; }
            }
            part holder { attribute a; item i; part p; port q; }
            part explicit[1];
            part base[2..5]; part other[4..7];
            part subset :> base; part intersection :> base, other;
            part smaller[1] :> base;
            part chain :>> subset; part mixed :> base :>> other;
            part missing :> absent; part partial :> base, absent;
            part cycle :> cycle; part ca :> cb; part cb :>> ca;
            part noBound; part inheritedDefault :> noBound;
            part Dsubset :> D::p;
            part low[0..1]; part conflict :> base, low;
            part def Container { part subset :> P::base; }
        }
    "#,
    );
    model.add_source(
        "defaults.kerml",
        "package K { feature a; class C { feature a; } }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    for name in [
        "D::a",
        "D::i",
        "D::p",
        "D::q",
        "D::reference",
        "D::input",
        "holder::a",
        "holder::i",
        "holder::p",
        "holder::q",
        "explicit",
        "Dsubset",
    ] {
        let e = r.resolve_qualified(&format!("P::{name}")).unwrap();
        assert_eq!(r.effective_cardinality(e), Some((1, Some(1))), "{name}");
    }
    for name in [
        "P::a",
        "P::i",
        "P::p",
        "P::q",
        "P::holder",
        "P::D::c",
        "P::D::face",
        "P::D::alloc",
        "P::D::act",
        "P::D::occ",
        "P::D::generic",
        "P::D::Nested::a",
        "P::D::Nested::p",
        "P::inheritedDefault",
        "K::a",
        "K::C::a",
    ] {
        let e = r.resolve_qualified(name).unwrap();
        assert_eq!(r.effective_cardinality(e), Some((0, None)), "{name}");
    }
    for (name, bounds) in [
        ("subset", (2, Some(5))),
        ("intersection", (4, Some(5))),
        ("smaller", (1, Some(1))),
        ("chain", (2, Some(5))),
        ("mixed", (4, Some(5))),
        ("Container::subset", (2, Some(5))),
    ] {
        let e = r.resolve_qualified(&format!("P::{name}")).unwrap();
        assert_eq!(r.effective_cardinality(e), Some(bounds), "{name}");
    }
    for name in ["missing", "partial", "cycle", "ca", "conflict"] {
        let e = r.resolve_qualified(&format!("P::{name}")).unwrap();
        assert_eq!(r.effective_cardinality(e), None, "{name}");
    }
}

#[test]
fn inherited_subsetting_bounds_control_collection_operations() {
    let decls = "part base[4]; part middle :> base; part inherited :>> middle;
        part empty[0]; part emptySubset :> empty;
        part variable[2..5]; part variableSubset :> variable;
        part unknown; part def D { part singleton; }";
    assert_eq!(eval_with(decls, "size(inherited)"), Ok(int(4)));
    assert_eq!(
        eval_with(decls, "isEmpty(emptySubset)"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(decls, "notEmpty(variableSubset)"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(eval_with(decls, "size(unknown)"), Ok(Value::Indeterminate));
    assert_eq!(eval_with(decls, "size(D::singleton)"), Ok(int(1)));
    assert!(matches!(
        eval_with(decls, "inherited#(5)"),
        Err(EvalError::Type(_))
    ));
}

#[test]
fn unsupported_owned_multiplicities_and_subsettings_stay_unknown() {
    let mut model = Model::new();
    let unit = model.add_source(
        "unsupported.kerml",
        "package K {
            feature base[2];
            feature ranged { multiplicity [3]; }
            feature named { multiplicity bounds [4]; }
            feature conflicting[1] { multiplicity bounds [2]; }
            feature inherited subsets base { multiplicity bounds [4]; }
            feature reference references base;
            feature receiver { feature leaf[2]; }
            feature crossing crosses receiver.leaf;
        }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let unit = model.add_source(
        "enum.sysml",
        "enum def Choice { on; off; }
        enum root : Choice;
        part def D { enum choice : Choice; }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    for (name, count) in [("ranged", 3), ("named", 4), ("inherited", 4)] {
        let e = r.resolve_qualified(&format!("K::{name}")).unwrap();
        assert_eq!(
            r.effective_cardinality(e),
            Some((count, Some(count))),
            "{name}"
        );
    }
    for name in ["conflicting", "reference", "crossing"] {
        let e = r.resolve_qualified(&format!("K::{name}")).unwrap();
        assert_eq!(r.effective_cardinality(e), None, "{name}");
    }
    let root = r.resolve_qualified("root").unwrap();
    assert_eq!(r.effective_cardinality(root), Some((0, None)));
    let member = r.resolve_qualified("D::choice").unwrap();
    assert_eq!(r.effective_cardinality(member), Some((1, Some(1))));
}

#[test]
fn inherited_cardinality_uses_the_redefining_context() {
    let decls = "part def Rack { attribute count = 4; part slots[count]; }
        part rack : Rack[1] { attribute :>> count = 6; part :>> slots; }
        part zero[0]; part empty :>> zero;
        part low[2..3]; part high[4..5]; part conflict :>> low, high;
        part broad[2..8]; part narrowed[6] :>> broad;";
    assert_eq!(eval_with(decls, "size(rack.slots)"), Ok(int(6)));
    assert_eq!(eval_with(decls, "size(empty)"), Ok(int(0)));
    assert_eq!(eval_with(decls, "size(narrowed)"), Ok(int(6)));
    assert_eq!(eval_with(decls, "isEmpty(empty)"), Ok(Value::Boolean(true)));
    assert_eq!(eval_with(decls, "size(conflict)"), Ok(Value::Indeterminate));
}

#[test]
fn cardinality_keeps_unknown_receivers_and_shared_heritage_bounded() {
    let decls = "part def Rack { attribute count default = 4; part slots[count]; part fixed[4]; }
        requirement def R { subject unit : Rack[1]; }";
    assert_eq!(
        eval_with(decls, "size(R::unit.slots)"),
        Ok(Value::Indeterminate)
    );
    assert_eq!(eval_with(decls, "size(R::unit.fixed)"), Ok(int(4)));

    let mut diamond = String::from("part a0[4]; part b0[4];");
    for n in 1..24 {
        diamond.push_str(&format!(
            "part a{n} :>> a{}, b{}; part b{n} :>> a{}, b{};",
            n - 1,
            n - 1,
            n - 1,
            n - 1
        ));
    }
    assert_eq!(eval_with(&diamond, "size(a23)"), Ok(int(4)));
}

/// Lib-gated: verification verdict helpers evaluate — the library's
/// pass/fail calc reduces a boolean argument to the corresponding
/// verdict-kind enum member (not a scalar), through calc-body inlining
/// and enum identity.
#[test]
fn verdict_helpers_evaluate_to_enum_members() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "verdict.sysml",
        "package VP {
            private import ScalarValues::*;
            private import VerificationCases::*;
            attribute measured : Real = 12.5;
            attribute limit : Real = 20.0;
            attribute passing = PassIf(measured <= limit);
            attribute failing = PassIf(measured > limit);
        }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let name_of = |r: &mut ResolvedModel, q: &str| -> String {
        let e = r.resolve_qualified(q).expect("resolves");
        match r.evaluate(e) {
            Ok(Value::Element(t)) => r.element_qualified_name(t).unwrap_or_default(),
            other => panic!("expected an enum member, got {other:?}"),
        }
    };
    assert_eq!(
        name_of(&mut r, "VP::passing"),
        "VerificationCases::VerdictKind::pass"
    );
    assert_eq!(
        name_of(&mut r, "VP::failing"),
        "VerificationCases::VerdictKind::fail"
    );
}

/// Numbers are exact: decimal literals are rationals, arithmetic over
/// them never rounds, integers outgrow the machine range without
/// wrapping, and only transcendental results are approximate doubles.
#[test]
fn exact_rational_arithmetic() {
    assert_eq!(eval("0.1 + 0.2"), Ok(rat(3, 10)));
    assert_eq!(eval("0.1 + 0.2 == 0.3"), Ok(Value::Boolean(true)));
    assert_eq!(eval("0.1 * 3"), Ok(rat(3, 10)));
    assert_eq!(eval("100 * 1.1"), Ok(int(110)));
    assert_eq!(eval("1.1 * 1.1"), Ok(rat(121, 100)));
    assert_eq!(eval("0.1 + 0.7"), Ok(rat(4, 5)));
    assert_eq!(eval("1 / 3"), Ok(rat(1, 3)));
    assert_eq!(eval("1 / 3 * 3"), Ok(int(1)));
    assert_eq!(eval("7 / 2 * 2"), Ok(int(7)));
    assert_eq!(eval("2.0"), Ok(int(2)));
    assert_eq!(eval("2 ** -2"), Ok(rat(1, 4)));
    let text = |e: &str| eval(e).map(|v| v.to_string());
    assert_eq!(text("2.957353E-05"), Ok("0.00002957353".into()));
    assert_eq!(text("1 / 3"), Ok("1/3".into()));
    assert_eq!(text("0.1 + 0.2"), Ok("0.3".into()));
    assert_eq!(text("-0.5 * 3"), Ok("-1.5".into()));
    // Integer results beyond `i128` stay exact instead of wrapping.
    assert_eq!(
        text("2 ** 200"),
        Ok("1606938044258990275541962092341162602522202993782792835301376".into())
    );
    assert_eq!(eval("2 ** 200 / 2 ** 199"), Ok(int(2)));
    assert_eq!(
        text("170141183460469231731687303715884105727 + 1"),
        Ok("170141183460469231731687303715884105728".into())
    );
    assert_eq!(
        eval("170141183460469231731687303715884105727 + 1 - 1"),
        Ok(int(170141183460469231731687303715884105727))
    );
    // Exact roots and powers; inexact ones are doubles.
    assert_eq!(eval("sqrt(0.25)"), Ok(rat(1, 2)));
    assert_eq!(eval("8 ** (2/3)"), Ok(int(4)));
    assert_eq!(eval("sqrt(2)"), Ok(Value::Real(std::f64::consts::SQRT_2)));
    assert!(matches!(eval("sqrt(-1)"), Err(EvalError::Type(_))));
    // Comparison across exact and approximate numbers is exact.
    assert_eq!(eval("3 == 3.0"), Ok(Value::Boolean(true)));
    assert_eq!(eval("sqrt(0.25) == 0.5"), Ok(Value::Boolean(true)));
    assert_eq!(eval("0.1 < 1/3"), Ok(Value::Boolean(true)));
    assert_eq!(eval("sqrt(2) * sqrt(2) == 2"), Ok(Value::Boolean(false)));
    assert_eq!(eval("max((0.3, 0.1 + 0.2))"), Ok(rat(3, 10)));
    // Rational parts, rounding, and string conversion stay exact.
    assert_eq!(eval("numer(0.75)"), Ok(int(3)));
    assert_eq!(eval("denom(0.75)"), Ok(int(4)));
    assert_eq!(eval("rat(1, 3) + rat(2, 3)"), Ok(int(1)));
    assert_eq!(eval("floor(-0.5)"), Ok(int(-1)));
    assert_eq!(eval("round(2.5)"), Ok(int(3)));
    assert_eq!(eval("floor(sqrt(2))"), Ok(int(1)));
    assert_eq!(eval("7.5 % 2"), Ok(rat(3, 2)));
    assert_eq!(eval("ToReal(\"0.1\") + ToReal(\"0.2\")"), Ok(rat(3, 10)));
    assert_eq!(eval("ToString(0.1 + 0.2)"), Ok(Value::String("0.3".into())));
    assert_eq!(eval("ToString(1 / 3)"), Ok(Value::String("1/3".into())));
    // `ToString` output reads back exactly, in either spelling.
    assert_eq!(eval("ToReal(ToString(1 / 3))"), Ok(rat(1, 3)));
    assert_eq!(eval("ToReal(\"-500000/3183\")"), Ok(rat(-500000, 3183)));
    assert_eq!(eval("ToReal(\"2.5\") * 2"), Ok(int(5)));
    assert!(matches!(eval("ToReal(\"1/0\")"), Err(EvalError::Type(_))));
    // Rounding an infinite value is an error, not a saturated integer.
    assert!(matches!(
        eval("floor(1 / 0.0)"),
        Err(EvalError::DivisionByZero)
    ));
    assert!(matches!(eval("round(*)"), Err(EvalError::Type(_))));
}

/// A computed double exponent still names a root when it is the
/// nearest double of a small fraction, as a literal exponent does.
#[test]
fn approximate_unit_exponents_snap_to_small_fractions() {
    let units = "attribute m;";
    assert_eq!(
        eval_with(units, "(9 [m**2]) ** (sqrt(0.25))"),
        Ok(Value::Quantity(
            Box::new(int(3)),
            unit_probe_with(units, "m")
        ))
    );
    // The unit exponent snaps; the magnitude stays approximate because an
    // approximate operand took part.
    assert_eq!(
        eval_with(units, "(9 [m**2]) ** (cos(0) / 2)"),
        Ok(Value::Quantity(
            Box::new(Value::Real(3.0)),
            unit_probe_with(units, "m")
        ))
    );
    assert!(matches!(
        eval_with(units, "(9 [m**2]) ** (sqrt(2))"),
        Err(EvalError::Unsupported(_))
    ));
}

/// Unit scales are exact, so conversions never round: a millimetre
/// factor of `0.001` is one thousandth, not its nearest double.
#[test]
fn exact_unit_conversion() {
    let units = "attribute m;
                 attribute mm {
                     attribute unitConversion {
                         attribute referenceUnit = m;
                         attribute conversionFactor = 0.001;
                     }
                 }
                 attribute inch {
                     attribute unitConversion {
                         attribute referenceUnit = m;
                         attribute conversionFactor = 2.54E-02;
                     }
                 }";
    assert_eq!(
        eval_with(units, "1 [mm] + 1 [m]"),
        Ok(Value::Quantity(
            Box::new(int(1001)),
            unit_probe_with(units, "mm")
        ))
    );
    assert_eq!(
        eval_with(units, "(3 [mm]) [m]"),
        Ok(Value::Quantity(
            Box::new(rat(3, 1000)),
            unit_probe_with(units, "m")
        ))
    );
    assert_eq!(
        eval_with(units, "(0.3 [m]) [mm]"),
        Ok(Value::Quantity(
            Box::new(int(300)),
            unit_probe_with(units, "mm")
        ))
    );
    assert_eq!(
        eval_with(units, "0.1 [m] + 0.2 [m] == 0.3 [m]"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(units, "300 [mm] == 0.3 [m]"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(units, "(1 [inch]) [mm]"),
        Ok(Value::Quantity(
            Box::new(rat(127, 5)),
            unit_probe_with(units, "mm")
        ))
    );
    assert_eq!(
        eval_with(units, "(1 [m]) / (3 [mm])").map(|v| v.to_string()),
        Ok("1000/3".into())
    );
    assert_eq!(
        eval_with(units, "((1 [mm]) * (1 [mm])) [m ** 2]"),
        Ok(Value::Quantity(
            Box::new(rat(1, 1_000_000)),
            unit_probe_with(units, "m ** 2")
        ))
    );
}

/// Lib-gated: combined results are written in SI-coherent units. The
/// library's `kg` is the gram with the `kilo` prefix, so mass expands to
/// `g`; a product or quotient over it is written in `kg` with the
/// magnitude divided by 1000 per power of mass, exactly, and is the same
/// unit as the bracket that spells it; SI's named units (`N`, `Pa`, `J`,
/// `W`) are written by name. A user unit named `g` is not SI's.
#[test]
fn combined_results_are_written_in_kilograms() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "coherent.sysml",
        "package C {
            private import SI::*;
            attribute f = 2 [kg] * 3 [m/s**2];
            attribute p = 10 [N] / (2 [m**2]);
            attribute e = 10 [N] * 2 [m];
            attribute rho = 1000 [kg] / (1 [m**3]);
            attribute w = e / (4 [s]);
            attribute pressure = p == 5 [Pa];
            attribute force = f == 6 [N];
            attribute more = f + 1 [N];
            attribute grams = 0.5 [g] * 3 [m];
            attribute squared = 4 [g] * 2 [g];
            attribute per = 1 / (4 [kg]);
            attribute root = sqrt(4 [g]);
            attribute same = 6 [kg*m/s**2];
            package U {
                attribute g;
                attribute twice = 2 [g] * 3 [g];
            }
            package V {
                attribute kg; attribute m; attribute s;
                attribute f = 2 [kg] * 3 [m/s**2];
            }
            package W {
                private import USCustomaryUnits::*;
                attribute torque = 10 [N] * (2 [ft]);
                attribute weight = 2 [lb] * 32.174 [ft] / (1 [s]) ** 2;
                attribute accel = 10 [N] / (5 [kg]);
                attribute stress = 10 [N] / (2 ['in'] * (1 ['in']));
                attribute flux = 10 [N] * (2 ['m⋅s⁻¹']) / (3 ['in']);
            }
        }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let mut value = |q: &str| {
        let e = r.resolve_qualified(q).expect("resolves");
        r.evaluate(e)
    };
    let shown = |v: Result<Value, EvalError>| v.map(|v| v.to_string());
    // SI's named units are written by their names.
    assert_eq!(shown(value("C::f")), Ok("6 [N]".into()));
    assert_eq!(shown(value("C::p")), Ok("5 [Pa]".into()));
    assert_eq!(shown(value("C::e")), Ok("20 [J]".into()));
    assert_eq!(shown(value("C::w")), Ok("5 [W]".into()));
    assert_eq!(shown(value("C::rho")), Ok("1000 [kg/m**3]".into()));
    assert_eq!(value("C::pressure"), Ok(Value::Boolean(true)));
    assert_eq!(value("C::force"), Ok(Value::Boolean(true)));
    // The result is the bracket's unit, not one that converts to it, so
    // adding a bracket value keeps the number as it is.
    assert_eq!(value("C::f"), value("C::same"));
    assert_eq!(shown(value("C::more")), Ok("7 [N]".into()));
    // Grams convert exactly, every power of mass by its own factor.
    let Ok(Value::Quantity(n, u)) = value("C::grams") else {
        panic!("a quantity");
    };
    assert_eq!((*n, u.display()), (rat(3, 2000), "kg*m"));
    assert_eq!(shown(value("C::squared")), Ok("0.000008 [kg**2]".into()));
    assert_eq!(shown(value("C::per")), Ok("0.25 [1/kg]".into()));
    // No exact power of the factor: the root of a mass stays in grams.
    assert_eq!(shown(value("C::root")), Ok("2 [g**(1/2)]".into()));
    assert_eq!(shown(value("C::U::twice")), Ok("6 [g**2]".into()));
    assert_eq!(shown(value("C::V::f")), Ok("6 [kg*m/s**2]".into()));
    // Read in the units they were written in, values written in SI units
    // read as SI writes them, and other units re-express them.
    assert_eq!(shown(value("C::W::accel")), Ok("2 [m/s**2]".into()));
    let mut written = |q: &str| {
        let e = r.resolve_qualified(q).expect("resolves");
        let v = r.evaluate(e).unwrap();
        r.value_as_written(&v).map(|w| w.to_string())
    };
    assert_eq!(written("C::e"), None);
    assert_eq!(written("C::p"), None);
    assert_eq!(written("C::W::accel"), None);
    assert_eq!(written("C::W::torque"), Some("20 [N*ft]".into()));
    assert_eq!(written("C::W::stress"), Some("5 [N/in**2]".into()));
    assert_eq!(written("C::W::weight"), Some("64.348 [ft*lb/s**2]".into()));
    // A dimension nobody wrote a unit for reads as SI writes it: the
    // mass the newton brings is in kilograms.
    assert_eq!(
        written("C::W::flux"),
        Some("500000000/48387 [in*kg/s**3]".into())
    );
}

/// A conversion's reference unit can be a derived unit (`N = kg*m/s^2`)
/// or a product of units (`m^3`). Either evaluates to a product of units,
/// which no value represents, so the binding is read as a unit
/// expression: the converted unit takes the reference's dimensions. A
/// reference that cancels leaves the unit a named unit, not a number.
#[test]
fn conversions_to_derived_and_product_reference_units() {
    let units = "attribute s; attribute m; attribute g;
                 attribute kilo { attribute conversionFactor = 1000; }
                 attribute kg {
                     attribute unitConversion { attribute prefix = kilo; attribute referenceUnit = g; }
                 }
                 attribute N = kg*m/s^2;
                 attribute lbf {
                     attribute unitConversion { attribute referenceUnit = N; attribute conversionFactor = 4.4482216152605; }
                 }
                 attribute L {
                     attribute unitConversion { attribute referenceUnit = m^3; attribute conversionFactor = 0.001; }
                 }
                 attribute ratio {
                     attribute unitConversion { attribute referenceUnit = m/m; attribute conversionFactor = 2; }
                 }";
    assert_eq!(
        eval_with(units, "1 [lbf] == 4.4482216152605 [N]"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(units, "1 [N] + 1 [lbf]").map(|v| v.to_string()),
        Ok("5.4482216152605 [N]".into())
    );
    assert_eq!(
        eval_with(units, "1000 [L] == 1 [m^3]"),
        Ok(Value::Boolean(true))
    );
    assert!(matches!(
        eval_with(units, "1 [ratio] + 1"),
        Err(EvalError::Type(_))
    ));
}

/// Lib-gated: the standard library's conversions to derived reference
/// units (`lbf`, `kip` and `ozf` to `N`, `Btu_IT` to `J`, `hp` to `W`)
/// and to products of units (`gal` to `m^3`, `L` to `m³`) convert, so
/// they compare, add and combine with SI's units.
#[test]
fn standard_library_conversions_to_derived_reference_units() {
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "derived.sysml",
        "package D {
            private import SI::*;
            private import USCustomaryUnits::*;
            attribute force = 1 [lbf] == 4.448222 [N];
            attribute sum = 1 [N] + 1 [lbf];
            attribute kips = 1 [kip] == 1000 [lbf];
            attribute ounces = 1 [ozf] == 0.2780139 [N];
            attribute energy = 1 [Btu_IT] == 1055.056 [J];
            attribute power = 1 [hp] == 745.6999 [W];
            attribute volume = 1 [gal] == 3.785412 [L];
            attribute cubic = 1000 [L] == 1 [m^3];
            attribute moment = 1 ['ft⋅lbf'] == 1 [ft] * 1 [lbf];
            attribute rate = 1 [ft] * 1 [lbf] / (1 [s]);
        }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let mut value = |q: &str| {
        let e = r.resolve_qualified(q).expect("resolves");
        r.evaluate(e)
    };
    for name in [
        "force", "kips", "ounces", "energy", "power", "volume", "cubic", "moment",
    ] {
        assert_eq!(
            value(&format!("D::{name}")),
            Ok(Value::Boolean(true)),
            "{name}"
        );
    }
    let rate = value("D::rate").unwrap();
    assert_eq!(value("D::sum").unwrap().to_string(), "5.448222 [N]");
    assert_eq!(rate.to_string(), "1.3558180656 [W]");
    assert_eq!(
        r.value_as_written(&rate).map(|w| w.to_string()),
        Some("1 [lbf*ft/s]".into())
    );
}

/// The evaluation budget: a range, a string or a step count that would
/// run or allocate without bound fails cleanly instead of hanging the
/// evaluator or exhausting memory.
#[test]
fn evaluation_budget_bounds_ranges_strings_and_steps() {
    let range = eval("1..1000000000");
    assert!(
        matches!(&range, Err(EvalError::Budget(m)) if m.contains("range")),
        "{range:?}"
    );
    let wide = eval("-500000000..500000000");
    assert!(matches!(&wide, Err(EvalError::Budget(_))), "{wide:?}");
    assert_eq!(
        eval("(1..3)->collect { in x; x * 2 }"),
        Ok(Value::Sequence(vec![int(2), int(4), int(6)]))
    );
    let doubling = eval_with(
        "calc def dbl { in s; in n; if n <= 0 ? s else dbl(s + s, n - 1) }",
        "dbl(\"x\", 40)",
    );
    assert!(
        matches!(&doubling, Err(EvalError::Budget(m)) if m.contains("string")),
        "{doubling:?}"
    );
    // Step-heavy without allocating: every range an inner lambda built
    // would count against the allocation budget first.
    let steps = eval("(1..1000000)->collect { in x; x + x + x + x + x + x + x + x + x + x + x }");
    assert!(
        matches!(&steps, Err(EvalError::Budget(m)) if m.contains("steps")),
        "{steps:?}"
    );
}

/// Budgets that the step count alone cannot enforce: sequences and
/// strings that are each admissible but add up, range bounds spanning the
/// machine range, and exact integers that grow one multiplication at a time.
#[test]
fn evaluation_budget_bounds_cumulative_allocation_and_number_size() {
    use sysmlv2_parser::eval::MAX_ALLOCATION;
    // One full-size range is admissible; a collect that materializes one
    // per element is not, although it needs only a few million steps.
    assert!(1_000_000 * std::mem::size_of::<Value>() <= MAX_ALLOCATION);
    assert_eq!(eval("size(1..1000000)"), Ok(int(1_000_000)));
    let nested = eval("(1..1000000)->collect { in x; 1..1000000 }");
    assert!(
        matches!(&nested, Err(EvalError::Budget(m)) if m.contains("bytes")),
        "{nested:?}"
    );
    // Strings below the per-operation limit still add up.
    let strings = eval_with(
        "calc def dbl { in s; in n; if n <= 0 ? s else dbl(s + s, n - 1) }",
        "(1..40)->collect { in i; dbl(\"x\", 23) }",
    );
    assert!(
        matches!(&strings, Err(EvalError::Budget(m)) if m.contains("bytes")),
        "{strings:?}"
    );
    // Bounds spanning the machine range are refused, not overflowed.
    let extreme =
        eval("-170141183460469231731687303715884105727..170141183460469231731687303715884105727");
    assert!(
        matches!(&extreme, Err(EvalError::Budget(m)) if m.contains("range")),
        "{extreme:?}"
    );
    assert_eq!(eval("size(5..3)"), Ok(int(0)));
    // Exact integers stop growing at the bit limit: a fold such as
    // `product(1..1000000)` fails the same way, one multiplication past
    // the limit, but takes tens of thousands of large multiplications to
    // get there, so the check is exercised here through powers instead.
    assert_eq!(eval("product(1..20)"), Ok(int(2_432_902_008_176_640_000)));
    assert_eq!(eval("Length(ToString(2 ** 500000))"), Ok(int(150_515)));
    let product = eval("(2 ** 500000) * (2 ** 500000) * (2 ** 100000)");
    assert!(
        matches!(&product, Err(EvalError::Budget(m)) if m.contains("bits")),
        "{product:?}"
    );
    // A power past the limit degrades to an approximate infinity instead;
    // exact operands just under it still add past it.
    assert_eq!(eval("2 ** 1000000"), Ok(Value::Real(f64::INFINITY)));
    let sum = eval("(2 ** 524288) * (2 ** 524287) + (2 ** 524288) * (2 ** 524287)");
    assert!(
        matches!(&sum, Err(EvalError::Budget(m)) if m.contains("bits")),
        "{sum:?}"
    );
}

#[test]
fn fan_out_charges_cloned_payloads_before_repeating_them() {
    let payload = "x".repeat(1 << 20);
    let decls = format!(
        "attribute def Packet {{ attribute text; }}
         part def Record {{
             attribute text = \"{payload}\";
             attribute packet = new Packet(text);
         }}
         part many : Record[257];
         part few : Record[2];
         part def Numeric {{ attribute number = 2 ** 500000; }}
         part numbers : Numeric[5000];"
    );
    // Each string is small enough on its own. Cloning it directly or
    // inside a data instance must account for its heap storage, as must
    // cloning a large exact number. The count cap alone admits all three.
    for expr in ["many.text", "many.packet", "numbers.number"] {
        let result = eval_with(&decls, expr);
        assert!(
            matches!(&result, Err(EvalError::Budget(m)) if m.contains("bytes")),
            "{expr} must exhaust the allocation budget"
        );
    }
    for expr in ["few.text", "few.packet"] {
        let result = eval_with(&decls, expr).unwrap();
        assert!(matches!(result, Value::Sequence(items) if items.len() == 2));
    }
}

/// The allocation budget covers every operator that materializes a value,
/// not only arithmetic: an intrinsic that copies a sequence and a fold
/// that grows a string one item at a time each stay under the per-value
/// limits while adding up far past the cumulative one.
#[test]
fn evaluation_budget_covers_intrinsics_and_per_item_results() {
    // Each copy of a full-size range is admissible on its own.
    assert_eq!(eval("size(reverse(1..1000000))"), Ok(int(1_000_000)));
    let copies = eval("size(reverse(reverse(reverse(reverse(reverse(1..1000000))))))");
    assert!(
        matches!(&copies, Err(EvalError::Budget(m)) if m.contains("bytes")),
        "{copies:?}"
    );
    // A fold whose accumulator grows by a kilobyte per item: every
    // intermediate string is small, their total is not.
    let folded = eval_with(
        "calc def dbl { in s; in n; if n <= 0 ? s else dbl(s + s, n - 1) }",
        "(1..1000)->collect { in i; dbl(\"x\", 10) }->reduce '+'",
    );
    assert!(
        matches!(&folded, Err(EvalError::Budget(m)) if m.contains("bytes")),
        "{folded:?}"
    );
}

#[test]
fn intrinsic_names_do_not_override_user_calculations() {
    let decls = "
        calc def sum { in x; return r = 99; }
        calc def min { in x; in y; return r = 88; }
        calc def '+' { in x; in y; return r = 77; }
        alias renamed for sum;
        calc def Call { in sum; return r = sum(1); }
    ";
    for expr in [
        "sum(1)",
        "T::sum(1)",
        "1->sum()",
        "1->T::sum()",
        "renamed(1)",
        "Call(sum)",
    ] {
        assert_eq!(eval_with(decls, expr), Ok(int(99)), "{expr}");
    }
    for expr in ["(1, 2)->reduce min", "(1, 2)->reduce T::min"] {
        assert_eq!(eval_with(decls, expr), Ok(int(88)), "{expr}");
    }
    for expr in ["(1, 2)->reduce '+'", "(1, 2)->reduce T::'+'"] {
        assert_eq!(eval_with(decls, expr), Ok(int(77)), "{expr}");
    }
    assert!(matches!(
        eval("Missing::sum(1)"),
        Err(EvalError::Unsupported(_))
    ));
    assert!(matches!(
        eval("(1, 2)->Missing::reduce '+'"),
        Err(EvalError::Unsupported(_))
    ));
    assert!(matches!(
        eval_with("calc def reduce;", "(1, 2)->reduce '+'"),
        Err(EvalError::Unsupported(_))
    ));
    assert!(matches!(
        eval_with("calc def collect;", "(1, 2)->collect { in x; x }"),
        Err(EvalError::Unsupported(_))
    ));
}

#[test]
fn intrinsic_dispatch_follows_library_identity_and_aliases() {
    let mut model = Model::new();
    for (file, source) in [
        (
            "numeric.kerml",
            "standard library package NumericalFunctions { abstract function sum { in x; return r; } }",
        ),
        (
            "control.kerml",
            "standard library package ControlFunctions { abstract function reduce { in x; in fn; return r; } }",
        ),
        (
            "other.kerml",
            "standard library package Other { function sum { in x; return r = 42; } }",
        ),
    ] {
        let unit = model.add_library_source(file, source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    }
    let unit = model.add_source(
        "user.sysml",
        "package T {
        alias total for NumericalFunctions::sum;
        alias fold for ControlFunctions::reduce;
        calc def sum { in x; return r = 99; }
        calc def Call { in sum; return r = sum((1, 2, 3)); }
        attribute builtin = total((1, 2, 3));
        attribute qualified = NumericalFunctions::sum((1, 2, 3));
        attribute arrow = (1, 2, 3)->total();
        attribute indirect = Call(total);
        attribute folded = (1, 2)->fold '+';
        attribute own = sum(1);
        attribute libraryBody = Other::sum(1);
    }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    for (name, value) in [
        ("builtin", 6),
        ("qualified", 6),
        ("arrow", 6),
        ("indirect", 6),
        ("folded", 3),
        ("own", 99),
        ("libraryBody", 42),
    ] {
        let e = r.resolve_qualified(&format!("T::{name}")).unwrap();
        assert_eq!(r.evaluate(e), Ok(int(value)), "{name}");
    }
}

#[test]
fn standard_library_operator_aliases_reduce_by_identity() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source(
        "t.sysml",
        "package T {
        alias add for DataFunctions::'+';
        alias concatenate for StringFunctions::'+';
        alias fold for ControlFunctions::reduce;
        attribute numeric = (1, 2, 3)->fold add;
        attribute text = (\"a\", \"b\")->fold concatenate;
        attribute integer = (1, 2, 3)->fold IntegerFunctions::'+';
        attribute scalar = (1, 2, 3)->fold ScalarFunctions::'+';
    }",
    );
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    for name in ["numeric", "integer", "scalar"] {
        let e = r.resolve_qualified(&format!("T::{name}")).unwrap();
        assert_eq!(r.evaluate(e), Ok(int(6)), "{name}");
    }
    let text = r.resolve_qualified("T::text").unwrap();
    assert_eq!(r.evaluate(text), Ok(Value::String("ab".into())));
}

#[test]
fn ambiguous_intrinsic_spelling_is_not_a_missing_builtin() {
    let decls = "package A { calc def sum { in x; return r = 1; } }
        package B { calc def sum { in x; return r = 2; } }
        import A::*; import B::*;";
    assert!(matches!(
        eval_with(decls, "sum(3)"),
        Err(EvalError::Unsupported(_))
    ));
}

#[test]
fn inaccessible_intrinsic_spelling_is_not_a_missing_builtin() {
    let decls = "package A { private calc def sum { in x; return r = 1; } } import A::*;";
    assert!(matches!(
        eval_with(decls, "sum(3)"),
        Err(EvalError::Unsupported(_))
    ));
}

#[test]
fn unbound_collections_never_materialize_as_single_instances() {
    let decls = "
        part def Motor { attribute mass = 0.55; }
        part def Rack { part motors : Motor[4]; }
        part def Middle :> Rack { part :>> motors; }
        part rack : Middle[1] { part :>> motors; }
        part motors : Motor[4];
        part optional : Motor[0..1];
        part empty : Motor[0];
        part m1 : Motor[1]; part m2 : Motor[1]; part m3 : Motor[1]; part m4 : Motor[1];
        part concrete = (m1, m2, m3, m4);
        calc def Identity { in x; return result = x; }
    ";
    // A chain from an exact count of unknown instances takes the member
    // from one of them, once per instance: every motor has the declared
    // mass. Nothing materializes the motors themselves.
    for collection in ["motors", "rack.motors"] {
        assert_eq!(
            eval_with(decls, &format!("{collection}.mass")),
            Ok(Value::Sequence(vec![rat(11, 20); 4])),
            "{collection}"
        );
        assert_eq!(
            eval_with(decls, &format!("sum({collection}.mass)")),
            Ok(rat(11, 5)),
            "{collection}"
        );
    }
    // A calculation hands back the placeholder with no record of how it was
    // reached; a member declared outright in usages names its instances.
    for expr in [
        "sum(Identity(motors).mass)",
        "sum(Identity(rack.motors).mass)",
    ] {
        assert_eq!(eval_with(decls, expr), Ok(rat(11, 5)), "{expr}");
    }
    for expr in [
        "optional.mass",
        "sum(optional.mass)",
        "sum(Identity(optional).mass)",
    ] {
        assert_eq!(eval_with(decls, expr), Ok(Value::Indeterminate), "{expr}");
    }
    for collection in ["motors", "rack.motors", "optional"] {
        for expr in [
            format!("{collection}->collect {{ in m; m.mass }}"),
            format!("{collection}->reduce {{ in a; in b; a }}"),
            format!("{collection}->forAll {{ in m; m.mass == 0.55 }}"),
            format!("{collection}->exists {{ in m; true }}"),
            format!("size(({collection},))"),
            format!("size({collection} as Motor)"),
            format!("size(m1->collect {{ in m; {collection} }})"),
            format!("size(tail({collection}))"),
            format!("size(reverse({collection}))"),
            format!("size(union({collection}, m1))"),
            format!("head({collection}).mass"),
            format!("last({collection}).mass"),
            format!("max({collection})"),
            format!("min({collection})"),
            format!("product({collection})"),
        ] {
            assert_eq!(eval_with(decls, &expr), Ok(Value::Indeterminate), "{expr}");
        }
    }
    for (expr, expected) in [
        ("size(rack.motors)", int(4)),
        ("size(concrete)", int(4)),
        ("size((m1, m2))", int(2)),
        ("sum(concrete->collect { in m; m.mass })", rat(11, 5)),
        ("sum(concrete.mass)", rat(11, 5)),
        ("sum(empty.mass)", int(0)),
        ("product(empty.mass)", int(1)),
        ("size((empty, m1))", int(1)),
        ("empty->forAll { in m; false }", Value::Boolean(true)),
        ("empty->exists { in m; true }", Value::Boolean(false)),
        ("size(empty->collect { in m; m.mass })", int(0)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
}

#[test]
fn indexing_chained_collections_requires_known_flattened_positions() {
    let declarations = "
        part def A {
            attribute xs[4] ordered;
            attribute flag[1];
            attribute items[0..*] ordered = if flag ? xs else xs;
            attribute scalar[1];
        }
        part def B { attribute items[1] = 99; attribute scalar[1] = 99; }
        part a : A[1]; part b : B[1];
    ";
    for expression in ["(a, b).items#(2)", "(a, b).items#(3)", "(b, a).items#(2)"] {
        assert_eq!(
            eval_with(declarations, expression),
            Ok(Value::Indeterminate),
            "{expression}"
        );
    }
    // Exact singleton placeholders retain a position, even though their value
    // remains unknown. Direct unknown collections retain their upper bounds.
    assert!(matches!(
        eval_with(declarations, "(a, b).scalar#(1)"),
        Ok(Value::Unbound(..))
    ));
    assert_eq!(eval_with(declarations, "(a, b).scalar#(2)"), Ok(int(99)));
    assert_eq!(
        eval_with(declarations, "a.xs#(2)"),
        Ok(Value::Indeterminate)
    );
    assert!(matches!(
        eval_with(declarations, "a.xs#(5)"),
        Err(EvalError::Type(_))
    ));
}

#[test]
fn qualified_collection_receivers_fan_out_or_stay_indeterminate() {
    use sysmlv2_parser::ast::{Name, QualifiedName};
    let mut model = Model::new();
    let unit = model.add_source(
        "t.sysml",
        "package P {
        part def Motor { attribute mass = 0.55; }
        part motors : Motor[4];
        part wrapped : Motor = (motors,);
    }",
    );
    assert!(unit.diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    let member = QualifiedName {
        is_global: false,
        segments: vec![Name {
            value: "mass".into(),
            span: Default::default(),
        }],
        span: Default::default(),
    };
    // The chain reads every motor; the qualified name, one motor.
    let root = r.resolve_qualified("P::motors").unwrap();
    assert_eq!(
        r.evaluate_chain(root, &[&member]),
        Ok(Value::Sequence(vec![rat(11, 20); 4]))
    );
    assert_eq!(r.evaluate_qualified("P::motors::mass"), Ok(rat(11, 20)));
    // A tuple of four unknown motors has no positions to put them at.
    let root = r.resolve_qualified("P::wrapped").unwrap();
    assert_eq!(r.evaluate_chain(root, &[&member]), Ok(Value::Indeterminate));
    assert_eq!(
        r.evaluate_qualified("P::wrapped::mass"),
        Ok(Value::Indeterminate)
    );
}

/// A qualified name's prefix with no value stands for one instance of it,
/// whatever its multiplicity, at every depth: a part a package owns is a
/// collection of any size, yet `P::car::mass` is the mass of each car.
/// The chain `car.mass` reads every car, so it stays indeterminate.
#[test]
fn qualified_names_evaluate_for_one_instance_of_their_prefix() {
    let mut model = Model::new();
    let unit = model.add_source(
        "t.sysml",
        "package P {
            part def Wheel { attribute mass = 20; }
            part def Car {
                attribute base = 1000;
                part wheels : Wheel[4];
                attribute mass = base + sum(wheels.mass);
            }
            part car : Car { attribute :>> base = 1200; part :>> wheels { attribute :>> mass = 25; } }
            part fleet : Car[2..*];
            part tuned : Car[1] { attribute :>> wheels.mass = 30; }
            part none : Car[0];
            attribute chained = car.mass;
        }",
    );
    assert!(unit.diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    for (name, expected) in [
        ("P::car::base", int(1200)),
        ("P::car::mass", int(1300)),
        ("P::car::wheels::mass", int(25)),
        ("P::fleet::mass", int(1080)),
        ("P::fleet::wheels::mass", int(20)),
        ("P::Car::wheels::mass", int(20)),
        // A feature of no instance has no value to read.
        ("P::none::mass", Value::Sequence(Vec::new())),
    ] {
        assert_eq!(r.evaluate_qualified(name), Ok(expected), "{name}");
    }
    // `tuned` redefines the wheels' mass as a chain, which their declaration
    // in `Car` does not see: no wheel is taken for its instances.
    assert_eq!(
        r.evaluate_qualified("P::tuned::wheels::mass"),
        Ok(Value::Indeterminate)
    );
    assert_eq!(r.evaluate_qualified("P::chained"), Ok(Value::Indeterminate));
}

/// A constraint or feature declared in an instance reads for that instance
/// even with no chain to it, and so does a calculation the definition
/// declares when the instance runs it: a rollup in it fans out over the
/// instance's motors.
#[test]
fn evaluation_started_in_an_instance_reads_for_it() {
    let mut model = Model::new();
    let unit = model.add_source(
        "t.sysml",
        "package P {
            part def Motor { attribute mass; }
            part def Quad {
                attribute each default 0.5;
                part motors : Motor[4] { attribute :>> mass = each; }
                calc tot { return r = sum(motors.mass); }
                attribute total = tot();
            }
            part drone : Quad[1] {
                attribute :>> each = 0.6;
                attribute direct = total;
                attribute called = tot();
            }
        }",
    );
    assert!(unit.diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    for name in ["P::drone::direct", "P::drone::called"] {
        let e = r.resolve_qualified(name).unwrap();
        assert_eq!(r.evaluate(e), Ok(rat(12, 5)), "{name}");
        assert_eq!(r.evaluate_qualified(name), Ok(rat(12, 5)), "{name}");
    }
    // Read for the definition itself, its declarations are what it reads.
    let total = r.resolve_qualified("P::Quad::total").unwrap();
    assert_eq!(r.evaluate(total), Ok(int(2)));
}

/// A chain step over a feature that stands for an exact number of unknown
/// instances takes the rest of the chain from one of them and repeats a
/// data result once per instance, through nested counts. A result with an
/// identity (an element, an unknown) stays indeterminate, as does a
/// receiver of open count.
#[test]
fn chains_over_an_exact_count_of_unknown_instances_fan_out() {
    let decls = "
        part def Tire { attribute pressure = 30; }
        part def Wheel { part tire : Tire; attribute rim = 17; port valve; }
        part def Spoke { attribute length = 2; }
        part def Hub { part spokes : Spoke[3]; }
        part def Gauge { attribute reading; attribute fallback default 7; }
        enum def Mode { on; off; }
        part def Switch { attribute mode : Mode = Mode::on; }
        part def Pair { attribute xs = (1, 2); }
        part def Car {
            part wheels : Wheel[4];
            attribute totalPressure = sum(wheels.tire.pressure);
        }
        part def Rig { ref part one : Gauge[1]; ref part two : Gauge[2]; }
        part wheels : Wheel[4];
        part hubs : Hub[2];
        part gauges : Gauge[3];
        part rig : Rig[1];
        part some : Wheel[2..4];
        part switches : Switch[2];
        part pairs : Pair[600000];
        part car : Car[1] { part :>> wheels { part :>> tire { attribute :>> pressure = 32; } } }
    ";
    for (expr, expected) in [
        ("wheels.rim", Value::Sequence(vec![int(17); 4])),
        ("sum(wheels.tire.pressure)", int(120)),
        ("size(hubs.spokes.length)", int(6)),
        ("sum(hubs.spokes.length)", int(12)),
        ("size(switches.mode)", int(2)),
        ("gauges.fallback", Value::Sequence(vec![int(7); 3])),
        ("car.totalPressure", int(128)),
        ("sum(car.wheels.tire.pressure)", int(128)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
    for expr in [
        "wheels.tire",
        "size(wheels.tire)",
        "wheels.valve",
        "gauges.reading",
        // A reference's default is no value of what it refers to, one
        // instance or several.
        "rig.one.fallback",
        "rig.two.fallback",
        "some.rim",
        "sum(some.rim)",
    ] {
        assert_eq!(eval_with(decls, expr), Ok(Value::Indeterminate), "{expr}");
    }
    // Too many repeated values: indeterminate, as without the fan-out.
    assert_eq!(eval_with(decls, "pairs.xs"), Ok(Value::Indeterminate));
}

/// The one instance a fan-out evaluates is read for the instance the chain
/// went through, so a redefinition there by name (`each`, and `n`, which
/// counts the motors) is what every motor reads. A feature that names some
/// of the motors' values (`m1 :> motors`) leaves the chain indeterminate, as
/// does an evaluation of the one instance that recurses into itself.
#[test]
fn a_fan_out_reads_only_where_the_instances_read() {
    let decls = "
        part def Motor { attribute mass default 0.5; }
        part def Quad {
            attribute each default 0.5;
            attribute n default 4;
            part motors : Motor[4] { attribute :>> mass = each; }
            part counted : Motor[n];
            attribute total = sum(motors.mass);
            attribute countedTotal = sum(counted.mass);
        }
        part plain : Quad[1];
        part heavier : Quad[1] { attribute :>> each = 0.6; }
        part hexa : Quad[1] { attribute :>> n = 6; }
        part named : Quad[1] { part m1 :> motors[1] { attribute :>> mass = 1.0; } }
        part redefinedNamed : Quad[1] {
            part :>> motors;
            part m1 :> motors[1] { attribute :>> mass = 1.0; }
        }
        part own : Quad[1] { attribute :>> each = 0.6; part :>> motors; }
        part def Node {
            attribute weight = 1;
            part subs : Node[2];
            attribute total = weight + sum(subs.total);
        }
        part tree : Node[1];
    ";
    for (expr, expected) in [
        ("plain.total", int(2)),
        ("own.total", rat(12, 5)),
        ("heavier.total", rat(12, 5)),
        ("plain.countedTotal", int(2)),
        ("hexa.countedTotal", int(3)),
        ("size(hexa.counted)", int(6)),
        ("size(tree.subs.weight)", int(2)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
    for expr in ["named.total", "redefinedNamed.total", "tree.total"] {
        assert_eq!(eval_with(decls, expr), Ok(Value::Indeterminate), "{expr}");
    }
}

/// A redefinition by name alone, under the feature's name or a short name,
/// is the instance's version as a spelled `:>>` is: a fan-out reads it,
/// through an intermediate definition, over another such redefinition, and
/// with a type of its own. Two of them on different paths disagree, so the
/// read is refused.
#[test]
fn a_fan_out_follows_implicit_redefinitions() {
    for overriding in [
        "attribute each = 0.6;",
        "attribute <each> heavier = 0.6;",
        "attribute each : ScalarValues::Real = 0.6;",
    ] {
        let decls = format!(
            "part def Motor {{ attribute mass; }}
             part def Quad {{
                 attribute each default 0.5;
                 part motors : Motor[4] {{ attribute :>> mass = each; }}
                 attribute total = sum(motors.mass);
             }}
             part def Heavy :> Quad {{ {overriding} }}
             part def Indirect :> Heavy;
             part def Again :> Heavy {{ attribute each = 0.7; }}
             part def Other :> Quad {{ attribute each = 0.7; }}
             part def Both :> Heavy, Other;
             part h : Indirect[1];
             part a : Again[1];
             part b : Both[1];
             part plain : Quad[1] {{ attribute unrelated = 9; }}"
        );
        assert_eq!(eval_with(&decls, "h.each"), Ok(rat(3, 5)));
        for expr in ["h.total", "sum(h.motors.mass)"] {
            assert_eq!(
                eval_with(&decls, expr),
                Ok(rat(12, 5)),
                "{overriding}: {expr}"
            );
        }
        assert_eq!(eval_with(&decls, "a.total"), Ok(rat(14, 5)), "{overriding}");
        assert_eq!(
            eval_with(&decls, "b.total"),
            Ok(Value::Indeterminate),
            "{overriding}"
        );
        assert_eq!(eval_with(&decls, "plain.total"), Ok(int(2)));
    }
}

/// A feature naming some of the instances says something of a member when
/// one of its own members redefines that member by name alone, as it does
/// with a spelled `:>>`: the fan-out is refused. One redefining an unrelated
/// member by name refuses too (develop's rule for a specializer with any
/// implicit redefinition), and a subsetting that says nothing still counts.
#[test]
fn a_specializer_redefining_by_name_alone_refuses_a_fan_out() {
    const DECLS: &str = "part def Motor { attribute mass; attribute pressure default 30; }
         part def Quad {
             attribute each default 0.5;
             part motors : Motor[4] { attribute :>> mass = each; }
             attribute total = sum(motors.mass);
         }
         part def Named :> Quad { part m1 :> motors[1] { attribute mass = 1; } }
         part def Short :> Quad { part m1 :> motors[1] { attribute <mass> weight = 1; } }
         part def Unrelated :> Quad { part m1 :> motors[1] { attribute pressure = 32; } }
         part def Deep :> Quad { part box { part m1 :> motors[1] { attribute mass = 1; } } }
         part def Counted :> Quad { part m1 :> motors[1]; }
         part n : Named[1];
         part s : Short[1];
         part u : Unrelated[1];
         part d : Deep[1];
         part c : Counted[1];
         part i : Quad[1] { part m1 :> motors[1] { attribute mass = 1; } }
         part k : Quad[1] { part box { part m1 :> motors[1] { attribute <mass> weight = 1; } } }";
    for expr in [
        "n.total",
        "sum(n.motors.mass)",
        "s.total",
        "u.total",
        "d.total",
        "i.total",
        "sum(i.motors.mass)",
        "k.total",
    ] {
        assert_eq!(eval_with(DECLS, expr), Ok(Value::Indeterminate), "{expr}");
    }
    assert_eq!(eval_with(DECLS, "c.total"), Ok(int(2)));
    assert_eq!(eval_with(DECLS, "n.m1.mass"), Ok(int(1)));
}

#[test]
fn a_fan_out_checks_library_specializers_in_every_load_mode() {
    use sysmlv2_parser::prepared::PreparedLibrary;
    for specializer in [
        "part heavy :> motors[1] { attribute :>> mass = 1; }",
        "ref part heavy ::> motors[1] { attribute :>> mass = 1; }",
        "part counted :> motors[1];",
    ] {
        let source = format!(
            "package L {{
                part def Motor {{ attribute mass default 0.5; }}
                part def Quad {{
                    part motors : Motor[4];
                    {specializer}
                    attribute total = sum(motors.mass);
                }}
            }}"
        );
        for mode in ["source", "library", "prepared", "restored"] {
            let mut model = Model::new();
            let unit = if mode == "source" {
                model.add_source("library.sysml", &source)
            } else {
                model.add_library_source("library.sysml", &source)
            };
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            if matches!(mode, "prepared" | "restored") {
                let mut prepared = model.prepare_library().unwrap();
                if mode == "restored" {
                    let bytes = prepared.to_bytes(42).unwrap();
                    prepared =
                        std::sync::Arc::new(PreparedLibrary::from_bytes(&bytes, 42).unwrap());
                }
                model = Model::new();
                prepared.install(&mut model).unwrap();
            }
            let unit = model.add_source(
                "user.sysml",
                "package T { part q : L::Quad[1]; attribute total = q.total; }",
            );
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            let mut r = ResolvedModel::build(&model);
            let total = r.resolve_qualified("T::total").unwrap();
            let expected = if specializer.contains("counted") {
                int(2)
            } else {
                Value::Indeterminate
            };
            assert_eq!(r.evaluate(total), Ok(expected), "{mode}: {specializer}");
        }
    }
}

/// The instance chain a fan-out reads through is checked whole: every
/// declaration around the one instance must read as the instance in the
/// same place does, on every specialization path (a redefinition by name is
/// read as the instance's), and no feature elsewhere may name some of these
/// instances' values. A reference, a binding the evaluation does not follow
/// and a feature naming some of the instances leave the chain
/// indeterminate. A definition's own reading is its declaration, whatever
/// its specializations redefine.
#[test]
fn a_fan_out_checks_the_whole_instance_chain() {
    let decls = "
        part def Rotor { attribute mass; }
        part def Motor { part rotor : Rotor[1]; attribute mass default 0.5; }
        part def Quad {
            attribute each default 0.5;
            part motors : Motor[4] { part :>> rotor { attribute :>> mass = each; } }
            attribute total = sum(motors.rotor.mass);
        }
        part def Heavy :> Quad { attribute :>> each = 0.6; }
        part def Plain :> Quad;
        part def Mix :> Heavy, Plain;
        part diamond : Quad, Heavy [1];
        part mixed : Mix[1];
        part nested : Quad[1] { attribute :>> each = 0.6; part :>> motors; }
        part plain : Plain[1];
        part ownRotors : Quad[1] {
            attribute :>> each = 0.6;
            part :>> motors { part :>> rotor { attribute :>> mass = each; } }
        }
        part def Rack { attribute k default 3; part sub : Motor[2] { attribute :>> mass = k; } }
        part def Holder { ref part rack : Rack[1]; attribute w = sum(rack.sub.mass); }
        part holder : Holder[1];
        part def Pod { part motors : Motor[4]; attribute total = sum(motors.mass); }
        part q : Pod[1];
        part m1 :> q.motors [1] { attribute :>> mass = 1.0; }
        part spare : Pod[1];
        part spare2 :> spare { part :>> motors { attribute :>> mass = 1.0; } }
        part loose : Pod[1];
        part def Calculated {
            attribute each default 0.5;
            part motors : Motor[4] { attribute :>> mass = each; }
            calc tot { return r = sum(motors.mass); }
            attribute total = tot();
        }
        part calculated : Calculated[1] { attribute :>> each = 0.6; }
        part own : Pod[1] { part :>> motors; }
        part other[1] { ref part favourite ::> own.motors[1] { attribute :>> mass = 1.0; } }
        attribute six = 0.6;
        part bound : Calculated[1] { bind each = six; }
        part own2 : Pod[1] { part :>> motors; }
        part other2[1] { ref part favourite ::> T::own2::motors[1] { attribute :>> mass = 1.0; } }
        part wired : Pod[1] { part :>> motors; }
        part def Thing;
        part thing : Thing[1];
        allocation wiring allocate thing to wired.motors;
        part heavyOnes : Motor[0..*] { attribute :>> mass = 1.0; }
        part shared : Pod[1];
        part heavyShared :> shared.motors, heavyOnes [1];
        part counted : Pod[1];
        part countedOne :> counted.motors [1];
    ";
    for (expr, expected) in [
        ("plain.total", int(2)),
        ("ownRotors.total", rat(12, 5)),
        ("loose.total", int(2)),
        // An allocation's end names the motors and says nothing about them,
        // and so does a feature that only counts one of them.
        ("wired.total", int(2)),
        ("counted.total", int(2)),
        ("Quad::total", int(2)),
        // Every path to `Quad` redefines `each` by name, or nothing.
        ("diamond.total", rat(12, 5)),
        ("mixed.total", rat(12, 5)),
        ("nested.total", rat(12, 5)),
        ("sum(nested.motors.rotor.mass)", rat(12, 5)),
        // A calculation the definition declares runs for the instance.
        ("calculated.total", rat(12, 5)),
        // A binding with both ends resolved is followed.
        ("bound.total", rat(12, 5)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
    for expr in [
        "holder.w",
        "q.total",
        "spare.total",
        // A reference anywhere naming one of the instance's own motors.
        "own.total",
        "own2.total",
        // A motor that is also one of the heavy ones.
        "shared.total",
    ] {
        assert_eq!(eval_with(decls, expr), Ok(Value::Indeterminate), "{expr}");
    }
}

/// A feature with no value that an instance inherits, or that a chain reaches
/// through an instance, is that instance's: its members read the instance's
/// redefinitions, at every depth, through an alias, a calculation and a
/// qualified path. A definition's own reading, and a qualified name, read the
/// declaration.
#[test]
fn placeholders_read_for_the_instance_they_were_reached_through() {
    let decls = "
        part def Motor { attribute mass; }
        part def Quad {
            attribute each default 0.5;
            part spare : Motor[1] { attribute :>> mass = each; }
            attribute s = spare;
            attribute spareMass = spare.mass;
            calc twice { return r = spare.mass * 2; }
            attribute doubled = twice();
        }
        part drone : Quad[1] {
            attribute :>> each = 0.6;
            attribute inner = spare.mass;
            attribute called = twice();
        }
        part def Heavy :> Quad { attribute :>> each = 0.7; attribute own = spare.mass; }
        part heavy : Heavy[1];
        part def Sys {
            part drone : Quad[1] { attribute :>> each = 0.65; }
            attribute inner = drone.spare.mass;
        }
        part def Sys2 :> Sys { part :>> drone { attribute :>> each = 0.66; } }
        part sys : Sys[1];
        part sys2 : Sys2[1];
    ";
    for (expr, expected) in [
        ("drone.spare.mass", rat(3, 5)),
        ("drone.spareMass", rat(3, 5)),
        ("drone.s.mass", rat(3, 5)),
        ("drone.inner", rat(3, 5)),
        ("drone.doubled", rat(6, 5)),
        ("drone.twice()", rat(6, 5)),
        ("drone.called", rat(6, 5)),
        ("heavy.own", rat(7, 10)),
        ("heavy.spare.mass", rat(7, 10)),
        ("sys.drone.spare.mass", rat(13, 20)),
        ("sys.inner", rat(13, 20)),
        ("sys2.drone.spare.mass", rat(33, 50)),
        ("sys2.inner", rat(33, 50)),
        ("sys2.drone.doubled", rat(33, 25)),
        ("Quad::spareMass", rat(1, 2)),
        ("Quad::doubled", int(1)),
        ("Quad::spare.mass", rat(1, 2)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
}

/// An instance reads a name its declaration resolves where the declaration
/// resolves it: a package-level feature beside the declaring definition
/// stays that one, whatever the instance's own package declares. A
/// qualified name's prefix supplies the instances, and `that` is the
/// instance standing for the featuring type.
#[test]
fn an_instance_reads_names_where_its_declaration_resolves_them() {
    let mut model = Model::new();
    let unit = model.add_source(
        "t.sysml",
        "package A {
            attribute g = 9.8;
            part def Motor { attribute mass; }
            part def Quad {
                attribute each default 0.5;
                part spare : Motor[1] {
                    attribute :>> mass = each;
                    attribute grav = g;
                    attribute owner = that;
                }
            }
        }
        package B {
            private import A::*;
            attribute g = 1;
            attribute each = 99;
            part drone : Quad[1] { attribute :>> each = 0.6; }
            attribute grav = drone.spare.grav;
            attribute owner = drone.spare.owner;
        }",
    );
    assert!(unit.diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    for (name, expected) in [
        ("B::drone::spare::mass", rat(3, 5)),
        ("B::drone::spare::grav", rat(49, 5)),
        ("A::Quad::spare::mass", rat(1, 2)),
    ] {
        assert_eq!(r.evaluate_qualified(name), Ok(expected), "{name}");
    }
    let grav = r.resolve_qualified("B::grav").unwrap();
    assert_eq!(r.evaluate(grav), Ok(rat(49, 5)));
    let drone = r.resolve_qualified("B::drone").unwrap();
    let owner = r.resolve_qualified("B::owner").unwrap();
    assert!(
        matches!(r.evaluate(owner), Ok(Value::Unbound(e, _)) if e == drone),
        "{:?}",
        r.evaluate(owner)
    );
}

/// A fan-out reads what a lookup by name finds, so what that misses keeps
/// the chain indeterminate rather than repeating a declaration's value: a
/// redefinition under another name, in the instance, in the part the chain
/// reads through or in its type; a subsetting feature; a qualified name
/// that reads a declaration the instance stands for. Nested instances read
/// for each other, and a count reads the instance's bounds.
#[test]
fn a_fan_out_refuses_what_a_lookup_by_name_misses() {
    let decls = "
        part def Motor { attribute mass default 0.5; }
        part def Quad {
            attribute each default 0.5;
            attribute n default 4;
            part motors : Motor[4] { attribute :>> mass = each; }
            part plainMotors : Motor[4];
            part counted : Motor[n];
            attribute total = sum(motors.mass);
            attribute plainTotal = sum(plainMotors.mass);
            calc own { return r = each; }
            part called : Motor[4] { attribute :>> mass = Quad::own(); }
            part spare : Motor[1] { attribute :>> mass = each; }
            part qualified : Motor[4] { attribute :>> mass = Quad::spare::mass; }
        }
        part drone : Quad[1] { attribute :>> each = 0.6; }
        part renamed : Quad[1] { attribute weight :>> each = 0.6; }
        part subset : Quad[1] { attribute e2 :> each = 0.6; }
        part renamedInside : Quad[1] { part :>> plainMotors { attribute weight :>> mass = 1.0; } }
        part def Heavy :> Motor { attribute weight :>> mass = 1.0; }
        part typed : Quad[1] { part :>> plainMotors : Heavy; }
        part def Sys {
            attribute k default 5;
            part drone : Quad[1] { attribute :>> each = 0.65; attribute :>> n = k; }
        }
        part def Sys2 :> Sys { part :>> drone { attribute :>> each = 0.7; } }
        part sys : Sys[1];
        part sys2 : Sys2[1];
        part def Other { attribute each default 9; }
        part both : Quad, Other [1] { attribute :>> Other::each = 7; }
        part nestedNamed : Quad[1] {
            attribute :>> each = 0.6;
            part inner[1] { part m1 :> motors[1] { attribute :>> mass = 1.0; } }
        }
        part def Vehicle {
            part wheels : Motor[4];
            part frontLeft :> wheels;
            attribute front = sum(frontLeft.mass);
        }
        part v7 : Vehicle[1] { part :>> wheels { attribute :>> mass = 1.1; } }
        part def Sub :> Quad { attribute each2 :> each; }
        part pinned : Sub[1] { attribute :>> each2 = 0.8; }
        part pinnedInside : Quad[1] { attribute e2 :> each; part inner[1] { attribute :>> e2 = 0.8; } }
        part def Car {
            part wheels : Motor[4];
            part frontAxle[1] { part leftWheel :> wheels { attribute :>> mass = 1.2; } }
        }
        part car : Car[1];
        part counted4 : Quad[1] { attribute :>> each = 0.6; part m1 :> motors[1]; }
    ";
    for (expr, expected) in [
        // `both` redefines `Other::each`, not `Quad::each`.
        ("both.spare.mass", rat(1, 2)),
        ("sys.drone.total", rat(13, 5)),
        ("sum(sys.drone.motors.mass)", rat(13, 5)),
        ("sys2.drone.total", rat(14, 5)),
        ("sys2.drone.plainTotal", int(2)),
        // A feature that only counts one of the motors changes no value.
        ("counted4.total", rat(12, 5)),
        // The count reads `k` in the enclosing instance.
        ("size(sys.drone.counted)", int(5)),
        ("sum(sys.drone.counted.mass)", rat(5, 2)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
    for expr in [
        "renamed.total",
        "subset.total",
        "renamedInside.plainTotal",
        "sum(renamedInside.plainMotors.mass)",
        "typed.plainTotal",
        "sum(drone.called.mass)",
        "sum(drone.qualified.mass)",
        "both.total",
        // A motor declared inside the instance, with a mass of its own.
        "nestedNamed.total",
        // The front wheels are among `v7`'s wheels, which their own
        // declaration does not read.
        "v7.front",
        "sum(v7.frontLeft.mass)",
        // `each2 :> each`, given a value below, gives single-valued `each`
        // that value.
        "pinned.total",
        "pinnedInside.total",
        // A wheel declared inside the car, with a mass of its own.
        "sum(car.wheels.mass)",
    ] {
        assert_eq!(eval_with(decls, expr), Ok(Value::Indeterminate), "{expr}");
    }
}

/// Reads for an instance take what an instance around it says: a chain
/// redefinition (`attribute :>> b.kb = 9;`) wherever the feature is read for
/// that path, a calculation's parameter bound to the instance's feature, and
/// a count from the instance's bounds. A feature that subsets one and says
/// nothing of its values changes none of them.
#[test]
fn instances_read_what_the_instances_around_them_say() {
    let decls = "
        part def C { attribute kc default 1; attribute v = kc * 10; }
        part def B { attribute kb default 2; attribute twice = kb * 2; part c : C[1] { attribute :>> kc = kb; } }
        part def A { attribute k default 3; part b : B[1] { attribute :>> kb = k; } }
        part chained : A[1] { attribute :>> b.kb = 9; }
        part redefinedToo : A[1] { attribute :>> b.kb = 9; part :>> b; }
        part threeLinks : A[1] { attribute :>> b.c.kc = 11; }
        part def Own { part a : A[1]; attribute :>> a.b.kb = 4; attribute sv = a.b.c.v; }
        part def Pair { part bs : B[2]; part b1 :> bs[1]; part b2 :> bs[1]; attribute t = sum(bs.c.v); }
        part pair : Pair[1] { attribute :>> b1.kb = 9; }
        part nested : A[1] { part :>> b { attribute :>> kb = k + 100; } attribute :>> k = 7; }
        calc def Twice { in x; return r = 2 * x; }
        part def Plate { attribute w = 3; attribute area = w * 4; calc dbl : Twice { in x = area; } attribute a2 = dbl(); }
        part plate : Plate[1] { attribute :>> w = 5; }
        part def Wheel { attribute mass = 10; }
        part def SubW :> Wheel { attribute rimMass :> mass; }
        part def Car { part wheels : Wheel[4]; attribute total = sum(wheels.mass); }
        part car : Car[1] { part :>> wheels : SubW[4]; }
        part def Rack { attribute n = 4; part items : Wheel[n]; attribute cnt = size(items); }
        part rack : Rack[1] { attribute :>> n = 6; }
        part def Tyre { attribute mass = 10; attribute pressure = 30; }
        part def Fleet {
            part wheels : Tyre[4];
            part axle[1] { part leftWheel :> wheels { attribute :>> pressure = 32; } }
        }
        part fleet : Fleet[1];
    ";
    for (expr, expected) in [
        ("chained.b.kb", int(9)),
        ("chained.b.c.v", int(90)),
        // Read beside the chain's end, in the same instance, three links
        // down, and in a definition's own reading.
        ("chained.b.twice", int(18)),
        ("redefinedToo.b.c.v", int(90)),
        ("threeLinks.b.c.v", int(110)),
        ("Own::sv", int(40)),
        ("nested.b.c.v", int(1070)),
        ("plate.a2", int(40)),
        ("car.total", int(40)),
        ("sum(car.wheels.mass)", int(40)),
        ("rack.cnt", int(6)),
        // A wheel declared inside the fleet changes its pressure, not its
        // mass.
        ("sum(fleet.wheels.mass)", int(40)),
        ("pair.b1.c.v", int(90)),
        ("pair.b2.c.v", int(20)),
        // `b1` and `b2`, declared in `Pair`, are the pair's two `bs`.
        ("sum(pair.bs.c.v)", int(110)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
    // The pressure it changes, and a rollup in the pair's definition over
    // `bs` when a chain in the pair pins one of them, stay unknown.
    for expr in ["sum(fleet.wheels.pressure)", "pair.t"] {
        assert_eq!(eval_with(decls, expr), Ok(Value::Indeterminate), "{expr}");
    }
}

/// A binding connector gives a feature with no value of its own the other
/// end's value, read for the instance the binding is read for: in the
/// instance, in its definition, through a chain end, from either side, from
/// an enclosing instance, and inside a fan-out. A default yields to a
/// settled value and holds against an unsettled one; a value of the feature's
/// own that is no default is kept; two unvalued ends stay unknown.
#[test]
fn bindings_give_a_feature_the_other_ends_value() {
    let decls = "
        part def Motor { attribute mass default 0.5; }
        part def Quad {
            attribute each default 0.5;
            part spare : Motor[1] { attribute :>> mass = each; }
            part motors : Motor[4] { attribute :>> mass = each; }
            attribute total = sum(motors.mass);
            calc tot { return r = sum(motors.mass); }
            attribute viaCalc = tot();
        }
        attribute six = 0.6;
        part bound : Quad[1] { bind each = six; }
        part def BoundDef :> Quad { bind each = six; }
        part bd : BoundDef[1];
        part reversed : Quad[1] { bind six = each; }
        part local : Quad[1] { attribute z = 0.7; bind each = z; }
        part def C { attribute kc default 1; attribute v = kc * 10; }
        part def B { attribute kb default 2; part c : C[1] { attribute :>> kc = kb; } }
        part def A { attribute k default 3; part b : B[1] { attribute :>> kb = k; } }
        part a8 : A[1] { attribute z = 12; bind k = z; }
        part def Two { attribute x; attribute y; bind x = y; }
        part two : Two[1];
        part def Twin { attribute x; attribute y = 5; bind x = y; }
        part twin : Twin[1];
        part valued : Quad[1] { attribute :>> each = 0.9; bind each = six; }
        part unsettled : Quad[1] { attribute w; bind each = w; }
        part def Sys { attribute s = 0.8; part q : Quad[1] { bind each = s; } attribute inner = q.total; }
        part sys : Sys[1];
        part sys2 : Sys[1] { attribute :>> s = 0.3; }
        part outerChain : Sys[1] { attribute z = 0.2; bind q.each = z; }
        action def Act { in x; }
        action act : Act[1] { action b[1] { in y = x; } bind x = b.y; }
        part def Base { attribute x default 1; attribute y = 5; bind x = y; }
        part inherits : Base[1] { attribute :>> y = 7; }
        part o1[1] { attribute x default 1; attribute y; attribute z = 5; bind x = y; bind x = z; }
        part o2[1] { attribute x default 1; attribute y; attribute z = 5; bind x = z; bind x = y; }
        part def Rack { attribute n default 4; part items : Motor[n]; }
        part rack : Rack[1] { attribute six = 6; bind n = six; }
    ";
    for (expr, expected) in [
        ("bound.spare.mass", rat(3, 5)),
        ("bound.total", rat(12, 5)),
        ("bound.viaCalc", rat(12, 5)),
        ("bound.each", rat(3, 5)),
        ("bd.spare.mass", rat(3, 5)),
        ("bd.total", rat(12, 5)),
        ("reversed.spare.mass", rat(3, 5)),
        ("local.total", rat(14, 5)),
        ("a8.k", int(12)),
        ("a8.b.c.v", int(120)),
        ("twin.x", int(5)),
        ("valued.spare.mass", rat(9, 10)),
        ("unsettled.spare.mass", rat(1, 2)),
        ("unsettled.total", int(2)),
        ("sys.q.total", rat(16, 5)),
        ("sys.inner", rat(16, 5)),
        ("sys2.q.spare.mass", rat(3, 10)),
        ("outerChain.q.total", rat(16, 5)),
        // An inherited binding reads the instance's version of its end.
        ("inherits.x", int(7)),
        // Whatever the order, the binding whose end settles gives the value;
        // a default does not settle a binding being followed.
        ("o1.x", int(5)),
        ("o1.y", int(5)),
        ("o2.x", int(5)),
        ("o2.y", int(5)),
        // A bound reads its feature through the binding too.
        ("rack.n", int(6)),
        ("size(rack.items)", int(6)),
        ("sum(rack.items.mass)", int(3)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
    // Two unvalued ends, and an equality that comes back round to the
    // feature read (`y = x`, `x = b.y`), settle nothing.
    for expr in ["two.x", "act.b.y"] {
        assert!(
            matches!(eval_with(decls, expr), Ok(Value::Unbound(..))),
            "{expr}: {:?}",
            eval_with(decls, expr)
        );
    }
}

/// A multiplicity bound reading a feature of an enclosing instance reads it
/// there, with that instance's redefinitions and through its formulas; two
/// redefinitions of one feature inherited on paths that agree on nothing, an
/// ambiguous lookup past such redefinitions, or a redefinition under another
/// name in a type the instance specializes leave the feature's reads
/// indeterminate, where agreeing paths and a single one read the redefinition.
#[test]
fn enclosing_bounds_are_read_there_and_disagreeing_redefinitions_refuse() {
    let decls = "
        part def Motor { attribute mass default 0.5; }
        part def Rack { attribute n = 4; part items : Motor[n]; attribute total = sum(items.mass); }
        part def Sys { attribute k = 5; part rack : Rack[1] { attribute :>> n = k; } }
        part sys : Sys[1];
        part sys2 : Sys[1] { attribute :>> k = 7; }
        part def Deep { attribute m = 3; attribute k = m * 2; part rack : Rack[1] { attribute :>> n = k; } }
        part deep : Deep[1] { attribute :>> m = 4; }
        part def Quad { attribute each default 0.5; part spare : Motor[1] { attribute :>> mass = each; } attribute spareMass = spare.mass; }
        part def H1 :> Quad { attribute :>> each = 0.6; }
        part def H2 :> Quad { attribute :>> each = 0.7; }
        part def R1 :> Quad { attribute w :>> each = 0.9; }
        part def H1b :> H1 { attribute :>> each = 0.65; }
        part both : H1, H2 [1];
        part mix : H1, R1 [1];
        part mix3 : R1 [1] { attribute :>> each = 0.4; }
        part agree : H1, H1b [1];
        part h1 : H1[1];
        part renamed : Quad[1] { attribute weight :>> each = 0.6; }
    ";
    for (expr, expected) in [
        ("size(sys.rack.items)", int(5)),
        ("sum(sys.rack.items.mass)", rat(5, 2)),
        ("sys.rack.total", rat(5, 2)),
        ("size(sys2.rack.items)", int(7)),
        ("sys2.rack.total", rat(7, 2)),
        ("size(deep.rack.items)", int(8)),
        ("agree.spare.mass", rat(13, 20)),
        ("h1.spare.mass", rat(3, 5)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
    for expr in [
        "both.spare.mass",
        "both.spareMass",
        "mix.spare.mass",
        "mix3.spare.mass",
        "renamed.spare.mass",
        "renamed.each",
    ] {
        assert_eq!(eval_with(decls, expr), Ok(Value::Indeterminate), "{expr}");
    }
}

/// A chain of bindings longer than the call depth is a runaway, refused with
/// a budget error rather than followed without bound.
#[test]
fn a_runaway_chain_of_bindings_exhausts_the_budget() {
    let mut decls = String::from("part p[1] {");
    for i in 0..120 {
        decls.push_str(&format!(" attribute x{i};"));
    }
    decls.push_str(" attribute x120 = 7;");
    for i in (0..120).rev() {
        decls.push_str(&format!(" bind x{i} = x{};", i + 1));
    }
    decls.push('}');
    assert!(matches!(
        eval_with(&decls, "p.x0"),
        Err(EvalError::Budget(_))
    ));
    // A chain within the budget is followed to its end.
    let mut decls = String::from("part p[1] {");
    for i in 0..20 {
        decls.push_str(&format!(" attribute x{i};"));
    }
    decls.push_str(" attribute x20 = 7;");
    for i in (0..20).rev() {
        decls.push_str(&format!(" bind x{i} = x{};", i + 1));
    }
    decls.push('}');
    assert_eq!(eval_with(&decls, "p.x0"), Ok(int(7)));
}

/// A component in which every feature is bound to every other is walked
/// once per read, not once per path through it: forty features finish
/// at once, unsettled with none valued and settled when one is. Cycles
/// with a value reach it from every feature, and a feature read twice in
/// one expression is settled both times.
#[test]
fn a_densely_bound_component_is_walked_once() {
    for valued in [false, true] {
        let mut decls = String::from("part p[1] {");
        for i in 0..40 {
            decls.push_str(&format!(" attribute x{i};"));
        }
        if valued {
            decls.push_str(" attribute x40 = 7;");
        } else {
            decls.push_str(" attribute x40;");
        }
        for i in 0..=40 {
            for j in i + 1..=40 {
                decls.push_str(&format!(" bind x{i} = x{j};"));
            }
        }
        decls.push('}');
        let value = eval_with(&decls, "p.x0");
        if valued {
            assert_eq!(value, Ok(int(7)));
        } else {
            assert!(matches!(value, Ok(Value::Unbound(..))), "{value:?}");
        }
    }
    const DECLS: &str = "part def Ring {
             attribute a; attribute b; attribute c; attribute d = 4;
             bind a = b; bind b = c; bind c = a; bind c = d;
         }
         part ring : Ring[1];
         part def Twice { attribute u; attribute v = 3; bind u = v; attribute w = u + u; }
         part tw : Twice[1];";
    assert_eq!(eval_with(DECLS, "ring.a"), Ok(int(4)));
    assert_eq!(eval_with(DECLS, "ring.b"), Ok(int(4)));
    assert_eq!(eval_with(DECLS, "tw.w"), Ok(int(6)));
}

/// A binding whose other end has a value nobody knows still fixes the
/// feature, so its default does not apply: `y` redefined under another name
/// in the instance has no reading that is the instance's. A binding to an
/// unvalued feature leaves the default its say, and one reaching a value
/// through another binding takes it.
#[test]
fn a_binding_to_an_unknown_value_keeps_the_default_out() {
    const DECLS: &str =
        "part def Base { attribute x default 1; attribute y default 5; bind x = y; }
         part p : Base[1] { attribute renamed :>> y = 7; }
         part def Pair { attribute x default 1; attribute y; attribute z; bind x = y; bind y = z; }
         part q : Pair[1];
         part r : Pair[1] { attribute :>> z = 9; }";
    assert_eq!(eval_with(DECLS, "p.x"), Ok(Value::Indeterminate));
    assert_eq!(eval_with(DECLS, "p.y"), Ok(Value::Indeterminate));
    assert_eq!(eval_with(DECLS, "p.renamed"), Ok(int(7)));
    assert_eq!(eval_with(DECLS, "q.x"), Ok(int(1)));
    assert_eq!(eval_with(DECLS, "r.x"), Ok(int(9)));
}

/// Bindings a library declares are followed when a model reads through
/// them, and a model's binding to a feature a library declares is followed
/// too.
#[test]
fn library_bindings_are_followed() {
    let mut model = Model::new();
    let unit = model.add_library_source(
        "domain.sysml",
        "package D { part def Base { attribute x default 1; attribute y = 5; bind x = y; } part def Plain { attribute x default 1; } }",
    );
    assert!(unit.diagnostics.is_empty());
    let unit = model.add_source(
        "user.sysml",
        "package U {
            part p : D::Base[1];
            part q : D::Plain[1] { attribute y = 5; bind x = y; }
            attribute px = p.x;
            attribute qx = q.x;
        }",
    );
    assert!(unit.diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    for name in ["U::px", "U::qx"] {
        let e = r.resolve_qualified(name).unwrap();
        assert_eq!(r.evaluate(e), Ok(int(5)), "{name}");
    }
}

/// The cardinality report of a placeholder reads its bounds in the instance
/// the placeholder is read for, as `size` does: never the declaration's
/// bounds the instance overrides. Its certified projection covers
/// declaration receivers, so for an instance it may answer incomplete
/// rather than certify.
#[test]
fn the_cardinality_report_never_certifies_bounds_an_instance_overrides() {
    let mut model = Model::new();
    let unit = model.add_source(
        "t.sysml",
        "package P {
            part def Motor;
            part def Rack { attribute n default 4; part items : Motor[n]; }
            part p : Rack[1] { attribute :>> n = 6; }
            attribute items = p.items;
            attribute count = size(p.items);
        }",
    );
    assert!(unit.diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    let count = r.resolve_qualified("P::count").unwrap();
    assert_eq!(r.evaluate(count), Ok(int(6)));
    let items = r.resolve_qualified("P::items").unwrap();
    let value = r.evaluate(items).unwrap();
    assert!(matches!(value, Value::Unbound(..)), "{value:?}");
    match r.collection_cardinality_report(&value).bounds {
        Ok(bounds) => assert_eq!(bounds.size(), Some(6)),
        Err(issue) => assert!(
            matches!(
                issue,
                sysmlv2_parser::json::CardinalityIssue::IncompleteProvider
                    | sysmlv2_parser::json::CardinalityIssue::UnsupportedBound
            ),
            "{issue:?}"
        ),
    }
}

/// Features that are one value each and subset a feature that is one
/// value all name that one value. Siblings that only name it count it once;
/// a chain reads its most specific member; siblings saying something of it
/// leave the population unknown; subsets of two different values count two.
#[test]
fn subsets_of_one_value_count_it_once() {
    const DECLS: &str = "part def Motor { attribute mass default 10; }
         part def Kit { part items : Motor[0..*]; part a :> items[1]; }
         part def Kit2 { part items : Motor[0..*]; part a :> items[1]; part b :> items[1]; }
         part sib : Kit[1] { part also :> a[1]; part again :> a[1]; }
         part sib3 : Kit[1] { part also :> a[1]; part again :> a[1]; part third :> a[1]; }
         part sibsay : Kit[1] { part also :> a[1] { attribute :>> mass = 20; } part again :> a[1]; }
         part chain : Kit[1] { part also :> a[1]; part deeper :> also[1] { attribute :>> mass = 4; } }
         part two : Kit2[1] { part also :> a[1]; part again :> b[1]; }";
    assert_eq!(eval_with(DECLS, "size(sib.items)"), Ok(int(1)));
    assert_eq!(eval_with(DECLS, "sum(sib.items.mass)"), Ok(int(10)));
    assert_eq!(eval_with(DECLS, "size(sib3.items)"), Ok(int(1)));
    assert_eq!(
        eval_with(DECLS, "sum(sibsay.items.mass)"),
        Ok(Value::Indeterminate)
    );
    assert_eq!(eval_with(DECLS, "size(chain.items)"), Ok(int(1)));
    assert_eq!(eval_with(DECLS, "sum(chain.items.mass)"), Ok(int(4)));
    assert_eq!(eval_with(DECLS, "size(two.items)"), Ok(int(2)));
    assert_eq!(eval_with(DECLS, "sum(two.items.mass)"), Ok(int(20)));
}

/// A general's member that the receiver hides with a same-named member of
/// its own, in the receiver or in a definition between, is gathered as the
/// receiver's member, never as well as it.
#[test]
fn a_population_reads_the_receivers_same_name_version() {
    const DECLS: &str = "part def Motor { attribute mass default 2; }
         part def Kit { part items : Motor[0..*]; part a :> items[1]; }
         part shadow : Kit[1] { part a[1] { attribute mass = 3; } }
         part def Kit3 :> Kit { part a[1] { attribute mass = 4; } }
         part mid : Kit3[1];
         part subsetting : Kit[1] { part a :> items[1] { attribute mass = 5; } }";
    assert_eq!(eval_with(DECLS, "shadow.a.mass"), Ok(int(3)));
    assert_eq!(eval_with(DECLS, "sum(shadow.items.mass)"), Ok(int(3)));
    assert_eq!(eval_with(DECLS, "size(shadow.items)"), Ok(int(1)));
    assert_eq!(eval_with(DECLS, "sum(mid.items.mass)"), Ok(int(4)));
    assert_eq!(eval_with(DECLS, "sum(subsetting.items.mass)"), Ok(int(5)));
    assert_eq!(eval_with(DECLS, "size(subsetting.items)"), Ok(int(1)));
}

/// Features that specialize a member populate it only when they can supply
/// every value it needs: one `[1]` part among four motors leaves the four
/// unknown, their count still the declared one, and their values readable
/// when the part adds nothing.
#[test]
fn a_partly_populated_collection_stays_unknown() {
    let decls = "
        part def Motor { attribute mass default 0.5; }
        part def Quad {
            attribute each default 0.5;
            part motors : Motor[4] { attribute :>> mass = each; }
        }
        part drone : Quad[1] { attribute :>> each = 0.6; part m1 :> motors[1]; }
        part heavy : Quad[1] { part m1 :> motors[1] { attribute :>> mass = 1.0; } }
        part kit[1] { part items : Motor[0..*]; part a :> items[1]; part b :> items[1]; }
        part def Kit { part items : Motor[0..*]; part a :> items[1] { attribute :>> mass = 1; } part b :> items[1] { attribute :>> mass = 2; } }
        part fromDef : Kit[1];
        part redefined : Kit[1] { part :>> a { attribute :>> mass = 10; } }
        part def Axle { part wheels : Motor[2]; attribute wm = sum(wheels.mass); }
        part def FrontAxle :> Axle { part left :> wheels; part right :> wheels; }
        part axle : FrontAxle[1];
        part six : Quad[1] { part sx :>> motors[6]; }
        part def Kit2 { part items : Motor[0..*]; part a :> items[1] { attribute :>> mass = 2; } }
        part renamed : Kit2[1] { part r :>> a { attribute :>> mass = 10; } }
        part chained : Kit2[1] { part also :> a[1]; }
    ";
    for (expr, expected) in [
        ("size(drone.motors)", int(4)),
        ("isEmpty(drone.motors)", Value::Boolean(false)),
        ("drone.motors.mass", Value::Sequence(vec![rat(3, 5); 4])),
        ("size(heavy.motors)", int(4)),
        ("size(kit.items)", int(2)),
        // Subsetting parts a general declares populate the member too.
        ("size(fromDef.items)", int(2)),
        ("sum(fromDef.items.mass)", int(3)),
        ("sum(redefined.items.mass)", int(12)),
        // A subsetting part with no multiplicity of its own populates
        // nothing; a redefinition is the member itself.
        ("sum(axle.wheels.mass)", int(1)),
        ("axle.wm", int(1)),
        ("sum(six.motors.mass)", int(3)),
        // A redefinition of a populating part, under another name, stands
        // for it; a part subsetting a `[1]` part as `[1]` is that part.
        ("size(renamed.items)", int(1)),
        ("sum(renamed.items.mass)", int(10)),
        ("size(chained.items)", int(1)),
        ("sum(chained.items.mass)", int(2)),
    ] {
        assert_eq!(eval_with(decls, expr), Ok(expected), "{expr}");
    }
    assert_eq!(
        eval_with(decls, "heavy.motors.mass"),
        Ok(Value::Indeterminate)
    );
}

/// A host's chain off a root it names reads for no instance around the
/// root, so a definition's feature does not fan out from there, while a
/// part declared outright does. A placeholder from outside the evaluation
/// never fans out. A declaration nested in a type the instance chain does
/// not stand for keeps the chain indeterminate.
#[test]
fn a_fan_out_from_outside_needs_instances_the_evaluation_established() {
    use sysmlv2_parser::ast::{Name, QualifiedName};
    let mut model = Model::new();
    let unit = model.add_source(
        "t.sysml",
        "package P {
            private import ScalarFunctions::*;
            part def Motor { attribute mass = 0.5; }
            part def Quad { part motors : Motor[4]; }
            part drone : Quad[1];
            part def Outer {
                attribute k default 3;
                part def Inner { part ms : Motor[2] { attribute :>> mass = k; } attribute t = sum(ms.mass); }
            }
            part inner : Outer::Inner[1];
        }",
    );
    assert!(unit.diagnostics.is_empty());
    let mut r = ResolvedModel::build(&model);
    let member = QualifiedName {
        is_global: false,
        segments: vec![Name {
            value: "mass".into(),
            span: Default::default(),
        }],
        span: Default::default(),
    };
    let definition = r.resolve_qualified("P::Quad::motors").unwrap();
    assert_eq!(
        r.evaluate_chain(definition, &[&member]),
        Ok(Value::Indeterminate)
    );
    let motors = r.resolve_qualified("P::drone::motors").unwrap();
    let held = r.evaluate(motors).unwrap();
    assert!(matches!(held, Value::Unbound(..)), "{held:?}");
    assert_eq!(
        r.evaluate_value_chain(held, &[&member]),
        Ok(Value::Indeterminate)
    );
    // `Inner`'s own reading is its declaration's; `inner`'s is not read for
    // an instance of `Outer`, which no instance around it stands for.
    let t = r.resolve_qualified("P::Outer::Inner::t").unwrap();
    assert_eq!(r.evaluate(t), Ok(int(6)));
    assert_eq!(
        r.evaluate_qualified("P::inner::t"),
        Ok(Value::Indeterminate)
    );
}
