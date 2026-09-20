//! Expression evaluator: operator semantics, feature references,
//! Kernel Function Library intrinsics, lambdas, featuring contexts — plus
//! a corpus smoke gate (every feature value must evaluate or fail cleanly,
//! never panic).

use sysmlv2_parser::eval::{EvalError, Value};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;
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
        part installed : Child;
        requirement def R { subject unit : Parent; }
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
            requirement def R { subject unit : Parent; }
            part installed : Parent;
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
                subject unit : Parent;
                ref part aliasUnit : Parent = unit;
            }
            part installed : Parent;
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
             part car : Vehicle { attribute :>> baseMass = 1200; }
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
             part unnamed : D { part :>> c : N; }
             part named : D { part c :>> c : N; }
             part subset : D { part :> c : N; }
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
        matches!(r.evaluate(e), Ok(Value::Unbound(_))),
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
             part c1 : C { part :>> p : Base2; }
             attribute probe = c1.p.f;

             part def A1 { attribute g = 1; }
             part def A2 { attribute g = 2; }
             part q { part x : A1, A2; }
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
             part outer : Boxy {
                 part inner {
                     attribute me = that;
                 }
             }
             attribute probeMe = outer.inner.me istype Boxy;
             attribute probeChain = outer.inner.that istype Boxy;
             part shadow { attribute that = 42; attribute reads = that; }
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
    // Collection membership is also three-valued: a known match decides,
    // but a wholly unknown search value cannot fabricate absence.
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
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        eval_with(u, "excludes((1, u + 1), 1)"),
        Ok(Value::Boolean(false))
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
    // KFL names stay reserved: a user calc named `sum` does not shadow the
    // intrinsic.
    assert_eq!(
        eval_with("calc def sum { in x; 0 }", "sum((1, 2, 3))"),
        Ok(int(6))
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
    // Positional args bind the value-less fields in declaration order;
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
    // Errors stay clean: unknown field, too many args, unbound field.
    assert!(matches!(
        eval_with(defs, "new Date(moment = \"x\")"),
        Err(EvalError::Unresolved(_))
    ));
    assert!(matches!(
        eval_with(defs, "new Date(\"a\", \"b\")"),
        Err(EvalError::Type(_))
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
            action a1 : Step { attribute :>> cost = 5; }
            action a2 : Step { attribute :>> cost = 7; }
            action a3 : Step { attribute :>> cost = 10; }
            part p { perform a1; perform a2; }
            part rollup {
                attribute total : Real = RealFunctions::sum((p.performedActions as Step).cost);
            }
        }",
    );
    let mut r = ResolvedModel::build(&model);
    let e = r.resolve_qualified("T::rollup::total").expect("resolves");
    assert_eq!(r.evaluate(e), Ok(Value::Integer(12)));
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
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
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

/// Chain steps over a multi-valued source map the member access and the
/// result is unique per KFL `'.'` (its `source`/`target` are declared
/// nonunique; the `chain` result feature carries KerML's default) —
/// five engines with one specific impulse read as one value, while
/// distinct values stay a sequence.
#[test]
fn chain_over_sequence_maps_and_dedups() {
    let decls = "part def E { attribute v = 304; }
                 part def P { attribute m; }
                 part e1 : E; part e2 : E; part e3 : E;
                 part a : P { attribute :>> m = 1; }
                 part b : P { attribute :>> m = 2; }
                 part s { part es = (e1, e2, e3); part ps = (a, b); }";
    assert_eq!(eval_with(decls, "s.es.v"), Ok(int(304)));
    assert_eq!(
        eval_with(decls, "s.ps.m"),
        Ok(Value::Sequence(vec![int(1), int(2)]))
    );
    assert_eq!(eval_with(decls, "sum(s.ps.m)"), Ok(int(3)));
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
                part car : V { attribute :>> base = 10; }";
    assert_eq!(eval_with(deep, "car.total"), Ok(int(21)));
    let rollup = "part def M {
                      part subs : M [*] default null;
                      attribute mass;
                      attribute totalMass = mass + sum(subs.totalMass);
                  }
                  part leaf1 : M { attribute :>> mass = 1; }
                  part leaf2 : M { attribute :>> mass = 2; }
                  part root : M {
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
                 part e : Engine;
                 part w : Wheel;
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
    assert!(matches!(eval_with(decls, "Q::x"), Ok(Value::Unbound(_))));
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
            action c1 : Chore { attribute :>> effort = 4.0; }
            action c2 : Chore { attribute :>> effort = 9.0; }
            action c3 : Chore { attribute :>> effort = 100.0; }
            part worker {
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
/// bodies vacuously true). Sequence literals containing placeholders
/// keep their written arity, and enum literals stay closed one-element
/// values.
#[test]
fn unbound_cardinality_comes_from_declared_multiplicity() {
    let decls = "
        part def D;
        part rack {
            part slots[3] : D;
            part gear[1..*] : D;
            part loose[0..2] : D;
            part lone : D;
        }
        enum def Mode { ON; OFF; }
    ";
    // Exact declared multiplicity answers.
    assert_eq!(eval_with(decls, "size(rack.slots)"), Ok(int(3)));
    // The KerML default `[1..1]` answers for a bare feature.
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
    // Written arity survives placeholders inside sequence literals.
    assert_eq!(
        eval_with(decls, "size((rack.gear, rack.loose))"),
        Ok(int(2))
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
        Ok(Value::Unbound(_))
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
