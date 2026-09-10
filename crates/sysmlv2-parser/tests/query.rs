//! Ad-hoc query evaluation (`ResolvedModel::query` + `parse_expression`):
//! root-scope expression evaluation with the query-mode extensions —
//! closed-world element classification and the reflection intrinsics
//! `ownedMember` / `ownedFeature`. Model-file evaluation (`evaluate`) must
//! keep its open-world semantics untouched.

use sysmlv2_parser::eval::{EvalError, Value};
use sysmlv2_parser::json::ResolvedModel;
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::parse_expression;

const DEMO: &str = "package Demo {
    part def Wheel;
    part def SpareWheel :> Wheel;
    part def Engine;
    part def Vehicle {
        attribute mass = 1200;
        part frontLeft : Wheel;
        part frontRight : Wheel;
        part spare : SpareWheel;
        part engine : Engine;
    }
    part car : Vehicle;
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

fn query(src: &str, expr: &str) -> Result<Value, EvalError> {
    let mut r = resolved(src);
    let parsed = parse_expression(expr);
    assert!(
        parsed.diagnostics.is_empty(),
        "query must parse cleanly: {:?}",
        parsed.diagnostics[0]
    );
    let root = r.root_scope();
    r.query(root, &parsed.expr.expect("expression"))
}

/// Qualified names of the elements in a query result.
fn names(src: &str, expr: &str) -> Vec<String> {
    let mut r = resolved(src);
    let parsed = parse_expression(expr);
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let root = r.root_scope();
    let v = r
        .query(root, &parsed.expr.expect("expression"))
        .expect("query evaluates");
    v.items_for_test()
        .into_iter()
        .map(|item| match item {
            Value::Element(e) => r.element_qualified_name(e).expect("named element"),
            other => panic!("expected an element, got {other}"),
        })
        .collect()
}

// `Value` has no public items(); flatten here for assertions.
trait Items {
    fn items_for_test(self) -> Vec<Value>;
}
impl Items for Value {
    fn items_for_test(self) -> Vec<Value> {
        match self {
            Value::Sequence(items) => items,
            v => vec![v],
        }
    }
}

#[test]
fn expression_parse_entry_point() {
    assert!(parse_expression("1 + 2 * 3").expr.is_some());
    assert!(
        parse_expression("a.b->select { in x; x istype T }")
            .expr
            .is_some()
    );
    // Trailing input is an error, and errors suppress the expression.
    let p = parse_expression("1 + 2 }");
    assert!(p.expr.is_none());
    assert!(!p.diagnostics.is_empty());
    let p = parse_expression("part def");
    assert!(p.expr.is_none());
    assert!(!p.diagnostics.is_empty());
}

#[test]
fn plain_value_queries_evaluate_at_root() {
    assert_eq!(query(DEMO, "Demo::car.mass + 10"), Ok(Value::Integer(1210)));
    assert_eq!(query(DEMO, "2 ** 5"), Ok(Value::Integer(32)));
}

#[test]
fn owned_member_and_owned_feature_enumerate_in_declaration_order() {
    assert_eq!(
        names(DEMO, "ownedMember(Demo)"),
        [
            "Demo::Wheel",
            "Demo::SpareWheel",
            "Demo::Engine",
            "Demo::Vehicle",
            "Demo::car"
        ]
    );
    // ownedFeature keeps only Feature subtypes: the attribute and the
    // parts, in declaration order.
    assert_eq!(
        names(DEMO, "ownedFeature(Demo::Vehicle)"),
        [
            "Demo::Vehicle::mass",
            "Demo::Vehicle::frontLeft",
            "Demo::Vehicle::frontRight",
            "Demo::Vehicle::spare",
            "Demo::Vehicle::engine",
        ]
    );
    // A package owns no features.
    assert_eq!(names(DEMO, "ownedFeature(Demo)"), [] as [&str; 0]);
}

#[test]
fn find_parts_by_usage_type() {
    // The motivating query: closed-world istype makes select answer
    // `false` for the non-conforming members (engine, mass) instead of
    // failing undecided, and the specialization SpareWheel :> Wheel is
    // reached through the explicit closure.
    assert_eq!(
        names(
            DEMO,
            "ownedFeature(Demo::Vehicle)->select { in p; p istype Demo::Wheel }"
        ),
        [
            "Demo::Vehicle::frontLeft",
            "Demo::Vehicle::frontRight",
            "Demo::Vehicle::spare"
        ]
    );
    assert_eq!(
        names(
            DEMO,
            "ownedFeature(Demo::Vehicle)->select { in p; p istype Demo::SpareWheel }"
        ),
        ["Demo::Vehicle::spare"]
    );
    assert_eq!(
        query(
            DEMO,
            "size(ownedFeature(Demo::Vehicle)->select { in p; p istype Demo::Engine })"
        ),
        Ok(Value::Integer(1))
    );
}

#[test]
fn query_classification_is_closed_world_for_user_types() {
    assert_eq!(
        query(DEMO, "Demo::Vehicle::engine istype Demo::Wheel"),
        Ok(Value::Boolean(false))
    );
    assert_eq!(
        query(DEMO, "Demo::Vehicle::spare istype Demo::Wheel"),
        Ok(Value::Boolean(true))
    );
}

#[test]
fn model_file_classification_keeps_open_world_semantics() {
    // The same non-conforming istype *inside a model file* must stay
    // undecided — query mode never leaks into feature-value evaluation.
    // Undecided is a first-class indeterminate value, never `false`.
    let src = "package T {
        part def Wheel;
        part def Engine;
        part e : Engine;
        attribute result = e istype Wheel;
    }";
    let mut r = resolved(src);
    let e = r.resolve_qualified("T::result").expect("result resolves");
    assert_eq!(r.evaluate(e), Ok(Value::Indeterminate));
}

#[test]
fn reflection_intrinsics_are_query_mode_only() {
    // In a model file, `ownedFeature(...)` falls through to user-calc
    // resolution (and fails as unresolved/unsupported), so a user
    // calculation of that name can never be shadowed.
    let src = "package T {
        part def V { part a; }
        attribute result = ownedFeature(V);
    }";
    let mut r = resolved(src);
    let e = r.resolve_qualified("T::result").expect("result resolves");
    assert!(r.evaluate(e).is_err());

    // And a user calculation named `ownedFeature` still wins in a model
    // file (reserved KFL names don't include the reflection extensions).
    let src = "package T {
        calc def ownedFeature { in x; return r = x + 1; }
        attribute result = ownedFeature(41);
    }";
    let mut r = resolved(src);
    let e = r.resolve_qualified("T::result").expect("result resolves");
    assert_eq!(r.evaluate(e), Ok(Value::Integer(42)));
}

#[test]
fn element_qualified_names() {
    let mut r = resolved(DEMO);
    let e = r
        .resolve_qualified("Demo::Vehicle::frontLeft")
        .expect("resolves");
    assert_eq!(
        r.element_qualified_name(e).as_deref(),
        Some("Demo::Vehicle::frontLeft")
    );
    let root_pkg = r.resolve_qualified("Demo").expect("resolves");
    assert_eq!(r.element_qualified_name(root_pkg).as_deref(), Some("Demo"));
}

/// Classification follows semantic-metadata implied specializations: an
/// element annotated with a `SemanticMetadata` subtype conforms to the
/// metadata's `baseType` value — for annotated *definitions* as well as
/// usages — while a miss against an unrelated user type stays a definite
/// closed-world `false`. (`Metaobjects` is user-defined here, like the
/// resolution-side test: the `$::`-rooted lookup finds it without the
/// standard library.)
#[test]
fn istype_follows_semantic_metadata_annotation() {
    let src = "package Metaobjects { metadata def SemanticMetadata { attribute baseType; } }
        package M {
            metadata def U;
            action def Pulse;
            part def Other;
            metadata def Tagged :> Metaobjects::SemanticMetadata {
                :>> baseType = Pulse meta U;
            }
            #Tagged action def Blink;
            abstract action pulses : Pulse;
            metadata def TaggedU :> Metaobjects::SemanticMetadata {
                :>> baseType = pulses meta U;
            }
            #TaggedU action blip;
        }";
    // Annotated definition: Blink -> (semantic) Pulse.
    assert_eq!(
        query(src, "M::Blink istype M::Pulse"),
        Ok(Value::Boolean(true))
    );
    // Annotated usage: blip -> (semantic) pulses -> (typing) Pulse.
    assert_eq!(
        query(src, "M::blip istype M::Pulse"),
        Ok(Value::Boolean(true))
    );
    // A genuine miss against a user type stays closed-world false.
    assert_eq!(
        query(src, "M::Blink istype M::Other"),
        Ok(Value::Boolean(false))
    );
}

/// KerML 9.2 metadata reflection: `X.metadata` evaluates to the
/// element's annotations plus an instance of its reflective metaclass;
/// `meta` casts the metaobjects, `@@` tests them, and `@` answers the
/// annotation test with the reflection-metaclass fallback. Needs the
/// standard library (the reflection metaclasses live in `SysML`).
#[test]
fn metadata_reflection_operators() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_source(
        "t.sysml",
        "package P {
            private import ScalarValues::*;
            metadata def Safety { attribute level : Integer; }
            part def Prog {
                doc /* About Prog. */
                @Safety { level = 3; }
            }
            part def Other;
        }",
    );
    let mut r = ResolvedModel::build(&model);
    let root = r.root_scope();
    let mut q = |expr: &str| {
        let parsed = parse_expression(expr);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        r.query(root, &parsed.expr.expect("expression"))
    };

    // `.metadata` — the annotation, then the reflective instance.
    let metas = q("P::Prog.metadata").expect("evaluates").items_for_test();
    assert_eq!(metas.len(), 2);
    assert!(matches!(&metas[0], Value::Element(_)));
    assert!(matches!(&metas[1], Value::Instance { ty_name, .. } if ty_name == "PartDefinition"));

    // `meta` casts to the conforming metaobjects; fields chain.
    let cast = q("P::Prog.metadata meta SysML::PartDefinition")
        .expect("evaluates")
        .items_for_test();
    assert_eq!(cast.len(), 1);
    assert_eq!(
        q("(P::Prog.metadata meta SysML::PartDefinition).declaredName"),
        Ok(Value::String("Prog".into()))
    );
    assert_eq!(
        q("(P::Prog.metadata meta P::Safety).level"),
        Ok(Value::Integer(3))
    );
    // A plain element operand stands for its metadata access.
    assert_eq!(
        q("P::Other meta SysML::ActionDefinition"),
        Ok(Value::Sequence(Vec::new()))
    );

    // `@@` — every metaobject conforms.
    assert_eq!(
        q("P::Other.metadata @@ SysML::PartDefinition"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        q("P::Prog.metadata @@ SysML::PartDefinition"),
        Ok(Value::Boolean(false))
    );

    // `.metadata` on a lambda parameter (env shadows model names), and
    // reflective fields chain — the doc-harvest idiom.
    assert_eq!(
        q(
            "ownedMember(P::Prog)->select { in d; d @ SysML::MetadataUsage }\
           ->collect { in d; size(d.metadata) }"
        ),
        Ok(Value::Sequence(vec![Value::Integer(1)]))
    );

    // `@` — annotation test, with the reflection fallback.
    assert_eq!(q("P::Prog @ P::Safety"), Ok(Value::Boolean(true)));
    assert_eq!(q("P::Other @ P::Safety"), Ok(Value::Boolean(false)));
    assert_eq!(
        q("P::Prog @ SysML::PartDefinition"),
        Ok(Value::Boolean(true))
    );
    assert_eq!(
        q("P::Prog @ SysML::ActionDefinition"),
        Ok(Value::Boolean(false))
    );
    // Cross-package reflection is decidable: a SysML-metaclassed
    // candidate against a KerML metaclass answers through the connected
    // reflection hierarchies, never undecided.
    assert_eq!(q("P::Prog @ KerML::Element"), Ok(Value::Boolean(true)));
    assert_eq!(
        q("P::Prog @ KerML::Documentation"),
        Ok(Value::Boolean(false))
    );

    // The doc-harvest idiom: select owned documentation, read its body
    // through the reflective metaobject.
    assert_eq!(
        q(
            "ownedMember(P::Prog)->select { in d; d @ KerML::Documentation }\
           ->collect { in d; (d meta KerML::Documentation).body }"
        ),
        Ok(Value::Sequence(vec![Value::String("About Prog. ".into())]))
    );

    // Singleton sequences are scalars to binary operators (KerML values
    // are flat sequences) — a `collect` result concatenates directly.
    assert_eq!(
        q(
            "\"doc: \" + ownedMember(P::Prog)->select { in d; d @ KerML::Documentation }\
           ->collect { in d; (d meta KerML::Documentation).body }"
        ),
        Ok(Value::String("doc: About Prog. ".into()))
    );

    // Library datatypes construct: `KeyValuePair` fields are plain KerML
    // features, and chain steps read them back.
    assert_eq!(
        q("(new Collections::KeyValuePair(\"k\", 7)).val"),
        Ok(Value::Integer(7))
    );
    assert_eq!(
        q("(new Collections::KeyValuePair(\"k\", 7)).key"),
        Ok(Value::String("k".into()))
    );
}

/// Constructors bind INHERITED fields, not just declared ones: the
/// library's ordered collections declare no members of their own —
/// `elements` comes from `Collection` — so without the inheritance walk
/// they could not be constructed at all. Own fields keep their
/// positions; inherited ones follow.
#[test]
fn constructors_bind_inherited_fields() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    model.add_source("t.sysml", "package P { part def X; }");
    let mut r = ResolvedModel::build(&model);
    let root = r.root_scope();
    let mut q = |expr: &str| {
        let parsed = parse_expression(expr);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        r.query(root, &parsed.expr.expect("expression"))
    };

    // Inherited `elements` is the sole positional slot.
    assert_eq!(
        q("(new Collections::List((\"a\", \"b\"))).elements"),
        Ok(Value::Sequence(vec![
            Value::String("a".into()),
            Value::String("b".into())
        ]))
    );
    // Named binding reaches it too, on a type that inherits twice over.
    assert_eq!(
        q("(new Collections::Bag(elements = 7)).elements"),
        Ok(Value::Integer(7))
    );
    // A type that redeclares the inherited field keeps ONE slot for it
    // (the redeclaration shadows the inherited one, no duplicate).
    assert_eq!(
        q("size((new Collections::Map(new Collections::KeyValuePair(\"k\", 1))).elements)"),
        Ok(Value::Integer(1))
    );
    // Own fields still bind positionally, unchanged.
    assert_eq!(
        q("(new Collections::KeyValuePair(\"k\", 9)).val"),
        Ok(Value::Integer(9))
    );
}
