//! Inherited bounds preserve lexical identity while honoring actual overrides.
#![cfg(feature = "json")]

use std::sync::Arc;
use sysmlv2_parser::{
    eval::Value, json::ResolvedModel, libcache::LibraryCache, model::Model,
    prepared::PreparedLibrary,
};

fn models(library: &str, user: &str) -> Vec<ResolvedModel> {
    let mut base = Model::new();
    let unit = base.add_library_source("bounds.sysml", library);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    assert!(!base.has_errors());
    base.record_library_cache();
    ResolvedModel::build(&base);
    let cache =
        LibraryCache::from_bytes(&base.take_recorded_library_cache().unwrap().to_bytes()).unwrap();
    let prepared = base.prepare_library().unwrap();
    let decoded =
        Arc::new(PreparedLibrary::from_bytes(&prepared.to_bytes(31).unwrap(), 31).unwrap());
    (0..4)
        .map(|mode| {
            let mut model = Model::new();
            match mode {
                2 => Arc::clone(&prepared).install(&mut model).unwrap(),
                3 => Arc::clone(&decoded).install(&mut model).unwrap(),
                _ => {
                    model.add_library_source("bounds.sysml", library);
                    if mode == 1 {
                        model.set_library_cache(cache.clone());
                    }
                }
            }
            let unit = model.add_source("user.sysml", user);
            assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
            assert!(!model.has_errors());
            ResolvedModel::build(&model)
        })
        .collect()
}

fn exact(r: &mut ResolvedModel, name: &str, count: i128) {
    let e = r
        .resolve_qualified(name)
        .unwrap_or_else(|| panic!("missing {name}"));
    assert_eq!(
        r.effective_cardinality(e),
        Some((count, Some(count))),
        "{name}"
    );
}

#[test]
fn subsetting_bounds_do_not_capture_unrelated_package_names() {
    for mut r in models(
        "package A { attribute n = 4; part base[n]; }",
        "package B { attribute n = 2; part subset :> A::base; }",
    ) {
        for _ in 0..2 {
            exact(&mut r, "B::subset", 4);
            exact(&mut r, "A::base", 4);
        }
    }
}

#[test]
fn inherited_bounds_do_not_capture_a_new_member_over_a_lexical_name() {
    for mut r in models(
        "package A { attribute n = 4; part def Base { part slots[n]; } }",
        "package B { part def Child :> A::Base {
            attribute n = 2; part :>> slots;
        } }",
    ) {
        for _ in 0..2 {
            exact(&mut r, "B::Child::slots", 4);
            exact(&mut r, "A::Base::slots", 4);
        }
    }
}

#[test]
fn inherited_bounds_follow_actual_member_redefinitions() {
    for mut r in models(
        "package A { part def Base { attribute n = 4; part slots[n]; } }",
        "package B {
            part def Child :> A::Base { attribute :>> n = 6; part :>> slots; }
            part instance : Child[1] { attribute :>> n = 7; part :>> slots; }
        }",
    ) {
        for _ in 0..2 {
            exact(&mut r, "B::instance::slots", 7);
            exact(&mut r, "B::Child::slots", 6);
            exact(&mut r, "A::Base::slots", 4);
        }
    }
}

#[test]
fn contextual_constant_formulas_resolve_but_unrelated_shadows_stay_unknown() {
    for mut r in models(
        "package A { part def Base { attribute n = 4; part slots[n]; } }",
        "package B {
            part def SameName :> A::Base { attribute n = 2; part :>> slots; }
            part def Formula :> A::Base { attribute :>> n = 2 + 3; part :>> slots; }
        }",
    ) {
        exact(&mut r, "B::Formula::slots", 5);
        let e = r.resolve_qualified("B::SameName::slots").unwrap();
        assert_eq!(r.effective_cardinality(e), None);
    }
}

#[test]
fn calculation_arguments_do_not_fall_back_to_parameter_defaults_in_bounds() {
    for mut r in models(
        "package A { attribute n = 4; part base[n]; }",
        "calc def Count { in n default = 4; part p[n]; return result = size(p); }
        attribute answer = Count(2);",
    ) {
        let answer = r.resolve_qualified("answer").unwrap();
        assert_eq!(r.evaluate(answer), Ok(Value::Indeterminate));
    }
}

#[test]
fn lambda_parameter_names_do_not_capture_external_bound_names() {
    for mut r in models(
        "package A { attribute n = 4; part base[n]; }",
        "attribute answer = (2, 3)->collect { in n; size(A::base) };",
    ) {
        let answer = r.resolve_qualified("answer").unwrap();
        assert_eq!(
            r.evaluate(answer),
            Ok(Value::Sequence(vec![Value::Integer(4), Value::Integer(4)]))
        );
    }
}
#[test]
fn parameter_bounds_follow_supported_positional_redefinitions() {
    for mut r in models(
        "package A {
            requirement def Base { subject original[2]; }
            calc def Calc { in original[3]; return result; }
        }",
        "package B {
            requirement def Child :> A::Base { subject renamed; }
            requirement def Explicit :> A::Base { subject renamed[1]; }
            calc def ChildCalc :> A::Calc { in renamed; return result; }
            calc def StructuralCalc :> A::Calc { in attribute renamed; return result; }
            requirement def Broken :> A::Base, absent { subject renamed; }
        }",
    ) {
        for materialize in [false, true] {
            for name in [
                "B::Child::renamed",
                "B::Explicit::renamed",
                "B::ChildCalc::renamed",
                "B::Broken::renamed",
            ] {
                if materialize {
                    let e = r
                        .resolve_qualified(name)
                        .unwrap_or_else(|| panic!("missing {name}"));
                    r.implied_relationships(e);
                }
            }
            exact(&mut r, "B::Child::renamed", 2);
            exact(&mut r, "B::Explicit::renamed", 1);
            exact(&mut r, "B::ChildCalc::renamed", 3);
            exact(&mut r, "B::StructuralCalc::renamed", 1);
            let broken = r.resolve_qualified("B::Broken::renamed").unwrap();
            assert_eq!(r.effective_cardinality(broken), None);
        }
    }
}

#[test]
fn bound_formulas_rebind_dependencies_by_identity_in_the_receiver() {
    for mut r in models(
        "package A { attribute external = 2;
            part def Base {
                attribute n default = 3;
                alias alternate for n;
                attribute subtotal = alternate + external;
                attribute total = subtotal * 2;
                part slots[total];
                attribute directCount = n + 1; part direct[directCount];
                attribute chosen = if n > 4 ? n else 4; part conditional[chosen];
            }
        }",
        "package B {
            part def Child :> A::Base { attribute :>> n = 6;
                attribute external = 100;
                part :>> slots; part :>> direct; part :>> conditional;
            }
            part def Renamed :> A::Base { attribute other :>> n = 8;
                part :>> slots; part :>> direct;
            }
            part def Formula :> A::Base { attribute :>> n = 2 + 3;
                part :>> slots; part :>> direct;
            }
            part def Redefined :> A::Base { attribute :>> n = 7;
                attribute :>> total = subtotal + 1; part :>> slots;
            }
        }",
    ) {
        for _ in 0..2 {
            for (name, count) in [
                ("B::Child::slots", 16),
                ("B::Child::direct", 7),
                ("B::Child::conditional", 6),
                ("B::Renamed::slots", 20),
                ("B::Renamed::direct", 9),
                ("B::Formula::slots", 14),
                ("B::Formula::direct", 6),
                ("B::Redefined::slots", 10),
                ("A::Base::slots", 10),
                ("A::Base::direct", 4),
                ("A::Base::conditional", 4),
            ] {
                exact(&mut r, name, count);
            }
        }
    }
}

#[test]
fn bound_formula_dependencies_reject_cycles_ambiguity_and_unsupported_navigation() {
    for mut r in models(
        "package A { part def Base {
            attribute n default = 3; attribute formula = n + 1;
            part slots[formula]; attribute directCount = n + 1; part direct[directCount];
        } }",
        "package B {
            part def Cycle :> A::Base { attribute :>> n = A::Base::formula;
                part :>> slots; part :>> direct;
            }
            part def Shadow :> A::Base { attribute n = 9; part :>> slots; }
            part def Left :> A::Base { attribute left :>> n = 5; }
            part def Right :> A::Base { attribute right :>> n = 5; }
            part def Ambiguous :> Left, Right { part :>> slots; }
            part def Missing :> A::Base, absent { part :>> slots; }
            part def Calls :> A::Base { attribute :>> n = size((1, 2)); part :>> slots; }
            part def Chain :> A::Base { part p { attribute x = 2; }
                attribute :>> n = p.x; part :>> slots;
            }
        }",
    ) {
        for _ in 0..2 {
            for name in [
                "B::Cycle::slots",
                "B::Cycle::direct",
                "B::Shadow::slots",
                "B::Ambiguous::slots",
                "B::Missing::slots",
                "B::Calls::slots",
                "B::Chain::slots",
            ] {
                let e = r
                    .resolve_qualified(name)
                    .unwrap_or_else(|| panic!("missing {name}"));
                assert_eq!(r.effective_cardinality(e), None, "{name}");
            }
            exact(&mut r, "A::Base::slots", 4);
        }
    }
}

#[test]
fn bound_formula_dependency_depth_is_bounded() {
    let mut library = String::from("package A { part def Base { attribute v0 = 1;");
    for i in 1..80 {
        library.push_str(&format!("attribute v{i} = v{} + 1;", i - 1));
    }
    library.push_str("part slots[v79]; } }");
    for mut r in models(&library, "part def Child :> A::Base { part :>> slots; }") {
        let e = r.resolve_qualified("Child::slots").unwrap();
        assert_eq!(r.effective_cardinality(e), None);
    }
}

#[test]
fn local_bound_calls_remain_supported_without_escaping_contextual_guards() {
    for mut r in models(
        "package A { part def Base {
            attribute n = size((1, 2, 3));
            attribute formula = n + 1;
            part slots[n]; part dependent[formula]; attribute directCount = n + 1; part direct[directCount];
        } }",
        "package B { part def Child :> A::Base { part :>> slots; part :>> dependent;
            attribute local = size((1, 2)); attribute :>> n = local + 1;
            part :>> direct;
        } }",
    ) {
        for _ in 0..2 {
            exact(&mut r, "A::Base::slots", 3);
            exact(&mut r, "A::Base::dependent", 4);
            exact(&mut r, "A::Base::direct", 4);
            for name in ["B::Child::slots", "B::Child::dependent", "B::Child::direct"] {
                let e = r.resolve_qualified(name).unwrap_or_else(|| panic!("missing {name}"));
                assert_eq!(r.effective_cardinality(e), None, "{name}");
            }
        }
    }
}

#[test]
fn composed_bounds_preserve_unknown_defaults_and_restore_the_evaluator_context() {
    for mut r in models(
        "package A { part def Base { attribute n default = 3;
            attribute formula = A::Base::n + 1; part slots[formula];
        } }",
        "package B { part def Child :> A::Base { attribute other :>> n default = 6;
            part :>> slots;
        }
        requirement def R { subject unknown : Child[1]; }
        attribute unknownCount = size(R::unknown.slots);
        attribute probe = if size(R::unknown.slots) == 7 and false ? 999
            else size(A::Base::slots) + size(Child::slots);
        }",
    ) {
        let unknown = r.resolve_qualified("B::unknownCount").unwrap();
        assert_eq!(r.evaluate(unknown), Ok(Value::Indeterminate));
        let e = r.resolve_qualified("B::probe").unwrap();
        assert_eq!(r.evaluate(e), Ok(Value::Integer(11)));
    }
}

#[test]
fn contextual_bound_formulas_require_exact_nonnegative_integer_results() {
    for mut r in models(
        "package A { part def Base {
            attribute n = 2;
            attribute negative = -n;
            attribute fractional = n / 2;
            attribute invalid = n / 0;
            attribute overflow = 170141183460469231731687303715884105727 + n;
            attribute exactLarge = 9223372036854775808 + n;
            attribute zero = n - n;
            attribute chosen = if n > 1 and false ? absent else +n;
            part neg[negative]; part fraction[fractional]; part bad[invalid];
            part huge[overflow]; part big[exactLarge]; part empty[zero]; part choice[chosen];
        } }",
        "package B { part def Child :> A::Base { attribute :>> n = 3;
            part :>> neg; part :>> fraction; part :>> bad; part :>> huge;
            part :>> big; part :>> empty; part :>> choice;
        } }",
    ) {
        for name in ["neg", "fraction", "bad", "huge"] {
            let e = r.resolve_qualified(&format!("B::Child::{name}")).unwrap();
            assert_eq!(r.effective_cardinality(e), None, "{name}");
        }
        exact(&mut r, "B::Child::big", 9223372036854775811);
        exact(&mut r, "B::Child::empty", 0);
        exact(&mut r, "B::Child::choice", 3);
    }
}

#[test]
fn formula_depth_budget_covers_combined_syntax_and_dependency_nesting() {
    let mut library = String::from("package A { part def Base { attribute v0 = 1;");
    for i in 1..12 {
        library.push_str(&format!(
            "attribute v{i} = v{}{};",
            i - 1,
            " + 0".repeat(12)
        ));
    }
    library.push_str("part small[v2]; part deep[v11]; } }");
    for mut r in models(
        &library,
        "part def Child :> A::Base { part :>> small; part :>> deep; }",
    ) {
        exact(&mut r, "Child::small", 1);
        let e = r.resolve_qualified("Child::deep").unwrap();
        assert_eq!(r.effective_cardinality(e), None);
    }
}

#[test]
fn package_formula_dependencies_keep_the_receiver_without_capturing_package_names() {
    for mut r in models(
        "package A { attribute lexical = 2;
            attribute bridge = Base::n + lexical;
            attribute bridgeCall = size((1, 2, 3));
            part def Base { attribute n default = 3;
                attribute formula = bridge * 2;
                attribute unsafeFormula = bridgeCall + n;
                part slots[formula]; part blocked[unsafeFormula];
            }
        }",
        "package B { part def Child :> A::Base {
            attribute other :>> n = 6; attribute lexical = 100;
            part :>> slots; part :>> blocked;
        } }",
    ) {
        exact(&mut r, "B::Child::slots", 16);
        exact(&mut r, "A::Base::slots", 10);
        for name in ["A::Base::blocked", "B::Child::blocked"] {
            let e = r.resolve_qualified(name).unwrap();
            assert_eq!(r.effective_cardinality(e), None, "{name}");
        }
    }
}

#[test]
fn annotated_provider_completeness_remains_conservative() {
    for mut r in models(
        "package A { metadata def Marker;
            part def Base { attribute n = 4; part slots[n]; }
        }",
        "#A::Marker part def Annotated :> A::Base { part :>> slots; }
        part def Child :> Annotated { part :>> slots; }",
    ) {
        for name in ["Annotated::slots", "Child::slots"] {
            let e = r.resolve_qualified(name).unwrap();
            assert_eq!(r.effective_cardinality(e), None, "{name}");
        }
        exact(&mut r, "A::Base::slots", 4);
    }
}
