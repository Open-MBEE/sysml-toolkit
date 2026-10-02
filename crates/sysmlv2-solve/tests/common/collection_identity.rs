// Shared semantic fixtures exercised by both propagation and native solving.
pub fn contradictions() -> Vec<String> {
    let mut sources = Vec::new();
    for (base, declaration) in [
        ("", "part def A { attribute x : Integer;"),
        ("", "part def A { attribute x : Integer[1];"),
        (
            "part def Base { attribute x : Integer[1]; } part def Middle :> Base { attribute :>> x; }",
            "part def A :> Middle { attribute :>> x;",
        ),
    ] {
        for target in ["x", "alternate", "P::A::x"] {
            for quantifier in ["forAll", "exists"] {
                sources.push(format!(
                    "package P {{ attribute def Integer; {base} {declaration}
                        alias alternate for x;
                        assert constraint c {{ x == 0 & {target}->{quantifier} {{ in x; x == 1 }} }}
                    }} }}"
                ));
            }
        }
    }
    for local in ["", "attribute :>> value;"] {
        for target in ["p", "alternate", "P::A::p"] {
            sources.push(format!(
                "package P {{ attribute def Integer;
                    part def Item {{ attribute value : Integer; }}
                    part def A {{ part p : Item[1] {{ {local} }} alias alternate for p;
                        assert constraint c {{ p.value == 0 & {target}->forAll {{ in p; p.value == 1 }} }}
                    }}
                }}"
            ));
        }
    }
    sources.push(
        "package P { attribute def Integer;
        part def Item { attribute value : Integer; }
        part def A { part p : Item[1] { attribute :>> value; }
            assert constraint c { P::A::p::value == 0 & p->forAll { in i; i.value == 1 } }
        }
    }"
        .into(),
    );
    for size in [1, 2] {
        for target in ["alternate", "P::A::p"] {
            sources.push(format!(
                "package P {{ attribute def Integer;
                    part def Item {{ attribute value : Integer; }}
                    part def A {{ part p : Item[{size}]; alias alternate for p;
                        assert constraint c {{ p->forAll {{ in i; i.value == 0 }} & {target}->exists {{ in i; i.value == 1 }} }}
                    }}
                }}"
            ));
        }
    }
    sources.push(
        "package P { attribute def Integer;
            part def Item { attribute x : Integer default = 1; }
            requirement def R {
                subject p : Item[1];
                assert constraint c { p.x == 0 & p->forAll { in i; i.x == 1 } }
            }
        }"
        .into(),
    );
    sources.push(
        "package P { attribute def Integer;
            part def Item { attribute x : Integer; }
            part p : Item[1]; part q : Item[1];
            assert constraint c { p.x == 0 & p->forAll { in x;
                q->forAll { in x; x.x == 1 } & x.x == 1
            } }
        }"
        .into(),
    );
    sources
}

pub fn distinct_receivers(size: usize) -> String {
    format!("package P {{ attribute def Integer;
        part def Item {{ attribute value : Integer; }}
        part def A {{ part p : Item[{size}]; part q : Item[{size}];
            assert constraint c {{ p->forAll {{ in i; i.value == 0 }} & q->forAll {{ in i; i.value == 1 }} }}
        }}
    }}")
}

pub fn contextual_formulas() -> Vec<String> {
    let mut sources = Vec::new();
    for parameter in ["x", "i"] {
        for quantifier in ["forAll", "exists"] {
            sources.push(format!(
                "package P {{ attribute def Integer;
                    part def Item {{ attribute x : Integer; attribute y : Integer = x; }}
                    part p : Item[1];
                    assert constraint c {{ p.x == 0 & p->{quantifier} {{ in {parameter}; {parameter}.y == 1 }} }}
                }}"
            ));
        }
    }
    sources.push(
        "package P { attribute def Integer;
            part def Item { attribute x : Integer; attribute y : Integer = x; }
            part p : Item[2];
            assert constraint c { p->forAll { in i; i.x == 0 } & p->forAll { in x; x.y == 1 } }
        }"
        .into(),
    );
    sources.push(
        "package P { attribute def Integer;
            part def Item { attribute x : Integer; }
            part p : Item[1];
            assert constraint c { p.x == 0 & p->forAll { in x;
                x->forAll { in y; y.x == 1 }
            } }
        }"
        .into(),
    );
    sources.push(
        "package P { attribute def Integer;
            attribute n : Integer = 1;
            part def Item { attribute y : Integer = n; }
            part p : Item[1];
            calc def Check { in n : Integer default = 1;
                return result = p->forAll { in i; i.y == n };
            }
            attribute argument[1] : Integer;
            assert constraint c { argument == 0 & Check(argument) }
        }"
        .into(),
    );
    sources
}

pub fn closed_member_formula(size: usize) -> String {
    format!(
        "package P {{ attribute def Integer;
        part def Item {{ attribute x : Integer = 1; attribute y : Integer = x + 1; }}
        part p : Item[{size}]; attribute choice[1] : Integer;
        assert constraint c {{ choice == 0 & p->forAll {{ in x; x.y == 2 & x.x == 1 }} }}
    }}"
    )
}

// The Boolean marks declarations whose multiplicity proves scalar arity.
pub fn scalar_admission() -> Vec<(String, bool)> {
    let mut cases = Vec::new();
    for (declarations, scope, scalar) in [
        ("attribute x : Integer;", "", false),
        ("attribute x[1] : Integer;", "", true),
        ("attribute x : Integer;", "part def D {", true),
        ("ref x : Integer;", "part def D {", false),
        (
            "attribute base[1] : Integer; attribute x :> base;",
            "",
            true,
        ),
        (
            "attribute base[2] : Integer; attribute x :> base;",
            "",
            false,
        ),
        (
            "attribute base[2] : Integer; attribute x[1] :> base;",
            "",
            true,
        ),
        ("attribute base : Integer; attribute x :> base;", "", false),
        ("attribute x : Integer :> absent;", "part def D {", false),
    ] {
        let close = if scope.is_empty() { "" } else { "}" };
        cases.push((
            format!(
                "package P {{ attribute def Integer; {scope}
            {declarations} assert constraint c {{ x == 0 & x == 1 }} {close} }}"
            ),
            scalar,
        ));
    }
    cases
}

pub fn body_scalar_admission() -> Vec<(sysmlv2_model::model::Model, bool)> {
    [
        ("feature x : Integer { multiplicity [1]; }", true),
        ("feature x : Integer { multiplicity [2]; }", false),
        (
            "multiplicity one[1]; feature x : Integer { multiplicity subsets one; }",
            true,
        ),
        (
            "multiplicity many[2]; feature x : Integer { multiplicity subsets many; }",
            false,
        ),
        (
            "multiplicity unknown subsets absent; feature x : Integer { multiplicity subsets unknown; }",
            false,
        ),
    ]
    .into_iter()
    .map(|(declaration, scalar)| {
        let mut model = sysmlv2_model::model::Model::new();
        let unit = model.add_source(
            "bounds.kerml",
            &format!("package P {{ datatype Integer; {declaration} }}"),
        );
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let unit = model.add_source(
            "constraint.sysml",
            "assert constraint c { P::x == 0 & P::x == 1 }",
        );
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        assert!(!model.has_errors());
        (model, scalar)
    })
    .collect()
}
