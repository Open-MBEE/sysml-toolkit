//! `validateNamespaceDistinguishibility` over inherited members: an owned
//! member reusing an inherited name without redefining it, and a type
//! inheriting one name from two places. Every rejection has a legal
//! neighbor, and the implied redefinitions the specification grants
//! (parameters, ends, objectives, metadata body usages) stay silent.
use sysmlv2_parser::{check, json::ResolvedModel, model::Model};

const RULE: &str = "[validateNamespaceDistinguishibility]";

fn findings(src: &str) -> Vec<String> {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("d.sysml", src);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    check::validate_semantics_with(&mut r, &model)
        .into_iter()
        .map(|(_, d)| d.message)
        .filter(|m| m.contains(RULE))
        .collect()
}

fn kerml_findings(src: &str) -> Vec<String> {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("d.kerml", src);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    check::validate_semantics_with(&mut r, &model)
        .into_iter()
        .map(|(_, d)| d.message)
        .filter(|m| m.contains(RULE))
        .collect()
}

#[test]
fn owned_usage_reusing_an_inherited_name_is_reported() {
    let out = findings(
        "package P {
            private import ScalarValues::*;
            attribute def SwitchStatus { attribute downlinkPort : Real; }
            attribute def M1SwitchStatus :> SwitchStatus { attribute downlinkPort : Real[6]; }
        }",
    );
    assert_eq!(out.len(), 1, "{out:?}");
    assert!(
        out[0]
            .starts_with("`downlinkPort` duplicates the inherited member name from `SwitchStatus`"),
        "{out:?}"
    );
}

#[test]
fn redefinition_and_subsetting_are_the_legal_spellings() {
    for spelling in [
        "attribute :>> downlinkPort : Real[6];",
        "attribute downlinkPort :>> downlinkPort : Real[6];",
        "attribute downlinkPort :> downlinkPort : Real[6];",
    ] {
        let out = findings(&format!(
            "package P {{
                private import ScalarValues::*;
                attribute def SwitchStatus {{ attribute downlinkPort : Real; }}
                attribute def M1SwitchStatus :> SwitchStatus {{ {spelling} }}
            }}"
        ));
        assert!(out.is_empty(), "{spelling}: {out:?}");
    }
}

#[test]
fn short_names_share_the_name_space() {
    let out = findings(
        "package P {
            private import ScalarValues::*;
            attribute def SwitchStatus { attribute downlinkPort : Real; }
            attribute def M1SwitchStatus :> SwitchStatus { attribute <downlinkPort> port6 : Real[6]; }
        }",
    );
    assert_eq!(out.len(), 1, "{out:?}");
    assert!(out[0].contains("`downlinkPort` duplicates"), "{out:?}");
}

#[test]
fn a_usage_typed_by_the_offending_definition_inherits_both() {
    let out = findings(
        "package P {
            private import ScalarValues::*;
            attribute def SwitchStatus { attribute downlinkPort : Real; }
            attribute def M1SwitchStatus :> SwitchStatus { attribute downlinkPort : Real[6]; }
            attribute def LanStatus { attribute m1 : M1SwitchStatus; }
        }",
    );
    assert_eq!(out.len(), 2, "{out:?}");
    assert!(
        out.iter().any(|m| m.starts_with(
            "`downlinkPort` is inherited from both `M1SwitchStatus` and `SwitchStatus`"
        )),
        "{out:?}"
    );
}

#[test]
fn distinct_metaclasses_are_distinguishable() {
    // An item usage and an attribute usage neither conform to the other
    // (KerML `Membership::isDistinguishableFrom`).
    let out = findings(
        "package P {
            private import ScalarValues::*;
            part def A { attribute x : Real; }
            part def B :> A { item x; }
        }",
    );
    assert!(out.is_empty(), "{out:?}");
}

#[test]
fn kerml_features_collide_too() {
    let out = kerml_findings(
        "package P {
            classifier A { feature x; }
            classifier B specializes A { feature x; }
            classifier C specializes A { feature redefines x; }
        }",
    );
    assert_eq!(out.len(), 1, "{out:?}");
    assert!(
        out[0].contains("`x` duplicates the inherited member name from `A`"),
        "{out:?}"
    );
}

#[test]
fn library_heritage_alone_is_silent() {
    let out = findings(
        "package P {
            private import ScalarValues::*;
            part def Vehicle { part engine : Engine; attribute mass : Real; }
            part def Engine;
            part def Car :> Vehicle { part :>> engine; attribute :>> mass = 1200.0; }
            part car : Car;
            action def Drive { in speed : Real; out done : Boolean; }
            action def DriveFast :> Drive { in speed : Real; out done : Boolean; }
            state def Running { entry action init; do action run; exit action stop; }
            calc def Area { in w : Real; in h : Real; return area : Real = w * h; }
            calc def SquareArea :> Area { in w : Real; in h : Real; return area : Real = w * w; }
        }",
    );
    assert!(out.is_empty(), "{out:?}");
}

#[test]
fn implied_redefinitions_are_not_collisions() {
    // Interface ends reuse `BinaryInterface`'s end names positionally, a
    // case objective redefines `Case::obj`, and a metadata body usage is
    // an owned redefinition by the grammar.
    let out = findings(
        "package P {
            private import ScalarValues::*;
            private import ModelingMetadata::*;
            port def StagingPort;
            interface def StagingInterface {
                end source : StagingPort;
                end target : ~StagingPort;
            }
            part def Stage { port p : StagingPort; port q : ~StagingPort; }
            part def Rocket {
                part a : Stage;
                part b : Stage;
                interface : StagingInterface connect a.p to b.q;
                @Rationale { text = \"staged for mass\"; }
            }
            requirement def Objective;
            analysis def Study {
                subject s : Rocket;
                objective obj : Objective;
            }
        }",
    );
    assert!(out.is_empty(), "{out:?}");
}

#[test]
fn sibling_redefinitions_along_a_chain_are_removed_level_by_level() {
    // `Thermal::'packet data field'` redefines `Packets::'packet data
    // field'`; each owns a `'secondary header'` redefining `'header'`. The
    // nearer one removes the farther one at its own level, so a third
    // level redefining the nearer field inherits exactly one.
    let out = findings(
        "package Packets {
            private import ScalarValues::*;
            attribute 'packet data field' {
                attribute 'header' : Real;
                attribute 'secondary header' redefines 'header';
            }
            part def Packet { attribute redefines 'packet data field'; }
            part def ThermalPacket :> Packet {
                attribute 'packet data field' redefines Packets::'packet data field' {
                    attribute 'secondary header' redefines 'header';
                }
            }
            part packet3 : ThermalPacket {
                attribute 'special data field' redefines 'packet data field' {
                    attribute 'more' : Real;
                }
            }
        }",
    );
    assert!(out.is_empty(), "{out:?}");
}

#[test]
fn library_only_diamonds_are_left_to_the_specialization_error() {
    // `individual def X :> anAttributeDef` inherits `self` from both
    // `DataValue` and `Occurrence`; the class-specialization error already
    // names the cause, and the pair is not echoed.
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source(
        "d.sysml",
        "package P { attribute def TipTilt; individual def Zero :> TipTilt; }",
    );
    let mut r = ResolvedModel::build(&model);
    let all: Vec<String> = check::validate_semantics_with(&mut r, &model)
        .into_iter()
        .map(|(_, d)| d.message)
        .collect();
    assert!(
        all.iter()
            .any(|m| m.contains("[validateClassSpecialization]")),
        "{all:?}"
    );
    assert!(!all.iter().any(|m| m.contains(RULE)), "{all:?}");
}

#[test]
fn two_unrelated_bases_supplying_one_name_collide_deterministically() {
    let src = "package P {
        private import ScalarValues::*;
        part def A { attribute x : Real; attribute y : Real; }
        part def B { attribute x : Real; attribute y : Real; }
        part def C :> A, B;
    }";
    let out = findings(src);
    assert_eq!(out.len(), 2, "{out:?}");
    assert!(
        out[0].starts_with("`x` is inherited from both `A` and `B`"),
        "{out:?}"
    );
    assert!(
        out[1].starts_with("`y` is inherited from both `A` and `B`"),
        "{out:?}"
    );
    assert_eq!(findings(src), out, "order must not depend on hashing");
}

#[test]
fn a_chain_names_the_nearest_declaring_type() {
    let out = findings(
        "package P {
            private import ScalarValues::*;
            part def A { attribute x : Real; }
            part def B :> A { attribute x : Real; }
            part def C :> B { attribute x : Real; }
            part c : C;
        }",
    );
    assert_eq!(out.len(), 3, "{out:?}");
    assert!(out.contains(&"`x` duplicates the inherited member name from `A` — redefine it (`:>>`) or rename it [validateNamespaceDistinguishibility]".to_string()), "{out:?}");
    assert!(out.contains(&"`x` duplicates the inherited member name from `B` — redefine it (`:>>`) or rename it [validateNamespaceDistinguishibility]".to_string()), "{out:?}");
    assert!(
        out.iter()
            .any(|m| m.starts_with("`x` is inherited from both")),
        "{out:?}"
    );
}

#[test]
fn subsetting_at_the_definition_also_clears_its_usages() {
    let out = findings(
        "package P {
            private import ScalarValues::*;
            attribute def SwitchStatus { attribute downlinkPort : Real; }
            attribute def M1SwitchStatus :> SwitchStatus { attribute downlinkPort :> downlinkPort : Real[6]; }
            attribute m1 : M1SwitchStatus;
        }",
    );
    assert!(out.is_empty(), "{out:?}");
}

#[test]
fn owned_members_of_usages_and_nested_definitions_are_checked() {
    let out = findings(
        "package P {
            private import ScalarValues::*;
            part def A { attribute x : Real; part def N; }
            part a : A { attribute x : Real; }
            part def B :> A { part def N; }
        }",
    );
    assert_eq!(out.len(), 2, "{out:?}");
    assert!(
        out.iter()
            .any(|m| m
                .starts_with("`x` duplicates the inherited member name from `A` — redefine it")),
        "{out:?}"
    );
    assert!(out.iter().any(|m| m == "`N` duplicates the inherited member name from `A` — rename it [validateNamespaceDistinguishibility]"), "{out:?}");
}

#[test]
fn protected_members_inherit_and_private_ones_do_not() {
    let out = findings(
        "package P {
            private import ScalarValues::*;
            part def A { protected attribute x : Real; private attribute y : Real; }
            part def B :> A { attribute x : Real; attribute y : Real; }
        }",
    );
    assert_eq!(out.len(), 1, "{out:?}");
    assert!(out[0].starts_with("`x` duplicates"), "{out:?}");
}

#[test]
fn names_reexported_through_a_base_import_collide() {
    let out = findings(
        "package P {
            package Q { attribute def W; }
            part def A { public import Q::*; }
            part def B :> A { attribute def W; }
        }",
    );
    assert_eq!(out.len(), 1, "{out:?}");
    assert!(
        out[0].starts_with("`W` duplicates the inherited member name from `Q`"),
        "{out:?}"
    );
}

#[test]
fn parameters_redefine_positionally_only_under_behaviors() {
    let out = findings(
        "package P {
            private import ScalarValues::*;
            action def Act { in x : Real; }
            action def Act2 :> Act { in x : Real; }
            part def A { in attribute x : Real; }
            part def B :> A { in attribute x : Real; }
        }",
    );
    assert_eq!(out.len(), 1, "{out:?}");
    assert!(
        out[0].starts_with("`x` duplicates the inherited member name from `A`"),
        "{out:?}"
    );
}

#[test]
fn library_features_collide_with_user_usages_and_kerml_features() {
    // The usage is typed by `B`, so its own body inherits both `portions`
    // too — the same second finding a usage typed by any offending
    // definition carries.
    let out = findings(
        "package P {
            part def B { part portions : B; }
        }",
    );
    assert_eq!(out.len(), 2, "{out:?}");
    assert!(
        out[0].starts_with("`portions` duplicates the inherited member name from `Occurrence`"),
        "{out:?}"
    );
    assert!(
        out[1].starts_with("`portions` is inherited from both `B` and `Occurrence`"),
        "{out:?}"
    );
    let out = kerml_findings(
        "package P {
            private import Occurrences::Occurrence;
            classifier Y specializes Occurrence { feature portions; }
        }",
    );
    assert_eq!(out.len(), 1, "{out:?}");
    assert!(
        out[0].starts_with("`portions` duplicates the inherited member name from `Occurrence`"),
        "{out:?}"
    );
}

#[test]
fn a_diamond_reaching_both_sibling_redefinitions_collides() {
    // `Mid2`'s `s` removes `Mid1`'s at `Mid2`'s own level, but `Leaf` also
    // reaches `Mid1` directly and inherits both.
    let out = findings(
        "package P {
            private import ScalarValues::*;
            part def Base { attribute h : Real; }
            part def Mid1 :> Base { attribute s :>> h; }
            part def Mid2 :> Mid1 { attribute s :>> h; }
            part def Leaf :> Mid2, Mid1;
            part def Straight :> Mid2;
        }",
    );
    assert_eq!(out.len(), 1, "{out:?}");
    assert!(
        out[0].starts_with("`s` is inherited from both `Mid1` and `Mid2`"),
        "{out:?}"
    );
}
