//! Grammar edge coverage: corner-of-the-grammar forms that the textual
//! notations permit but that rarely appear in real models. Each case here
//! locks in accepted behavior so later parser changes cannot regress it;
//! sibling cases land together with the fixes that enable them.

use sysmlv2_parser::ast::{Dialect, SourceUnit};
use sysmlv2_parser::parser::{Parse, parse_kerml_source, parse_source};
use sysmlv2_parser::print::format_source;

/// AST equality modulo spans (same normalization as the formatter gates).
fn normalized(unit: &SourceUnit) -> String {
    format!("{unit:#?}")
        .lines()
        .filter(|line| !line.trim_start().starts_with("span:"))
        .collect::<Vec<_>>()
        .join("\n")
}

/// Parse must be clean, and the formatter gates must hold: the formatted
/// text parses clean, is AST-equal to the original, and is idempotent.
#[track_caller]
fn accepts(src: &str, dialect: Dialect) {
    let parse = |s: &str| -> Parse {
        match dialect {
            Dialect::Sysml => parse_source(s),
            Dialect::Kerml => parse_kerml_source(s),
        }
    };
    let Parse { unit, diagnostics } = parse(src);
    assert!(
        diagnostics.is_empty(),
        "unexpected diagnostics for {src:?}:\n{diagnostics:#?}"
    );
    let formatted =
        format_source(src, dialect).unwrap_or_else(|d| panic!("format failed for {src:?}: {d:#?}"));
    let reparsed = parse(&formatted);
    assert!(
        reparsed.diagnostics.is_empty(),
        "formatted output of {src:?} does not parse: {formatted:?}\n{:#?}",
        reparsed.diagnostics
    );
    assert_eq!(
        normalized(&unit),
        normalized(&reparsed.unit),
        "AST changed by formatting {src:?} -> {formatted:?}"
    );
    let second = format_source(&formatted, dialect)
        .unwrap_or_else(|d| panic!("re-format failed for {formatted:?}: {d:#?}"));
    assert_eq!(second, formatted, "formatting not idempotent for {src:?}");
}

#[track_caller]
fn sysml_ok(src: &str) {
    accepts(src, Dialect::Sysml);
}

#[track_caller]
fn kerml_ok(src: &str) {
    accepts(src, Dialect::Kerml);
}

// ---- multiplicity part / ordering markers in declarations ----

#[test]
fn declaration_reduced_to_multiplicity_or_ordering() {
    // A declaration may consist of nothing but a multiplicity, nothing but
    // ordering markers, or the markers in either order around specializations.
    kerml_ok("package P { feature [2]; }");
    kerml_ok("package P { feature ordered; }");
    kerml_ok("package P { feature nonunique; }");
    kerml_ok("package P { feature ordered nonunique; }");
    kerml_ok("package P { struct S { feature [2]; } }");
    kerml_ok("package P { feature f : T [1] ordered :> g; }");
    sysml_ok("package P { part [2]; }");
    sysml_ok("package P { part ordered; }");
    sysml_ok("package P { item nonunique ordered; }");
    sysml_ok("package P { attribute a : T [0..2] nonunique; }");
    // Keyword-less members reduced to only ordering markers or a
    // multiplicity are legal too.
    kerml_ok("package P { struct S { ordered; } }");
    kerml_ok("package P { struct S { nonunique ordered; } }");
    kerml_ok("package P { struct S { [2]; } }");
    sysml_ok("package P { part p { ordered; } }");
    sysml_ok("package P { part p { nonunique; } }");
    sysml_ok("package P { part p { [2]; } }");
}

#[test]
fn payload_typing_and_declaration_without_identification() {
    // PayloadFeature admits an identification-less owned typing, with an
    // optional multiplicity, as well as the declaration form whose
    // multiplicity part precedes a required specialization.
    kerml_ok("package P { datatype T; flow f of T; }");
    kerml_ok("package P { datatype T; flow f of [1] T; }");
    kerml_ok("package P { datatype T; flow f of ordered : T; }");
    kerml_ok("package P { datatype T; flow f of [1] ordered nonunique : T; }");
    sysml_ok("package P { item def T; action def A { accept T; } }");
    sysml_ok("package P { item def T; action def A { accept [1] T; } }");
    sysml_ok("package P { item def T; action def A { accept ordered : T; } }");
    sysml_ok("package P { item def T; action def A { accept [1] nonunique ordered : T; } }");
}

#[test]
fn empty_declaration_after_kind_keyword() {
    // `UsageDeclaration` is optional: a kind keyword directly followed by
    // the body terminator is a legal usage.
    sysml_ok("package P { part; }");
    sysml_ok("package P { part { } }");
    kerml_ok("package P { step; }");
    // The `ref` reference-usage keyword takes an optional `Usage` too.
    sysml_ok("package P { ref; }");
    sysml_ok("package P { ref { } }");
    sysml_ok("package P { part p { in ref; } }");
    sysml_ok("package P { abstract ref; }");
}

#[test]
fn multiplicity_bounds_all_literal_kinds() {
    // A multiplicity bound may own any literal expression, not only
    // integers and infinity.
    kerml_ok("package P { feature f : T [true]; }");
    kerml_ok("package P { feature f : T [\"n\"]; }");
    kerml_ok("package P { feature f : T [false..true]; }");
    kerml_ok("package P { feature f : T [1.5]; }");
    sysml_ok("package P { part p : T [true]; }");
    sysml_ok("package P { part p : T [\"n\"..\"m\"]; }");
    sysml_ok("package P { part p : T [0..*]; }");
    kerml_ok("package P { multiplicity m [true]; }");
}

// ---- sufficiency-marked connector declarations ----

#[test]
fn succession_all_declaration_less() {
    // The declaration alternative carrying only the sufficiency marker and
    // connector ends (no leading relational keyword) is legal.
    kerml_ok("package P { succession all s1 then s2; }");
    kerml_ok("package P { succession first s1 then s2; }");
}

#[test]
fn connector_all_declaration_less() {
    // The same sufficiency-marked alternative exists on the other binary
    // connector declarations, with the relational keyword optional.
    kerml_ok("package P { connector all a.x to b.y; }");
    kerml_ok("package P { connector all from a.x to b.y; }");
    kerml_ok("package P { binding all x = y; }");
    kerml_ok("package P { binding all of x = y; }");
    kerml_ok("package P { flow all a.x to b.y; }");
    kerml_ok("package P { succession flow all a.x to b.y; }");
    // Declared forms with the marker keep parsing.
    kerml_ok("package P { connector all c : C from a.x to b.y; }");
    kerml_ok("package P { flow all f of p from a.x to b.y; }");
}

#[test]
fn connector_all_declaration_owns_its_multiplicity() {
    // A multiplicity after `all` may belong to the feature declaration;
    // it is not necessarily the first connector end's cross multiplicity.
    kerml_ok("package P { connector all [1] from a to b; }");
    kerml_ok("package P { connector all [1] : C from a to b; }");
    kerml_ok("package P { binding all [1] of a = b; }");
    kerml_ok("package P { binding all [1] : C of a = b; }");
    kerml_ok("package P { succession all [1] first a then b; }");
    kerml_ok("package P { succession all [1] : C first a then b; }");
}

// ---- end features with a multiplicity-shaped cross feature ----

#[test]
fn end_prefix_with_multiplicity_cross_feature() {
    sysml_ok("package P { connection def C { end [1] item x : X; } }");
    sysml_ok("package P { connection def C { end [0..1] part cart : Cart [1]; } }");
    // An end feature with no cross feature at all.
    sysml_ok("package P { connection def C { end item x : X; } }");
    kerml_ok("package P { assoc A { end feature x : T; } }");
}

#[test]
fn end_prefix_cross_feature_all_starts() {
    // The cross feature is a full declaration with its own basic prefix; it
    // need not begin with a multiplicity.
    sysml_ok("package P { connection def C { end cart : Cart item x : X; } }");
    sysml_ok("package P { connection def C { end derived c : Cart [1] item x : X; } }");
    sysml_ok("package P { connection def C { end in c : Cart ref r : R; } }");
    sysml_ok("package P { connection def C { end ref c : Cart part p : P; } }");
    sysml_ok("package P { connection def C { end constant c : Cart part p : P; } }");
    kerml_ok("package P { assoc A { end in x : T feature y : U; } }");
    kerml_ok("package P { assoc A { end derived x : T feature y; } }");
    kerml_ok("package P { assoc A { end composite var x [1] feature y; } }");
    kerml_ok("package P { assoc A { end const x : T feature y; } }");
    kerml_ok("package P { end x : T connector a.b to c.d; }");
    // Cross features also precede the other feature-introducing keywords.
    kerml_ok("package P { end x : T step s; }");
}

#[test]
fn end_cross_feature_marker_and_continuation_residues() {
    kerml_ok("package P { end ordered feature y; }");
    kerml_ok("package P { end nonunique ordered feature y; }");
    kerml_ok("package P { end x : T y : U; }");

    sysml_ok("package P { connection def C { end ordered part p; } }");
    sysml_ok("package P { connection def C { end c : T bind a = b; } }");
    sysml_ok("package P { connection def C { end c : T #M x; } }");
    sysml_ok("package P { connection def C { end c : T first a then b; } }");
    sysml_ok("package P { connection def C { end c : T connect a to b; } }");
}

#[test]
fn succession_shorthand_under_metadata_and_variant_prefixes() {
    sysml_ok("package P { action def A { #M first a then b; } }");
    sysml_ok("package P { variation action def A { variant first a then b; } }");
}

// ---- metadata features, type featurings, prefix metadata positions ----

#[test]
fn metadata_declaration_empty_identification() {
    // The leading identification group may be taken with an empty
    // identification: a bare separator before the metaclass.
    kerml_ok("package P { @ : M; }");
    kerml_ok("package P { @ typed by M; }");
    kerml_ok("package P { metadata : M about x; }");
    sysml_ok("package P { @ : M; }");
    sysml_ok("package P { @ defined by M; }");
    // Named forms keep parsing.
    kerml_ok("package P { @ n : M; }");
    sysml_ok("package P { metadata n : M about x; }");
}

#[test]
fn metadata_body_redefinition_accepts_owned_feature_chains() {
    kerml_ok("package P { metaclass M; @M { a.b = 1; } }");
    sysml_ok("package P { metadata def M; part p { @M { a.b = 1; } } }");
}

#[test]
fn type_featuring_empty_identification() {
    kerml_ok("package P { featuring of x by T; }");
    kerml_ok("package P { featuring f of x by T; }");
    kerml_ok("package P { featuring x by T; }");
}

#[test]
fn prefix_metadata_before_metadata_and_namespace() {
    kerml_ok("package P { #foo @ M; }");
    kerml_ok("#foo namespace N { }");
    kerml_ok("package P { #foo metadata : M; }");
    sysml_ok("package P { #foo @ M; }");
    sysml_ok("package P { #foo metadata n : M about x; }");
}

// ---- expression positions with minimal owned expressions ----

#[test]
fn filter_conditions_minimal_expressions() {
    // Implicit-self classification, null, and the empty-sequence literal are
    // the smallest expressions a filter condition can own.
    sysml_ok("package P { filter istype T; }");
    sysml_ok("package P { filter @M; }");
    sysml_ok("package P { filter hastype T and @M; }");
    sysml_ok("package P { filter null; }");
    sysml_ok("package P { filter (); }");
    kerml_ok("package P { filter istype T; }");
}

#[test]
fn value_parts_minimal_expressions() {
    sysml_ok("package P { attribute a = null; }");
    sysml_ok("package P { attribute a = (); }");
    sysml_ok("package P { attribute a default := 2; }");
    sysml_ok("package P { attribute a default 2; }");
    kerml_ok("package P { feature f = as T; }");
}

// ---- action node declarations ----

#[test]
fn accept_node_trigger_forms() {
    sysml_ok("package P { action def A { accept x : T; } }");
    sysml_ok("package P { action def A { accept x : T at t0; } }");
    sysml_ok("package P { action def A { accept x : T after dt; } }");
    sysml_ok("package P { action def A { accept when c; } }");
    sysml_ok("package P { action def A { accept at t0; } }");
    sysml_ok("package P { action def A { accept x : T via p; } }");
}

#[test]
fn send_node_parameter_forms() {
    sysml_ok("package P { action def A { send x; } }");
    sysml_ok("package P { action def A { send x via p; } }");
    sysml_ok("package P { action def A { send x to q; } }");
    sysml_ok("package P { action def A { send x via p to q; } }");
    sysml_ok("package P { action def A { action n send x via p to q; } }");
}

#[test]
fn assignment_node_target_forms() {
    sysml_ok("package P { action def A { assign x := 1; } }");
    sysml_ok("package P { action def A { assign a.b.c := v; } }");
    sysml_ok("package P { action def A { action n1 : N assign x := f(y); } }");
    sysml_ok("package P { action def A { action n1 accept x : T; } }");
}

// ---- transition forms ----

#[test]
fn transition_and_target_succession_forms() {
    sysml_ok(
        "package P { state def S { transition t first s1 accept sig : Sig if g do send e to q then s2; } }",
    );
    sysml_ok("package P { state def S { s1 { } then s2; } }");
    sysml_ok("package P { state def S { s1 { } if g then s2; } }");
    sysml_ok("package P { state def S { s1 { } do send a to b; } }");
    sysml_ok("package P { state def S { transition first s1 if g then s2; } }");
    // Guard-first target transitions may carry an effect before `then`.
    sysml_ok("package P { state def S { s1 { } if g do send x to t then s2; } }");
    sysml_ok("package P { state def S { s1 { } if g do action a { } then s2; } }");
    // The target succession's membership prefix precedes its optional
    // multiplicity-only source end.
    sysml_ok("package P { action def A { private [1] then next; } }");
}

#[test]
fn transition_effect_brace_bodies() {
    // Every effect behavior form takes an optional brace body.
    sysml_ok("package P { state def S { s1 { } do accept x : X { } then s2; } }");
    sysml_ok(
        "package P { state def S { s1 { } accept go if g do assign a := b { part q; } then s2; } }",
    );
    sysml_ok("package P { state def S { s1 { } do send e to q { } then s2; } }");
}

#[test]
fn nested_if_node_keeps_its_action_node_prefix() {
    sysml_ok("package P { action def A { if true { } else action nested if false { } } }");
    sysml_ok("package P { action def A { if true { } else individual if false { } } }");
    sysml_ok(
        "package P { action def A { if true { } else individual action nested if false { } } }",
    );
}

#[test]
fn source_succession_precedes_a_full_member() {
    sysml_ok("package P { action def A { then [1] action next; } }");
    sysml_ok("package P { action def A { then [0..1] #M action next; } }");
}

#[test]
fn declared_state_action_nodes_dispatch_after_the_declaration() {
    sysml_ok("package P { state def S { entry action a accept x : T; } }");
    sysml_ok("package P { state def S { do action a send x; } }");
    sysml_ok("package P { state def S { exit action a assign x := y; } }");
}

#[test]
fn transition_effect_remaining_alternatives() {
    sysml_ok("package P { state def S { s {} do then t; } }");
    sysml_ok("package P { state def S { s {} do action e = x {} then t; } }");
    sysml_ok("package P { state def S { s {} do action e accept x : T {} then t; } }");
    sysml_ok("package P { state def S { s {} do action e send x {} then t; } }");
    sysml_ok("package P { state def S { s {} do action e assign x := y {} then t; } }");
    // A complete state `do` subaction must not absorb a `then` from the
    // following transition member.
    sysml_ok("package P { state def S { do action work { out x; } transition x then y; } }");
}

#[test]
fn sysml_semicolon_expression_bodies() {
    sysml_ok("package P { attribute a = ;; }");
    sysml_ok("package P { attribute a = 1 + ;; }");
    sysml_ok("package P { attribute a = xs.;; }");
    sysml_ok("package P { attribute a = xs.?;; }");
    sysml_ok("package P { attribute a = xs->F ;; }");
}

#[test]
fn empty_usage_after_special_prefixes_and_in_enumerations() {
    sysml_ok("package P { connection def C { end; } }");
    sysml_ok("package P { occurrence def O { individual; snapshot; timeslice; } }");
    sysml_ok("package P { variation part def V { variant; } }");
    sysml_ok("package P { enum def E { ; } }");
}

#[test]
fn interface_part_may_start_with_a_multiplicity() {
    sysml_ok("package P { interface [1] a to b; }");
    sysml_ok("package P { interface [0..1] a to [1] b; }");
    sysml_ok("package P { interface (a, b, c); }");
}

#[test]
fn plain_usage_members_take_extension_keywords() {
    // The `subject`/`actor`/`stakeholder`/`objective` keywords may be
    // followed by `#Meta` extension keywords.
    sysml_ok("package P { requirement def R { subject #M s : T; } }");
    sysml_ok("package P { requirement def R { actor #M a; } }");
    sysml_ok("package P { requirement def R { stakeholder #M s; } }");
    sysml_ok("package P { requirement def R { objective #M o { } } }");
}

// ---- trailing result expressions ----

#[test]
fn trailing_result_expressions() {
    kerml_ok("package P { function F { in x; x + 1 } }");
    kerml_ok("package P { feature y = {in x; x + 1}; }");
    sysml_ok("package P { calc def C { in x : R; x + 1 } }");
    // The result member takes the ordinary member prefix, so it may carry
    // a visibility marker — also when the body is nested in an expression.
    kerml_ok("package P { function F { in x; private x + 1 } }");
    kerml_ok("package P { feature y = {in x; protected x + 1}; }");
    sysml_ok("package P { calc def C { in x : R; public x + 1 } }");
    sysml_ok("package P { constraint def K { private 1 > 0 } }");
}
