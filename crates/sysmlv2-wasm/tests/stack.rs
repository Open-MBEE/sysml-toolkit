//! The module's reserved stack against the depths the toolkit's recursive
//! passes bound themselves to.
//!
//! On the wasm target a bound the stack cannot hold is not a diagnostic
//! but a trap, so the reservation and the bounds have to agree. These
//! tests hold the reservation to the build that applies it, and run the
//! bounds within it.
//!
//! What no test here can do is observe the reservation a wasm link
//! actually applies: that needs the module built for the wasm target and
//! its stack pointer read out of the linked binary, and these tests run
//! on the host. The probes below therefore run the bounds inside a *host*
//! thread the size of the reservation — they answer "is this size enough
//! for the bounds", not "did the module get this size". The second
//! question is held by [`the_build_reserves_the_declared_stack`], which
//! pins that the build reads the size from the crate and passes it to the
//! linker for both artifacts; if that wiring is removed, the size the
//! probes work against is no longer the size the module gets.

use sysmlv2_model::lift::MAX_LIFT_DEPTH;
use sysmlv2_syntax::parser::{MAX_NESTING, MAX_NESTING_STACK_BYTES, parse_source};
use sysmlv2_wasm::WASM_STACK_BYTES;

/// The linker's own default, which the reservation exists to replace.
const LINKER_DEFAULT_STACK_BYTES: usize = 1 << 20;

/// The build applies the reservation the crate declares, reading it from
/// the crate rather than repeating it.
///
/// This is the one test here that pins the reservation reaching a built
/// module; it does so through the build's wiring rather than by reading a
/// module, because building one is not something a unit test does.
#[test]
fn the_build_reserves_the_declared_stack() {
    // A reservation at or below the linker's own default asks for
    // nothing, and the flag below would be decoration.
    const {
        assert!(WASM_STACK_BYTES > LINKER_DEFAULT_STACK_BYTES);
    }
    let build = include_str!("../npm/build.mjs");
    assert!(
        build.contains("WASM_STACK_BYTES: usize = (\\d+);"),
        "the build script no longer reads the size from the crate"
    );
    assert!(
        build.contains("-C link-arg=-zstack-size=${stackSizeBytes}"),
        "the build script no longer passes the size to the linker"
    );
    assert_eq!(
        build
            .matches("-C link-arg=-zstack-size=${stackSizeBytes}")
            .count(),
        2,
        "both wasm artifacts — the module and the command-line binary — reserve it"
    );
}

/// One level of the *lift* costs about twenty times as much unoptimized
/// as optimized, and its bound is reachable in single megabytes only
/// when optimized. The shipped module is always optimized, so an
/// unoptimized probe of that bound is given that much more room — which
/// means the unoptimized run of [`the_reserved_stack_holds_the_lift_bound`]
/// is not a gate on the reservation: it checks that the bound is
/// reachable at all, and the optimized run is what holds the size.
///
/// The parser's bound needs no such allowance: its probe runs at the
/// reservation itself in either build (see
/// [`the_reserved_stack_holds_the_parser_bound`]).
const LIFT_PROFILE_FACTOR: usize = if cfg!(debug_assertions) { 20 } else { 1 };

/// Input past the parser's bound stops at it with a diagnostic, and
/// input up to it parses, both within a stack the size of the
/// reservation — in either build, so an unoptimized run gates the
/// reservation as much as an optimized one does. A host thread stands in
/// for the module's stack — see the note at the top of this file for what
/// that does and does not pin.
///
/// Two shapes reach the bound: bodies nested to it, and nesting that also
/// carries an operator chain at every level. The first is the more
/// expensive of the two, and the second is the one a written model gets
/// near.
#[test]
fn the_reserved_stack_holds_the_parser_bound() {
    // The reservation covers what the parser's own bound asks for.
    const {
        assert!(WASM_STACK_BYTES >= MAX_NESTING_STACK_BYTES);
    }
    std::thread::Builder::new()
        .stack_size(WASM_STACK_BYTES)
        .spawn(|| {
            let levels = MAX_NESTING as usize;
            let src = format!(
                "package P {{ {}{} }}",
                "part x { ".repeat(levels - 1),
                "}".repeat(levels - 1)
            );
            let parse = parse_source(&src);
            assert!(
                parse.diagnostics.is_empty(),
                "{levels} levels should parse: {:#?}",
                parse.diagnostics
            );

            let chain = (0..960)
                .map(|i| format!("a{i} > 0"))
                .collect::<Vec<_>>()
                .join(" and ");
            let src = format!(
                "package P {{ {}part y;{} }}",
                format!("part x {{ attribute v = {chain}; ").repeat(60),
                "}".repeat(60)
            );
            let parse = parse_source(&src);
            assert!(
                parse.diagnostics.is_empty(),
                "nesting carrying a full chain per level should parse: {:#?}",
                parse.diagnostics
            );

            let src = format!(
                "package P {{ {}{} }}",
                "part x { ".repeat(10_000),
                "}".repeat(10_000)
            );
            let parse = parse_source(&src);
            assert!(
                parse
                    .diagnostics
                    .iter()
                    .any(|d| d.message.contains("nesting is too deep")),
                "expected the bound to be reported, got {:?}",
                parse.diagnostics.first().map(|d| d.message.clone())
            );
        })
        .unwrap()
        .join()
        .unwrap();
}

/// The lift's bound is reached within a stack the size of the
/// reservation too. On this host the lift moves a payload that could nest
/// deeply onto a stack of its own; the wasm target has no threads and
/// lifts in place, which is what the reservation is for, so the probe
/// runs the whole lift inside it — again on a host thread, see the note
/// at the top of this file.
///
/// Only the optimized run gates the reservation here: an unoptimized
/// step costs about twenty times as much, so the probe is given that
/// much more room and could not detect an undersized reservation. See
/// [`LIFT_PROFILE_FACTOR`].
#[test]
fn the_reserved_stack_holds_the_lift_bound() {
    std::thread::Builder::new()
        .stack_size(WASM_STACK_BYTES * LIFT_PROFILE_FACTOR)
        .spawn(|| {
            let depth = MAX_LIFT_DEPTH * 2;
            let mut elements = Vec::new();
            for i in 0..depth {
                // Ownership is spelled both ways round, as a payload
                // spells it: the chain then has the one root it reads as.
                let mut membership = serde_json::json!({
                    "@id": format!("m{i}"),
                    "@type": "OwningMembership",
                    "ownedRelatedElement": [{ "@id": format!("p{i}") }],
                });
                if i > 0 {
                    membership["owningRelatedElement"] =
                        serde_json::json!({ "@id": format!("p{}", i - 1) });
                }
                elements.push(membership);
                let owned = if i + 1 < depth {
                    serde_json::json!([{ "@id": format!("m{}", i + 1) }])
                } else {
                    serde_json::json!([])
                };
                elements.push(serde_json::json!({
                    "@id": format!("p{i}"),
                    "@type": "PartUsage",
                    "declaredName": format!("p{i}"),
                    "owningRelationship": { "@id": format!("m{i}") },
                    "ownedRelationship": owned,
                }));
            }
            let Err(sysmlv2_model::lift::LiftError::Incomplete { errors }) =
                sysmlv2_model::lift::from_compact_json_on_this_stack(
                    &serde_json::Value::Array(elements),
                    &std::collections::HashMap::new(),
                )
            else {
                panic!("an over-budget document must not return a partial AST")
            };
            assert!(
                errors
                    .iter()
                    .any(|e| e.contains("ownership nesting deeper than")),
                "expected the bound to be reported, got {:?}",
                errors
            );
            // One report for the truncated subtree, not one per element
            // past the bound.
            assert_eq!(
                errors
                    .iter()
                    .filter(|e| e.contains("ownership nesting deeper than"))
                    .count(),
                1,
                "{:?}",
                errors
            );
        })
        .unwrap()
        .join()
        .unwrap();
}
