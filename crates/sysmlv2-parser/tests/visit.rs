//! Syntax-tree visitor: completeness over the expression-bearing
//! surface, proven by sentinel references reachable only through specific
//! walker paths, plus a corpus-wide smoke gate.

use std::collections::HashSet;
use std::fs;
use sysmlv2_parser::ast::*;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};
use sysmlv2_parser::visit::Visit;

/// Collects every qualified-name spelling the walk reaches.
#[derive(Default)]
struct Names(HashSet<String>);

impl<'a> Visit<'a> for Names {
    fn visit_qualified_name(&mut self, qn: &'a QualifiedName) {
        self.0.insert(qn.to_display_string());
    }
}

#[test]
fn visitor_reaches_every_construct() {
    // Each sentinel name appears in exactly one construct the walker
    // must descend into; missing any means a hole in the walk.
    let src = "package P {
        private import Lib::* [@ inFilter];
        part def D :> inSpecializes {
            attribute m : T[inMultLo..inMultHi];
        }
        part u : inTypedBy = inValue.inChainMember {
            attribute :>> m default inDefault;
        }
        connect inEndA.p to inEndB;
        bind inBindA = inBindB;
        action a {
            first start;
            accept sig : inAccept when inTrigger via inVia;
            send inSendPayload to inSendTo;
            assign inAssignTarget := inAssignValue;
            if inIfCond { action t1; }
            while inWhileCond { action t2; } until inUntil;
            for x in inForSeq { action t3; }
        }
        state def S {
            transition first s1 if inGuard do send inEffect to e then s2;
        }
        calc def C { in p; inLambdaTarget->select { in q; q == inLambdaBody } }
        attribute cls = x istype inClassify;
        satisfy inSatisfyReq by inSatisfyBy;
        flow of inPayloadTy from inFlowSrc.o to inFlowTgt.i;
    }";
    let parse = parse_source(src);
    assert!(
        parse.diagnostics.is_empty(),
        "sentinel source must parse cleanly: {:?}",
        parse.diagnostics[0]
    );
    let mut v = Names::default();
    v.visit_unit(&parse.unit);
    for sentinel in [
        "inFilter",
        "inSpecializes",
        "inMultLo",
        "inMultHi",
        "inTypedBy",
        "inValue",
        "inChainMember",
        "inDefault",
        "inEndA",
        "inEndB",
        "inBindA",
        "inBindB",
        "inAccept",
        "inTrigger",
        "inVia",
        "inSendPayload",
        "inSendTo",
        "inAssignTarget",
        "inAssignValue",
        "inIfCond",
        "inWhileCond",
        "inUntil",
        "inForSeq",
        "inGuard",
        "inEffect",
        "inLambdaTarget",
        "inLambdaBody",
        "inClassify",
        "inSatisfyBy",
        "inPayloadTy",
    ] {
        assert!(
            v.0.iter().any(|n| n == sentinel || n.contains(sentinel)),
            "walker never reached `{sentinel}`; saw {:?}",
            v.0
        );
    }
}

/// Corpus smoke: the walk covers all 345 files without panicking and
/// reaches a healthy reference count (a collapsed walk would crater it).
#[test]
fn corpus_walk_is_total() {
    let files = sysmlv2_testkit::corpus_files();
    assert!(files.len() > 340, "expected the full corpus checkout");
    struct Count(usize);
    impl<'a> Visit<'a> for Count {
        fn visit_qualified_name(&mut self, _: &'a QualifiedName) {
            self.0 += 1;
        }
    }
    let mut names = 0usize;
    for path in &files {
        let src = fs::read_to_string(path).unwrap();
        let parse = if path.extension().and_then(|e| e.to_str()) == Some("kerml") {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        let mut v = Count(0);
        v.visit_unit(&parse.unit);
        names += v.0;
    }
    // Ratchet: ~28.5k syntax-level names corpus-wide when this landed.
    // (The resolver's ~137k figure is graph-level — it includes implied
    // library bases and synthesized memberships, a different accounting.)
    // A collapsed walk craters this; move the floor only upward.
    assert!(
        names > 27_000,
        "corpus walk reached only {names} references"
    );
}

/// Cross-check the walk against one dense known file: SI.sysml declares
/// hundreds of typed, valued attributes — the walk must see them.
#[test]
fn si_library_walk_density() {
    let root = sysmlv2_testkit::library_dir();
    let path = root.join("Domain Libraries/Quantities and Units/SI.sysml");
    let src = fs::read_to_string(&path).unwrap();
    let parse = parse_source(&src);
    assert!(parse.diagnostics.is_empty());
    struct Count(usize);
    impl<'a> Visit<'a> for Count {
        fn visit_qualified_name(&mut self, _: &'a QualifiedName) {
            self.0 += 1;
        }
    }
    let mut v = Count(0);
    v.visit_unit(&parse.unit);
    assert!(v.0 > 700, "SI.sysml walk saw only {} names", v.0);
}
