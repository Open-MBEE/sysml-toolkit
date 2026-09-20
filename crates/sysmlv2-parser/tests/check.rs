//! Body-context validation: the corpus must validate with zero
//! diagnostics (no false positives), and known-illegal member placements
//! must be reported.

use std::fs;
use sysmlv2_parser::check::{validate, validate_model};
use sysmlv2_parser::model::Model;
use sysmlv2_parser::parser::{parse_kerml_source, parse_source};

#[test]
fn corpus_validates_without_diagnostics() {
    let files = sysmlv2_testkit::corpus_files();

    let mut failures = Vec::new();
    for path in files {
        let src = fs::read_to_string(&path).unwrap();
        let parse = if path.extension().and_then(|e| e.to_str()) == Some("kerml") {
            parse_kerml_source(&src)
        } else {
            parse_source(&src)
        };
        assert!(
            parse.diagnostics.is_empty(),
            "{}: parse failed",
            path.display()
        );
        for d in validate(&parse.unit) {
            failures.push(format!("{}: {}", path.display(), d.message));
        }
    }
    assert!(
        failures.is_empty(),
        "{} false positives on the corpus:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

/// Parse SysML source (must parse cleanly) and validate it.
fn check_sysml(src: &str) -> Vec<String> {
    let parse = parse_source(src);
    assert!(
        parse.diagnostics.is_empty(),
        "test source must parse cleanly, got: {}",
        parse.diagnostics[0].message
    );
    validate(&parse.unit)
        .into_iter()
        .map(|d| d.message)
        .collect()
}

fn check_kerml(src: &str) -> Vec<String> {
    let parse = parse_kerml_source(src);
    assert!(
        parse.diagnostics.is_empty(),
        "test source must parse cleanly, got: {}",
        parse.diagnostics[0].message
    );
    validate(&parse.unit)
        .into_iter()
        .map(|d| d.message)
        .collect()
}

/// Assert exactly one diagnostic whose message contains `expect`.
fn assert_one_error(src: &str, expect: &str) {
    let msgs = check_sysml(src);
    assert_eq!(
        msgs.len(),
        1,
        "expected exactly one diagnostic for {src:?}, got {msgs:#?}"
    );
    assert!(
        msgs[0].contains(expect),
        "expected {expect:?} in {:?}",
        msgs[0]
    );
}

#[test]
fn transition_in_part_body() {
    assert_one_error(
        "part def P { transition first a then b; }",
        "transition usage is not allowed in a definition or usage body",
    );
}

#[test]
fn action_nodes_outside_action_bodies() {
    assert_one_error(
        "part def P { send x() to y; }",
        "send action node is not allowed in a definition or usage body",
    );
    // Bare action nodes in a *state* body must go through entry/do/exit.
    assert_one_error(
        "state def S { assign x := 1; }",
        "assignment action node is not allowed in a state body",
    );
    assert_one_error(
        "package P { merge m; }",
        "merge node is not allowed in a package body",
    );
}

#[test]
fn state_subactions_only_in_states() {
    assert_one_error(
        "part def P { entry; }",
        "`entry` action member is not allowed in a definition or usage body",
    );
    assert_one_error(
        "action def A { do send s() to t; }",
        "`do` action member is not allowed in an action body",
    );
}

#[test]
fn requirement_members_only_in_requirements() {
    assert_one_error(
        "part def P { subject s; }",
        "`subject` member is not allowed in a definition or usage body",
    );
    assert_one_error(
        "part def P { require constraint { true } }",
        "`require` constraint member is not allowed in a definition or usage body",
    );
    assert_one_error(
        "case def C { stakeholder s; }",
        "`stakeholder` member is not allowed in a case body",
    );
    assert_one_error(
        "requirement def R { objective o { doc /* goal */ } }",
        "`objective` member is not allowed in a requirement body",
    );
}

#[test]
fn initial_node_contexts() {
    assert_one_error(
        "part def P { first start; }",
        "initial-node member (`first`) is not allowed in a definition or usage body",
    );
    // Not even in state bodies (only transitions target states).
    assert_one_error(
        "state def S { first start; }",
        "initial-node member (`first`) is not allowed in a state body",
    );
}

#[test]
fn view_members() {
    // `expose` belongs to view *usages*, not view definitions.
    assert_one_error(
        "view def V { expose A::*; }",
        "`expose` member is not allowed in a view definition body",
    );
    assert_one_error(
        "part def P { render asTree; }",
        "`render` member is not allowed in a definition or usage body",
    );
    assert!(check_sysml("view v { expose A::*; render asTree; }").is_empty());
}

#[test]
fn filter_contexts() {
    assert_one_error(
        "part def P { filter @Safety; }",
        "`filter` member is not allowed in a definition or usage body",
    );
    assert!(check_sysml("package P { filter @Safety; }").is_empty());
    assert!(check_sysml("view def V { filter @Safety; }").is_empty());
}

#[test]
fn return_and_result_contexts() {
    assert_one_error(
        "part def P { return x : Real; }",
        "`return` parameter member is not allowed in a definition or usage body",
    );
    assert!(check_sysml("calc def C { return x : Real; x + 1 }").is_empty());
}

#[test]
fn variant_requires_variation() {
    assert_one_error(
        "part def P { variant part v; }",
        "`variant` member is only allowed in the body of a `variation`",
    );
    assert_one_error(
        "package P { variant part v; }",
        "`variant` member is only allowed in the body of a `variation`",
    );
    assert!(check_sysml("variation part def P { variant part v; }").is_empty());
    assert!(check_sysml("part def E { variation part p { variant part v; } }").is_empty());
}

#[test]
fn enum_body_members() {
    assert_one_error(
        "enum def E { part p; }",
        "part usage is not allowed in an enumeration definition body",
    );
    assert_one_error(
        "enum def E { private import Other::*; }",
        "import is not allowed in an enumeration definition body",
    );
    assert!(check_sysml("enum def E { red; green; doc /* colors */ }").is_empty());
}

#[test]
fn package_level_shorthands() {
    assert_one_error(
        "package P { then t; }",
        "target succession (`then`) is not allowed in a package body",
    );
    assert_one_error(
        "package P { if go then t; }",
        "transition usage is not allowed in a package body",
    );
}

#[test]
fn action_body_shorthands_are_legal() {
    assert!(
        check_sysml(
            "action def A {
             first start;
             action a1;
             then a2;
             action a2;
             if c then done;
             else stop;
             first a1 if ok then a2;
         }"
        )
        .is_empty()
    );
}

#[test]
fn state_body_members_are_legal() {
    assert!(
        check_sysml(
            "state def S {
             entry; then s1;
             do send sig() to x;
             exit action cleanup;
             state s1;
             transition first s1 accept go then s2;
             state s2;
         }"
        )
        .is_empty()
    );
}

#[test]
fn calc_and_case_members_are_legal() {
    assert!(check_sysml("calc def C { in x : Real; return y : Real; x * 2 }").is_empty());
    assert!(check_sysml(
        "use case def U { subject s; actor a; objective { doc /* goal */ } include use case other; }"
    )
    .is_empty());
}

#[test]
fn requirement_members_are_legal() {
    assert!(
        check_sysml(
            "requirement def R {
             subject s;
             actor a;
             stakeholder sh;
             assume constraint { true }
             require constraint { true }
             frame concern c;
         }"
        )
        .is_empty()
    );
}

#[test]
fn kerml_contexts() {
    // `filter` is a package-body member in KerML, not a type-body member.
    let msgs = check_kerml("class C { filter x; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("`filter` member is not allowed in a type body"));

    let msgs = check_kerml("class C { return x; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("`return` parameter member is not allowed in a type body"));

    assert!(check_kerml("package P { filter x; }").is_empty());
    assert!(check_kerml("function f { in x : A; return y : A; x }").is_empty());
}

#[test]
fn imports_require_visibility() {
    assert_one_error(
        "package P { import Other::*; }",
        "import must declare an explicit visibility",
    );
    assert!(check_sysml("package P { private import Other::*; }").is_empty());
    assert!(check_sysml("package P { public import all Other::thing; }").is_empty());
    // `expose` carries its own visibility keyword.
    assert!(check_sysml("view v { expose A::*; }").is_empty());
    let msgs = check_kerml("package P { import Other::*; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("import must declare an explicit visibility"));
}

#[test]
fn top_level_imports_must_be_private() {
    assert_one_error(
        "public import Other::*;",
        "validateImportTopLevelVisibility: a top-level import must be private",
    );
    assert!(check_sysml("private import Other::*;").is_empty());
    // Public imports remain legal when owned by a package.
    assert!(check_sysml("package P { public import Other::*; }").is_empty());
}

#[test]
fn duplicate_member_names() {
    assert_one_error(
        "part def P { part x; part x; }",
        "name `x` is already used by an earlier member",
    );
    // Short names participate in distinguishability.
    assert_one_error(
        "package P { part def <D> Dee; part def D; }",
        "name `D` is already used by an earlier member",
    );
    // Aliases contribute names too.
    assert_one_error(
        "package P { part def A; alias A for B; }",
        "name `A` is already used by an earlier member",
    );
    // An element's own short name may equal its name.
    assert!(check_sysml("package P { part def <D> D; }").is_empty());
    // Same name in sibling namespaces is fine.
    assert!(check_sysml("package P { part def X; } package Q { part def X; }").is_empty());
    // KerML Membership::isDistinguishableFrom permits equal names when
    // neither member element's metaclass conforms to the other.
    assert!(check_sysml("package P { part def X; attribute def X; }").is_empty());
    // A PartDefinition is an ItemDefinition, so these metaclasses are not
    // distinguishable even though their concrete kinds differ.
    assert_one_error(
        "package P { item def X; part def X; }",
        "name `X` is already used by an earlier member",
    );
    // Redefinitions without their own declared name contribute nothing.
    assert!(check_sysml("part def B { attribute m; } part def C :> B { :>> m = 1; }").is_empty());
}

#[test]
fn requirement_and_case_subject_cardinalities() {
    assert_one_error(
        "requirement def R { subject s1; subject s2; }",
        "validateRequirementDefinitionOnlyOneSubject",
    );
    assert_one_error(
        "case def C { subject s1; subject s2; }",
        "validateCaseDefinitionOnlyOneSubject",
    );
    assert_one_error(
        "case def C { objective o1; objective o2; }",
        "validateCaseDefinitionOnlyOneObjective",
    );
    assert_one_error(
        "requirement r { subject s1; subject s2; }",
        "validateRequirementUsageOnlyOneSubject",
    );
    assert_one_error(
        "case c { objective o1; objective o2; }",
        "validateCaseUsageOnlyOneObjective",
    );
}

#[test]
fn subject_position_and_flow_end_cardinality() {
    assert_one_error(
        "requirement def R { in attribute input; subject s; }",
        "validateRequirementDefinitionSubjectParameterPosition",
    );
    assert!(
        check_sysml("requirement def R { attribute note; subject s; in attribute input; }")
            .is_empty()
    );
    assert_one_error(
        "case c { actor a; subject s; }",
        "validateCaseUsageSubjectParameterPosition",
    );
    assert_one_error(
        "flow def F { end item a; end item b; end item c; }",
        "validateFlowDefinitionFlowEnds",
    );
}

/// Referential warnings for one source (no library).
fn model_warnings(src: &str) -> Vec<String> {
    let mut model = Model::new();
    model.add_source("t.sysml", src);
    assert!(!model.has_errors(), "test source must parse cleanly");
    validate_model(&model)
        .into_iter()
        .map(|(_, d)| d.message)
        .collect()
}

#[test]
fn recursive_rollup_chain_member_resolves() {
    // Apollo-study regression: the chain-step member is the
    // feature being defined — the value-expression self-exclusion must not
    // block it (it resolves in the chain target's scope, over children).
    // (No `sum(…)` here: intrinsic *names* still need an import to satisfy
    // the referential check, and `model_warnings` runs without the library.)
    assert!(
        model_warnings(
            "package P {
             part def M {
                 attribute mass = 1;
                 part subcomponents : M;
                 attribute totalMass = mass + subcomponents.totalMass;
             }
         }"
        )
        .is_empty()
    );
}

#[test]
fn forward_chain_redefinition_shadowing_resolves() {
    // Specialization outcomes are resolved before ordinary value refs, so a
    // chain written before the declarations it reaches serializes exactly
    // like the same chain written afterward.
    assert!(
        model_warnings(
            "package P {
                attribute early = t.c.d;
                part def L { attribute d; }
                part def N :> L { attribute :>> d = 5; }
                part def T { part c : L; }
                part t : T { part :>> c : N; }
                attribute late = t.c.d;
            }"
        )
        .is_empty()
    );
}

#[test]
fn semantic_metadata_base_type_binds() {
    // SysML semantic metadata (KerML 9.2 metaobject semantics): a usage
    // annotated with a SemanticMetadata subtype implicitly specializes the
    // metadata's `baseType` value, so the base's members resolve in the
    // annotated usage's body (the Drone.sysml pattern — `#mec part
    // battery { :>> mass … }` subsets `mechanicalObjects`). Both the `#M`
    // prefix and the about-less `@M;` body spellings annotate the usage.
    // (`Metaobjects` is user-defined here: `model_warnings` runs without
    // the library, and the `$::`-rooted lookup finds it all the same.)
    let base = "package Metaobjects { metadata def SemanticMetadata { attribute baseType; } }
         package P {
             metadata def U;
             part def M { attribute mass; }
             abstract part mechanicalObjects : M;
             metadata def Mec :> Metaobjects::SemanticMetadata {
                 :>> baseType = mechanicalObjects meta U;
             }
             #Mec part battery { attribute :>> mass = 2; }
             part engine { @Mec; attribute :>> mass = 3; }
         }";
    assert!(model_warnings(base).is_empty());
    // A metadata def that does *not* conform to SemanticMetadata binds
    // nothing — the redefinition target stays unresolved.
    let msgs = model_warnings(
        "package Metaobjects { metadata def SemanticMetadata { attribute baseType; } }
         package P {
             metadata def U;
             part def M { attribute mass; }
             abstract part mechanicalObjects : M;
             metadata def NotSem { attribute baseType = mechanicalObjects meta U; }
             #NotSem part battery { attribute :>> mass = 2; }
         }",
    );
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("unresolved reference `mass`"));
}

#[test]
fn referential_unresolved_reference() {
    let msgs = model_warnings("package P { part def V; part x : Vehicel; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("unresolved reference `Vehicel`"));
    assert!(model_warnings("package P { part def V; part x : V; }").is_empty());
}

/// A `doc`, `comment`, `rep`, or `dependency` written with an
/// identification is an owned member of its namespace under that name,
/// so an `about` clause reaches it by local name, short name, or
/// qualified name — exactly like a type or feature member.
#[test]
fn referential_named_annotating_elements() {
    assert!(
        model_warnings(
            "package P {
                 metadata def Note;
                 part def V {
                     doc <vd> vDoc /* the definition */
                     comment named /* a named comment */
                     rep inOCL language \"ocl\" /* self.x > 0 */
                     comment about named /* local name */
                     comment about vd /* short name */
                     comment about inOCL /* textual representation */
                     @Note about vDoc;
                 }
                 comment about V::vDoc /* qualified */
                 comment about P::V::named /* fully qualified */
                 dependency vDep from V to Note;
                 comment about vDep /* dependency */
                 @Note about P::vDep;
             }"
        )
        .is_empty()
    );
    // An annotating element owns no members, so nothing resolves through it.
    let msgs = model_warnings(
        "package P { part def V { doc vDoc /* … */ } comment about V::vDoc::x /* */ }",
    );
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("unresolved reference `V::vDoc::x`"));
}

#[test]
fn referential_alias_target() {
    let msgs = model_warnings("package P { part def V; alias W for Vehicel; }");
    // The alias-specific finding subsumes the generic unresolved one.
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("alias target `Vehicel` does not resolve"));
    assert!(model_warnings("package P { part def V; alias W for V; }").is_empty());
}

#[test]
fn referential_import_cycle() {
    let msgs = model_warnings(
        "package P {
             package A { public import B::*; part def X; }
             package B { public import A::*; part def Y; }
         }",
    );
    assert_eq!(msgs.len(), 2, "{msgs:#?}");
    assert!(msgs.iter().all(|m| m.contains("circular namespace import")));
    // Importing an ancestor namespace is NOT a cycle.
    assert!(
        model_warnings(
            "package P { part def X; package Inner { private import P::*; part y : X; } }"
        )
        .is_empty()
    );
    // Resolution still works through the cycle (both defs visible).
    assert!(
        model_warnings(
            "package P {
             package A { public import B::*; part def X; }
             package B { public import A::*; part def Y; }
             part x : A::Y;
             part y : B::X;
         }"
        )
        .iter()
        .all(|m| !m.contains("unresolved"))
    );
}

#[test]
fn expose_makes_members_referencable() {
    // `expose` is an import for resolution (ViewTest.sysml pattern).
    assert!(
        model_warnings(
            "package M {
             package P { part def D; part p1 : D; }
             view v { expose P::*; alias vp1 for p1; }
         }"
        )
        .is_empty()
    );
}

/// Corpus ratchet: referential findings over the full corpus + library.
/// Visibility enforcement exposes references that previously leaked
/// through private memberships, and ambiguity is now counted separately
/// instead of binding the first declaration/import. Improvements should
/// lower these numbers; semantic corrections require a deliberate update.
///
/// Ambiguity rose 47 -> 48 on the pinned corpus, and the added finding
/// is ours, not the corpus's: correcting the individual-analysis
/// example's typing made a second inheritance path visible, and we do
/// not yet collapse a usage's re-declared feature onto the identically
/// named feature it inherits from its type (implicit redefinition by
/// name). Minimal shape — the reference to `y` inside the nested
/// redefinition is reported ambiguous:
///
/// ```text
/// action def A { out y : V; }
/// analysis def An { action a : A { out y : V; } }   // implicit :>> y
/// ```
///
/// (95, 48, 2, 2) -> (66, 25, 2, 2) when inherited-member merges gained
/// *explicit*-redefinition shadowing: a candidate that
/// transitively redefines another candidate wins instead of the pair
/// reading as ambiguous, so diamonds like a subject redefinition seen
/// beside the definition's original subject resolve — and the chain
/// members reached through the formerly ambiguous features resolve
/// with them (the 29-unresolved drop is entirely that cascade).
///
/// -> (66, 24, 2, 2) with *implicit* redefinition by name (the shape
/// documented above): a usage owned by a type that strictly
/// specializes another candidate's owning type shadows the same-named
/// inherited feature without a spelled `:>>`. The remaining ambiguities
/// are recursive-import multi-hits (several same-named declarations in
/// unrelated containers made visible by `import ::**`) — genuine
/// indistinguishability, not inheritance diamonds.
///
/// A user root declaration named like a standard-library root is silently
/// bypassed by resolution: root lookups keep the library declaration (the
/// two metaclasses do not overlap, so the earlier candidate stands), and
/// every qualified reference through the name lands in the library. The
/// referential check reports the collision at the user declaration's
/// name; resolution itself is unchanged.
#[test]
fn referential_root_shadows_library_root() {
    const LIB: &str = "standard library package Requirements { requirement def Base; }";
    let shadowing = |user: &str| {
        let mut model = Model::new();
        model.add_library_source("MiniLib.sysml", LIB);
        model.add_source("t.sysml", user);
        assert!(!model.has_errors(), "test source must parse cleanly");
        model
    };

    let src = "package Requirements {\n    requirement def Speed;\n}\npackage Uses {\n    \
               requirement s : Requirements::Speed;\n}\n";
    let model = shadowing(src);
    let diags = validate_model(&model);
    let msgs: Vec<&str> = diags.iter().map(|(_, d)| d.message.as_str()).collect();
    assert_eq!(
        msgs,
        [
            "root package `Requirements` shadows the standard library package `Requirements`; \
             references resolve to the library",
            "unresolved reference `Requirements::Speed`",
        ],
        "{msgs:#?}"
    );
    // Attributed to the user unit, at the declared name.
    let (unit, d) = &diags[0];
    assert_eq!(*unit, 1);
    assert_eq!(
        &src[d.span.start as usize..d.span.end as usize],
        "Requirements"
    );
    // Resolution behavior is unchanged: the root name reaches the library.
    let mut r = sysmlv2_parser::json::ResolvedModel::build(&model);
    let pkg = r.resolve_qualified("Requirements").expect("resolves");
    assert!(r.is_library_element(pkg));
    assert!(r.resolve_qualified("Requirements::Speed").is_none());
    assert!(r.resolve_qualified("Requirements::Base").is_some());

    // Any root declaration kind collides, not only packages.
    let msgs = validate_model(&shadowing("part def Requirements;"))
        .into_iter()
        .map(|(_, d)| d.message)
        .collect::<Vec<_>>();
    assert_eq!(
        msgs,
        [
            "root declaration `Requirements` shadows the standard library package \
             `Requirements`; references resolve to the library"
        ],
        "{msgs:#?}"
    );

    // A same-kind user root makes the name ambiguous instead — the
    // finding says so, alongside the per-reference ambiguity findings.
    let msgs = validate_model(&shadowing(
        "library package Requirements { requirement def Speed; }\n\
         package Uses { requirement s : Requirements::Speed; }\n",
    ))
    .into_iter()
    .map(|(_, d)| d.message)
    .collect::<Vec<_>>();
    assert_eq!(msgs.len(), 2, "{msgs:#?}");
    assert_eq!(
        msgs[0],
        "root package `Requirements` shadows the standard library package `Requirements`; \
         references to the name are ambiguous"
    );
    assert!(msgs[1].starts_with("ambiguous reference"), "{msgs:#?}");

    // Nested packages and differently named roots never collide.
    assert!(
        validate_model(&shadowing(
            "package Reqs { package Requirements { requirement def Speed; } \
             requirement s : Requirements::Speed; }"
        ))
        .is_empty()
    );
    // Without a library there is nothing to shadow.
    assert!(model_warnings("package Requirements { requirement def Speed; }").is_empty());
}

/// -> (65, 24, 2, 2) after trigger-bearing accept payload names stopped
/// being lowered as unresolved type references.
/// -> (63, 24, 2, 2) once named documentation and comment elements
/// became members their namespace binds, so `comment about cmt` reaches
/// a `comment cmt /* … */` sibling.
#[test]
fn corpus_referential_ratchet() {
    let root = sysmlv2_testkit::corpus_root();
    let mut model = Model::new();
    model
        .load_library_dir(&root.join("sysml.library"))
        .expect("library");
    let files = sysmlv2_testkit::user_files();
    for f in &files {
        let src = fs::read_to_string(f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let diags = validate_model(&model);
    let unresolved = diags
        .iter()
        .filter(|(_, d)| d.message.starts_with("unresolved"))
        .count();
    let aliases = diags
        .iter()
        .filter(|(_, d)| d.message.starts_with("alias"))
        .count();
    let ambiguous = diags
        .iter()
        .filter(|(_, d)| d.message.starts_with("ambiguous"))
        .count();
    let cycles = diags
        .iter()
        .filter(|(_, d)| d.message.starts_with("circular"))
        .count();
    assert_eq!(
        (unresolved, ambiguous, aliases, cycles),
        (63, 24, 2, 2),
        "referential ratchet moved — improvements should only lower these"
    );
}

/// Semantic-constraint findings for one source (no library).
fn sem_warnings(src: &str) -> Vec<String> {
    let mut model = Model::new();
    model.add_source("t.sysml", src);
    assert!(!model.has_errors(), "test source must parse cleanly");
    sysmlv2_parser::check::validate_semantics(&model)
        .into_iter()
        .map(|(_, d)| format!("{:?}: {}", d.severity, d.message))
        .collect()
}

#[test]
fn semantic_multiplicity_bounds() {
    let msgs = sem_warnings("package P { part def T; part x : T[2..1]; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("lower bound 2 exceeds upper bound 1"));
    // Negative bounds are not grammatical as literals — they arrive via
    // evaluated references.
    let msgs = sem_warnings("package P { attribute n = -1; part def T; part x : T[n]; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("negative"));
    // Fine: ranges, star, symbolic bounds (undecided — no diagnostic).
    assert!(sem_warnings("package P { part def T; part x : T[0..*]; }").is_empty());
    assert!(sem_warnings("package P { attribute n; part def T; part x : T[n]; }").is_empty());
    // Evaluated bounds work through feature references.
    let msgs = sem_warnings("package P { attribute n = 3; part def T; part x : T[n..2]; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
}

#[test]
fn multiplicity_bounds_require_natural_values() {
    for bound in ["\"two\"", "true", "1.5", "*..2"] {
        let findings = sem_warnings(&format!("part p[{bound}];"));
        assert!(
            findings.iter().any(|m| m.contains("Natural number")),
            "{bound}: {findings:?}"
        );
    }
    for bound in ["0..*", "2"] {
        assert!(
            sem_warnings(&format!("part p[{bound}];")).is_empty(),
            "{bound}"
        );
    }
    assert!(!sem_warnings("attribute n = (1, 2); part p[n];").is_empty());
    assert!(sem_warnings("attribute n = 4 / 2; part p[n];").is_empty());
}

#[test]
fn usage_typing_respects_metaclass_inheritance_and_single_type_rules() {
    for usage in [
        "attribute",
        "port",
        "action",
        "state",
        "calc",
        "constraint",
        "requirement",
        "analysis",
        "verification",
        "use case",
        "view",
        "rendering",
    ] {
        let findings = sem_warnings(&format!("part def D; {usage} x : D;"));
        assert!(
            findings.iter().any(|m| m.contains("must be typed by")),
            "{usage}: {findings:?}"
        );
    }
    assert!(!sem_warnings("attribute def D; occurrence x : D;").is_empty());
    assert!(sem_warnings("interface def I; connection x : I;").is_empty());
    assert!(sem_warnings("requirement def R; constraint x : R;").is_empty());
    assert!(sem_warnings("calc def C; action x : C;").is_empty());
    assert!(sem_warnings("metadata def M; item x : M;").is_empty());
    assert!(
        sem_warnings("calc def C { in part x : ScalarValues::Real; return : ScalarValues::Real; }")
            .is_empty()
    );
    for kind in [
        "calc",
        "constraint",
        "requirement",
        "case",
        "analysis",
        "verification",
        "use case",
        "view",
        "viewpoint",
        "rendering",
        "enum",
    ] {
        let findings = sem_warnings(&format!("{kind} def A; {kind} def B; {kind} x : A, B;"));
        assert!(
            findings
                .iter()
                .any(|m| m.contains("one non-redundant type")),
            "{kind}: {findings:?}"
        );
        let findings = sem_warnings(&format!(
            "{kind} def A; {kind} def B :> A; {kind} x : B, A;"
        ));
        if kind == "enum" {
            assert!(
                findings
                    .iter()
                    .any(|m| m.contains("validateDefinitionVariationSpecialization")),
                "{findings:?}"
            );
        } else {
            assert!(findings.is_empty(), "redundant {kind}: {findings:?}");
        }
    }
}

#[test]
fn subsetting_cannot_widen_an_explicit_upper_bound() {
    let declaration = "part def A { part x[2..3]; }";
    let bad = sem_warnings(&format!(
        "{declaration} part def B :> A {{ part y[0..4] :> x; }}"
    ));
    assert_eq!(bad.len(), 1, "{bad:?}");
    assert!(bad[0].contains("subsetting multiplicity upper bound"));
    let good = sem_warnings(&format!(
        "{declaration} part def B :> A {{ part y[0..1] :> x; }}"
    ));
    assert!(good.is_empty(), "a subset may have fewer values: {good:?}");
}

#[test]
fn invocation_bindings_are_checked_by_name_and_position() {
    let calc = "calc def F { in a; in b = 2; a + b }";
    for (args, expected) in [
        ("a = 1, a = 2", "more than once"),
        ("1, a = 2", "more than once"),
        ("typo = 1", "unknown parameter"),
    ] {
        let findings = sem_warnings(&format!("{calc} attribute result = F({args});"));
        assert!(
            findings.iter().any(|m| m.contains(expected)),
            "{args}: {findings:?}"
        );
    }
    for args in ["a = 1", "b = 3, a = 1", "1", "1, b = 3"] {
        assert!(
            sem_warnings(&format!("{calc} attribute result = F({args});")).is_empty(),
            "{args}"
        );
    }
}

#[test]
fn arithmetic_dimensions_are_checked_even_when_parameters_are_unbound() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    model.add_source(
        "dimensions.sysml",
        r#"
        package Dimensions {
            private import SI::*;
            calc bad {
                in v :> ISQ::speed; in mu :> ISQ::force; in r :> ISQ::length;
                return result = v ** 2 + 2 * mu / r;
            }
            calc good {
                in v :> ISQ::speed; in a :> ISQ::acceleration; in r :> ISQ::length;
                return result = v ** 2 + 2 * a * r;
            }
            attribute badValue = 1 [m] + 1 [s];
            attribute zero = 1 [m] + 0;
            attribute unknown;
            attribute open = unknown + 1 [m];
        }
    "#,
    );
    assert!(!model.has_errors());
    let diagnostics = sysmlv2_parser::check::validate_semantics(&model);
    let messages: Vec<_> = diagnostics
        .iter()
        .map(|(_, d)| d.message.as_str())
        .collect();
    assert_eq!(messages.len(), 2, "{messages:#?}");
    assert!(
        messages
            .iter()
            .all(|m| m.contains("incompatible quantity dimensions"))
    );
}

#[test]
fn semantic_self_and_circular_specialization() {
    let msgs = sem_warnings("package P { part def A :> A; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("cannot specialize itself"));
    let msgs = sem_warnings("package P { part def A :> B; part def B :> A; }");
    assert_eq!(msgs.len(), 2, "{msgs:#?}");
    assert!(msgs.iter().all(|m| m.contains("circular specialization")));
    // A normal chain is fine.
    assert!(sem_warnings("package P { part def A; part def B :> A; part def C :> B; }").is_empty());
    // Feature subsetting of an inherited same-named feature stays exempt.
    assert!(
        sem_warnings("package P { part def V { part axle; } part v : V { part axle :> axle; } }")
            .is_empty()
    );
}

#[test]
fn semantic_duplicate_specializations() {
    let msgs = sem_warnings("package P { part def T; part x : T, T; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("Warning") && msgs[0].contains("duplicate specialization"));
    let msgs = sem_warnings("package P { part def S; part def D :> S, S; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    // Distinct targets are fine.
    assert!(sem_warnings("package P { part def A; part def B; part x : A, B; }").is_empty());
}

/// Corpus gate: every finding must be an adjudicated defect in the input,
/// rather than an implementation limitation or an unreviewed false positive.
#[test]
fn corpus_semantic_constraints_clean() {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    for f in sysmlv2_testkit::user_files() {
        let src = fs::read_to_string(&f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let diags = sysmlv2_parser::check::validate_semantics(&model);
    // The single long-standing exception here was a
    // corpus defect in `AnalysisIndividualExample.sysml`, where the
    // redefinition typed the wrong individual (the *analysis* def
    // rather than the action def declared for it); the pinned corpus
    // corrects the typing. Dimensional inference reveals two independent
    // defects, also reported by OpenSysML at d7d432ff4:
    // - Total Temperature declares V : VolumeValue and Cp : DimensionOneValue,
    //   then adds V^2/(2*Cp) (L^6) to T_static (temperature).
    // - The wheel expression adds 22/2*25.4 (dimensionless) to 110[mm]; the
    //   intended whole sum needs parentheses before its unit annotation.
    let msgs: Vec<String> = diags
        .iter()
        .map(|(u, d)| format!("{} — {}", model.units()[*u].name, d.message))
        .collect();
    assert_eq!(
        msgs,
        [
            "Turbojet Stage Analysis.sysml — expression combines incompatible quantity dimensions `L^6` and `Θ`",
            "VehicleGeometryAndCoordinateFrames.sysml — expression combines incompatible quantity dimensions `1` and `L`",
        ],
        "unexpected semantic findings on the corpus"
    );
}

/// Constraint verdicts for one source (no library).
fn verdicts(src: &str) -> Vec<(Option<String>, sysmlv2_parser::check::ConstraintVerdict)> {
    let mut model = Model::new();
    model.add_source("t.sysml", src);
    assert!(!model.has_errors(), "test source must parse cleanly");
    sysmlv2_parser::check::check_constraints(&model)
        .into_iter()
        .map(|c| (c.name, c.verdict))
        .collect()
}

#[test]
fn constraint_verdicts() {
    use sysmlv2_parser::check::ConstraintVerdict::*;
    let vs = verdicts(
        "package P {
             attribute mass = 1200;
             attribute maxMass = 2000;
             assert constraint ok { mass <= maxMass }
             assert constraint bad { mass > 5000 }
             assert not constraint inverted { mass > maxMass }
             constraint open { mass <= budget }
         }",
    );
    assert_eq!(vs.len(), 4, "{vs:#?}");
    assert_eq!(vs[0], (Some("ok".into()), Satisfied));
    assert_eq!(vs[1], (Some("bad".into()), Violated));
    // `assert not` inverts the expected value: mass > maxMass is false → satisfied.
    assert_eq!(vs[2], (Some("inverted".into()), Satisfied));
    assert!(matches!(&vs[3].1, Undecided(why) if why.contains("budget")));
}

#[test]
fn unbound_feature_comparisons_are_undecided() {
    use sysmlv2_parser::check::ConstraintVerdict::*;
    // `engine` is unbound: equality against a variant is unknown, not false.
    let vs = verdicts(
        "package P {
             variation part def Choices { variant part small; variant part big; }
             part engine : Choices[1];
             assert constraint pick { engine == Choices::small }
         }",
    );
    assert_eq!(vs.len(), 1, "{vs:#?}");
    assert!(matches!(&vs[0].1, Undecided(why) if why.contains("unbound")));
    // Enum literals on both sides stay decidable.
    let vs = verdicts(
        "package P {
             enum def L { low; high; }
             attribute chosen = L::high;
             assert constraint c { chosen == L::high }
         }",
    );
    assert_eq!(vs[0].1, Satisfied, "{vs:#?}");
}

/// A member read *through an unbound parameter* — a requirement's
/// `subject`, a calc parameter — is not the type's default: the default
/// belongs to the type and the argument bound later may override it, so
/// a definition-level constraint over the subject stays undecided
/// instead of accusing the type's defaults. A value the declaration
/// *fixes* to a literal holds for every argument and still decides,
/// and an ordinary usage still reads the defaults it inherits.
#[test]
fn defaults_read_through_an_unbound_subject_are_undecided() {
    use sysmlv2_parser::check::ConstraintVerdict::*;
    let vs = verdicts(
        "package P {
             part def Cartridge { attribute micron default = 5; }
             part def Filter {
                 attribute ratedHours default = 40;
                 attribute portCount = 3;
                 part cartridge : Cartridge;
             }
             requirement def FitForService {
                 subject unit : Filter;
                 require constraint fromDefault { unit.ratedHours >= 250 }
                 require constraint fromFixed { unit.portCount == 6 }
                 require constraint throughChain { unit.cartridge.micron <= 1 }
             }
             part installed : Filter;
             assert constraint onAUsage { installed.ratedHours == 40 }
         }",
    );
    let by_name = |n: &str| {
        vs.iter()
            .find(|(name, _)| name.as_deref() == Some(n))
            .unwrap_or_else(|| panic!("no constraint `{n}` in {vs:#?}"))
            .1
            .clone()
    };
    assert!(matches!(by_name("fromDefault"), Undecided(_)), "{vs:#?}");
    assert!(matches!(by_name("throughChain"), Undecided(_)), "{vs:#?}");
    assert_eq!(by_name("fromFixed"), Violated, "{vs:#?}");
    assert_eq!(by_name("onAUsage"), Satisfied, "{vs:#?}");
}

#[test]
fn unknown_receivers_do_not_commit_to_type_defaults() {
    use sysmlv2_parser::check::ConstraintVerdict::*;
    let vs = verdicts(
        "package P {
            part def Choice { attribute enabled default = false; }
            part installed : Choice;
            attribute externalDefault default = true;
            calc def Identity { in x; return y = x; }
            calc def Read { in x : Choice; return y = x.enabled; }
            part def Device {
                attribute ready default = false;
                attribute intermediate = ready;
                attribute enabled = intermediate;
                attribute external = installed.enabled;
                attribute externalScalar = externalDefault;
                attribute fixed = true;
                calc def LocalDefault { in x default = true; return y = x; }
                calc def ReadReady { return y = ready; }
                attribute localDefault = LocalDefault();
                attribute localUnknown = ReadReady();
                part choice : Choice;
                part concrete : Choice = installed;
            }
            requirement def Eligibility {
                subject unit : Device;
                ref part requested : Choice;
                ref part aliasUnit : Device = unit;
                require constraint referenceDefault { requested.enabled }
                require constraint fixedFormula { unit.enabled }
                require constraint aliasFormula { aliasUnit.enabled }
                require constraint conditionalDefault {
                    (if true ? requested else installed).enabled
                }
                require constraint returnedReference { Identity(requested).enabled }
                require constraint argumentReference { Read(requested) }
                require constraint nestedDefault { unit.choice.enabled }
                require constraint nestedAlias { Identity(unit.choice).enabled }
                require constraint fixedLiteral { unit.fixed }
                require constraint localDefault { unit.localDefault }
                require constraint localUnknown { unit.localUnknown }
                require constraint concreteMember { not unit.concrete.enabled }
                require constraint unrelatedReceiver { not unit.external }
                require constraint unrelatedScalar { unit.externalScalar }
                require constraint concreteConditional {
                    not (if false ? requested else installed).enabled
                }
                require constraint concreteArgument { not Read(installed) }
            }
            calc def Input {
                in requested : Choice;
                return result = requested.enabled;
                assert constraint inputDefault { requested.enabled }
            }
        }",
    );
    let unknown = [
        "referenceDefault",
        "fixedFormula",
        "aliasFormula",
        "conditionalDefault",
        "returnedReference",
        "argumentReference",
        "nestedDefault",
        "nestedAlias",
        "inputDefault",
        "localUnknown",
    ];
    assert_eq!(vs.len(), 17, "{vs:#?}");
    for (name, verdict) in &vs {
        if unknown.contains(&name.as_deref().unwrap()) {
            assert!(
                matches!(verdict, Undecided(reason) if reason.contains("indeterminate")),
                "{name:?}: {verdict:?}"
            );
        } else {
            assert_eq!(*verdict, Satisfied, "{name:?}");
        }
    }
}

#[test]
fn unknown_receiver_methods_follow_redefined_defaults() {
    use sysmlv2_parser::check::ConstraintVerdict::*;
    for declaration in ["attribute :>> ready", "attribute ready"] {
        for value in ["default = true", "= true"] {
            let vs = verdicts(&format!(
                "package P {{
                part def Base {{
                    attribute ready default = false;
                    calc def Read {{ attribute local = ready; return result = local; }}
                    attribute enabled = Read();
                }}
                part def Specialized :> Base {{ {declaration} {value}; }}
                requirement def R {{
                    subject unit : Specialized;
                    require constraint direct {{ unit.ready }}
                    require constraint method {{ unit.enabled }}
                }}
            }}"
            ));
            assert_eq!(vs.len(), 2, "{vs:?}");
            for (_, verdict) in vs {
                if value.starts_with("default") {
                    assert!(
                        matches!(verdict, Undecided(reason) if reason.contains("indeterminate")),
                        "{value}"
                    );
                } else {
                    assert_eq!(verdict, Satisfied, "{value}");
                }
            }
        }
    }
}

#[test]
fn unknown_receivers_do_not_taint_imported_concrete_values() {
    use sysmlv2_parser::check::ConstraintVerdict::*;
    let vs = verdicts(
        "package Globals {
            attribute flag default = true;
            part def Child { attribute flag default = true; }
            part installed : Child;
        }
        package P {
            part def Device {
                private import Globals::*;
                attribute scalar = flag;
                attribute nested = installed.flag;
            }
            requirement def R {
                subject unit : Device;
                require constraint scalar { unit.scalar }
                require constraint nested { unit.nested }
            }
        }",
    );
    assert_eq!(vs.len(), 2, "{vs:?}");
    for (_, verdict) in vs {
        assert_eq!(verdict, Satisfied);
    }
}

/// Corpus ratchet for constraint verdicts: a conforming corpus must have
/// **zero violated**; the satisfied/undecided split moves only through
/// deliberate evaluator improvements.
#[test]
fn corpus_constraint_verdicts_ratchet() {
    use sysmlv2_parser::check::ConstraintVerdict::*;
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .expect("library");
    for f in sysmlv2_testkit::user_files() {
        let src = fs::read_to_string(&f).unwrap();
        model.add_source(f.file_name().unwrap().to_string_lossy().into_owned(), &src);
    }
    let checks = sysmlv2_parser::check::check_constraints(&model);
    let count = |v: fn(&sysmlv2_parser::check::ConstraintVerdict) -> bool| {
        checks.iter().filter(|c| v(&c.verdict)).count()
    };
    let sat = count(|v| matches!(v, Satisfied));
    let vio = count(|v| matches!(v, Violated));
    let und = count(|v| matches!(v, Undecided(_)));
    assert_eq!(
        (sat, vio, und),
        // 80 → 90 when asserted constraints with *inherited* bodies
        // (`assert c : Def;`) gained verdicts; 90 → 116 when
        // satisfaction claims (`satisfy R by x;`) began expanding to
        // subject-bound verdicts — all 26 corpus expansions enter
        // undecided (their remaining parameters are unbound); the
        // evaluator/solver may promote them. Satisfied 7 → 4 when
        // unbound-feature cardinality stopped fabricating:
        // the three lost verdicts were `(1..size(xs)-1)->forAll` bodies
        // over unbound `[0..*]` collections, where the placeholder's
        // fabricated size of 1 emptied the range and made the forAll
        // vacuously true — never-actually-checked constraints now read
        // honestly undecided.
        (4, 0, 119),
        "constraint-verdict ratchet moved — violated must stay 0;          satisfied should only grow via evaluator improvements"
    );
}

#[test]
fn nested_contexts_are_tracked() {
    // The action body nested inside a state's `do` is a real action body.
    assert!(check_sysml("state def S { do action { send sig() to x; } }").is_empty());
    // A part nested inside an action body reverts to definition-body rules.
    assert_one_error(
        "action def A { part p { first start; } }",
        "initial-node member (`first`) is not allowed in a definition or usage body",
    );
    // Expression bodies are calculation bodies.
    assert!(check_sysml("part def P { attribute x = list->select { in i; i > 0 }; }").is_empty());
}

/// Invocation arity: fewer positional arguments than declared `in`
/// parameters is a warning — unless the unbound tail carries defaults,
/// the call uses named arguments, or the spelling is zero-argument.
#[test]
fn semantic_metadata_typing() {
    // All three spellings flag a non-metaclass type (errors).
    let msgs = sem_warnings("package P { part def D; #D part def X; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("metadata must be typed by a metadata definition"));
    assert!(msgs[0].contains("`D` is a PartDefinition"));
    let msgs = sem_warnings("package P { attribute def D; part y { @D; } }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    let msgs = sem_warnings("package P { part def D; part x; metadata m : D about x; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    // Metadata definitions (SysML) are fine in every spelling.
    assert!(
        sem_warnings(
            "package P { metadata def M; #M part def X; part y { @M; } metadata m : M about y; }"
        )
        .is_empty()
    );
    // KerML metaclasses are fine too.
    let mut model = Model::new();
    model.add_source(
        "t.kerml",
        "package P { metaclass M; struct S { metadata m : M; } }",
    );
    assert!(!model.has_errors(), "test source must parse cleanly");
    assert!(sysmlv2_parser::check::validate_semantics(&model).is_empty());
    // Unresolved metadata types stay out of semantic findings (referential
    // checks own those).
    assert!(sem_warnings("package P { #Missing::M part def X; }").is_empty());
}

#[test]
fn semantic_invocation_arity() {
    let calc = "calc def F { in a; in b; in c; a + b + c }";
    // Under-application: two of three parameters bound.
    let msgs = sem_warnings(&format!("package P {{ {calc} attribute x = F(1, 2); }}"));
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("binds 2 of its 3 parameters"), "{msgs:#?}");
    assert!(msgs[0].contains("`c` never bound"), "{msgs:#?}");
    // Exact application is clean.
    assert!(sem_warnings(&format!("package P {{ {calc} attribute x = F(1, 2, 3); }}")).is_empty());
    // A defaulted tail is clean.
    let defaulted = "calc def G { in a; in b = 10; a + b }";
    assert!(sem_warnings(&format!("package P {{ {defaulted} attribute x = G(1); }}")).is_empty());
    // Named and empty calls must not silently leave required inputs unbound.
    for args in ["a = 1, b = 2", ""] {
        let msgs = sem_warnings(&format!("package P {{ {calc} attribute x = F({args}); }}"));
        assert_eq!(msgs.len(), 1, "{msgs:#?}");
        assert!(msgs[0].contains("never bound"));
    }
    // Nested call sites are found.
    let msgs = sem_warnings(&format!(
        "package P {{ {calc} attribute x = 1 + F(1, 2) * 3; }}"
    ));
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
}

/// Redefinition type-compatibility: a redefining feature
/// whose declared types cannot conform to the redefined feature's
/// user-owned type is flagged; conforming redefinitions, untyped
/// redefinitions, and subsetting (legal via multiple classification)
/// stay silent.
#[test]
fn semantic_redefinition_type_compatibility() {
    let base = "part def A; part def B :> A; part def C;
                part def V { part x : A; }";
    // Redefining with a conforming (sub)type is fine.
    assert!(
        sem_warnings(&format!(
            "package P {{ {base} part def W :> V {{ part :>> x : B; }} }}"
        ))
        .is_empty()
    );
    // Redefining with an unrelated type is flagged.
    let msgs = sem_warnings(&format!(
        "package P {{ {base} part def W :> V {{ part :>> x : C; }} }}"
    ));
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("redefines `x`"), "{msgs:#?}");
    assert!(msgs[0].contains("`A`"), "{msgs:#?}");
    // Untyped redefinition stays silent.
    assert!(
        sem_warnings(&format!(
            "package P {{ {base} part def W :> V {{ part :>> x = null; }} }}"
        ))
        .is_empty()
    );
    // Subsetting across unrelated types is legal (multiple
    // classification) — the official Model Library Example pattern.
    assert!(
        sem_warnings("package P { part def A; part def C; part a : A[*]; part c : C[*] :> a; }")
            .is_empty()
    );
}

/// Redefinition multiplicity conformance: an explicit
/// redefining range outside the redefined feature's explicit range is
/// flagged; ranges within (including `[n]` inside `[1..*]`), symbolic
/// bounds, and missing declarations stay silent.
#[test]
fn semantic_redefinition_multiplicity_conformance() {
    let base = "part def E; part def V { part x : E[1..4]; }";
    // Within the range: fine.
    assert!(
        sem_warnings(&format!(
            "package P {{ {base} part def W :> V {{ part :>> x : E[2]; }} }}"
        ))
        .is_empty()
    );
    // Below the lower bound: flagged.
    let msgs = sem_warnings(&format!(
        "package P {{ {base} part def W :> V {{ part :>> x : E[0..2]; }} }}"
    ));
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("[0..2] is not within"), "{msgs:#?}");
    // Above the upper bound: flagged.
    let msgs = sem_warnings(&format!(
        "package P {{ {base} part def W :> V {{ part :>> x : E[5]; }} }}"
    ));
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    // `[n]` within `[1..*]` (the Apollo engines pattern): fine.
    assert!(
        sem_warnings(
            "package P { part def E; part def S { part e : E[1..*]; }
                     part def T :> S { part :>> e : E[5]; } }"
        )
        .is_empty()
    );
    // No explicit multiplicity on either side: silent.
    assert!(
        sem_warnings(&format!(
            "package P {{ {base} part def W :> V {{ part :>> x : E; }} }}"
        ))
        .is_empty()
    );
}

/// Feature-value scalar conformance (narrowed to kind-level
/// provability): cross-partition scalar values and non-integral
/// rationals against `Integer`-conforming types are flagged; the
/// official corpus's sibling-subtype bindings (`Rational` vs a `Real`
/// subtype, ISO-8601 strings vs a `String` subtype) stay silent —
/// they are legal under KerML multiple classification.
#[test]
fn semantic_feature_value_scalar_conformance() {
    // Non-integral rational vs an Integer-conforming type: flagged.
    let msgs = sem_warnings("package P { attribute def Integer; attribute w : Integer = 245.5; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("not an integer"), "{msgs:#?}");
    // Cross-partition: a String value vs a numeric type, and a numeric
    // value vs a String type.
    let msgs = sem_warnings("package P { attribute def Real; attribute r : Real = \"fast\"; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("a String"), "{msgs:#?}");
    let msgs = sem_warnings("package P { attribute def String; attribute s : String = 42; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("a number"), "{msgs:#?}");
    // A Boolean value vs a numeric type.
    let msgs = sem_warnings("package P { attribute def Integer; attribute b : Integer = true; }");
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("a Boolean"), "{msgs:#?}");
    // An untyped redefining feature borrows the target's declared type.
    let msgs = sem_warnings(
        "package P { attribute def Integer;
                     part def V { attribute w : Integer; }
                     part v : V { attribute :>> w = 2.5; } }",
    );
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("not an integer"), "{msgs:#?}");
    // The corpus's enum-restriction idiom (EnumerationTest.sysml): a
    // rational literal against a sibling subtype of `Real` may conform
    // through the value's extent — silent.
    assert!(
        sem_warnings(
            "package P { attribute def Real; attribute def Size :> Real;
                     enum def SizeChoice :> Size { = 60.0; = 70.0; }
                     enum size : SizeChoice = 60.0; }"
        )
        .is_empty()
    );
    // Integral rationals are admitted by Integer-conforming types.
    assert!(
        sem_warnings("package P { attribute def Integer; attribute w : Integer = 18.0; }")
            .is_empty()
    );
    // Unclassifiable declared types and unevaluable values: silent.
    assert!(sem_warnings("package P { part def T; part p : T = 5; }").is_empty());
    assert!(
        sem_warnings(
            "package P { attribute def Integer; attribute u;
                     attribute w : Integer = u + 1; }"
        )
        .is_empty()
    );
}

#[test]
fn semantic_connector_end_featuring() {
    // A connector end referencing a feature featured in an unrelated type
    // — no featuring context of the connector reaches `B::y` (warning).
    let msgs = sem_warnings(
        "package P {
            part def D;
            part def A { part x : D; }
            part def B { part y : D; }
            part def C {
                part a : A;
                connect a.x to B::y;
            }
        }",
    );
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("featured in `B`"), "{msgs:#?}");

    // Accessible shapes stay silent: same-context ends, package-owned
    // (universally featured) targets, chains rooted in the context, and
    // features reached through the one-hop featuring lift (a part typed
    // by the behavior gives access to its features).
    assert!(
        sem_warnings(
            "package P {
            part def D;
            package Elsewhere { part e1 : D; part e2 : D; }
            part system {
                part a : D;
                part b : D;
                connect a to b;
                connect a to Elsewhere::e2;
            }
        }",
        )
        .is_empty()
    );
    assert!(
        sem_warnings(
            "package P {
            action def Steps { action s1; action s2; }
            part sys {
                action run : Steps;
                succession first run.s1 then run.s2;
            }
        }",
        )
        .is_empty()
    );
}

/// Lib-gated: quantity-valued constraint arguments verify numerically.
/// An asserted constraint usage binding ISQ-typed attributes with
/// unit-bracket values evaluates through quantity arithmetic to a
/// definite verdict (12.5 V lies within 10% of 12 V) — no false
/// type-conformance error on the scalar-quantity expression, and no
/// undecided cop-out on the bound usage.
#[test]
fn quantity_constraint_verdict_with_library() {
    use sysmlv2_parser::check::ConstraintVerdict::*;
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "band.sysml",
        "package PowerCheck {
            private import ISQ::*;
            private import ScalarValues::*;
            private import NumericalFunctions::*;
            item def Feed { attribute level :> ISQ::voltage; }
            constraint def WithinBand {
                in item feed : Feed;
                in attribute nominal : Real :> ISQ::voltage;
                in attribute band : Real;
                abs(feed.level - nominal) <= band * nominal
            }
            part def Load {
                attribute supply : Feed {
                    attribute :>> level = 12.5 [SI::V];
                }
                attribute nominalLevel :> ISQ::voltage = 12 [SI::V];
                attribute tolerance : Real default 0.1;
                assert constraint inBand : WithinBand {
                    in feed = supply;
                    in nominal = nominalLevel;
                    in band = tolerance;
                }
            }
            part load1 : Load;
        }",
    );
    assert!(!model.has_errors());
    let checks = sysmlv2_parser::check::check_constraints(&model);
    let in_band: Vec<_> = checks
        .iter()
        .filter(|c| c.name.as_deref() == Some("inBand"))
        .collect();
    assert!(!in_band.is_empty(), "the asserted usage carries a verdict");
    assert!(
        in_band.iter().all(|c| matches!(c.verdict, Satisfied)),
        "{:#?}",
        in_band.iter().map(|c| &c.verdict).collect::<Vec<_>>()
    );
    // No constraint in the model may read as violated.
    assert!(
        checks.iter().all(|c| !matches!(c.verdict, Violated)),
        "no violated verdicts expected"
    );
}

/// Lib-gated: a satisfaction claim (`satisfy R by x;`) expands to
/// subject-bound constraint verdicts. Every constraint reachable through
/// the satisfied requirement's composition — nested `require` references
/// with `in` parameter bindings, inherited definition bodies, assumption
/// constraints — evaluates with R's subject bound to the satisfying
/// part, so the claim's actual truth surfaces: here the laden mass cap
/// holds but the tighter empty cap is genuinely exceeded.
#[test]
fn satisfaction_claims_expand_to_bound_verdicts() {
    use sysmlv2_parser::check::ConstraintVerdict::*;
    let lib = sysmlv2_testkit::library_dir();
    if !lib.exists() {
        eprintln!("skipping: corpus not present");
        return;
    }
    let mut model = Model::new();
    model.load_library_dir(&lib).unwrap();
    model.add_source(
        "freight.sysml",
        "package Freight {
            private import ISQ::*;
            private import SI::*;
            part def Wagon {
                attribute tare : MassValue;
                attribute cargo : MassValue;
            }
            part wagon1 : Wagon {
                attribute :>> tare = 800 [kg];
                attribute :>> cargo = 150 [kg];
                satisfy wagonSpec by wagon1;
            }
            requirement wagonSpec {
                subject unit : Wagon;
                require ladenLimit { in w = unit; }
                require emptyLimit { in w = unit; }
            }
            requirement def MassCap {
                attribute actual : MassValue;
                attribute cap : MassValue;
                require constraint { actual <= cap }
            }
            requirement def WagonMassCap :> MassCap {
                subject w : Wagon;
                attribute :>> actual = w.tare + w.cargo;
                assume constraint { w.cargo > 0 [kg] }
            }
            requirement ladenLimit : WagonMassCap {
                attribute :>> cap = 1000 [kg];
            }
            requirement emptyLimit : WagonMassCap {
                attribute :>> cap = 900 [kg];
            }
        }",
    );
    assert!(!model.has_errors());
    let checks = sysmlv2_parser::check::check_constraints(&model);
    let bound: Vec<_> = checks
        .iter()
        .filter(|c| c.context.as_deref() == Some("Freight::wagonSpec"))
        .collect();
    // Two branches × (mass-cap require + cargo assumption).
    assert_eq!(bound.len(), 4, "{bound:#?}");
    let sat = bound
        .iter()
        .filter(|c| matches!(c.verdict, Satisfied))
        .count();
    let vio = bound
        .iter()
        .filter(|c| matches!(c.verdict, Violated))
        .count();
    // 950 [kg] <= 1000 holds, <= 900 does not; the assumption holds in
    // both branches.
    assert_eq!((sat, vio), (3, 1), "{bound:#?}");
    // The unbound originals keep their honest undecided verdicts.
    assert!(
        checks
            .iter()
            .any(|c| c.context.is_none() && matches!(c.verdict, Undecided(_)))
    );
}

/// A connector with more than two ends must not specialize a *binary*
/// connector (typing, subsetting, or redefinition): the two-end shape
/// implies the binary library base, so the n-ary usage contradicts it.
/// The n-ary definition and a usage typed by it alone stay legal; the
/// diagnostic lands on the offending specialization's spelling.
#[test]
fn nary_connector_binary_specialization() {
    // Legal: three-ended definition + usage typed by it.
    assert!(
        sem_warnings(
            "package N {
             part def P;
             connection def Tri {
                 end part a : P[1];
                 end part b : P[1];
                 end part c : P[1];
             }
             part ctx {
                 part x : P; part y : P; part z : P;
                 connection t : Tri connect (a references x, b references y, c references z);
             }
         }"
        )
        .is_empty()
    );
    // Illegal: the same usage additionally subsets a two-end (binary)
    // connection.
    let msgs = sem_warnings(
        "package N {
             part def P;
             connection def Tri {
                 end part a : P[1];
                 end part b : P[1];
                 end part c : P[1];
             }
             part ctx {
                 part x : P; part y : P; part z : P;
                 connection bin connect x to y;
                 connection u : Tri :> bin connect (a references x, b references y, c references z);
             }
         }",
    );
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(
        msgs[0].contains("binary connector cannot have more than two ends"),
        "{msgs:#?}"
    );
}

/// A chain-written subsetting (`part m :> a.b;`) names a feature whose
/// featuring context is fixed by the chain's root: some owning type of
/// the subsetting feature must conform to the root's featuring type,
/// else the subsetted feature is not accessible from the subsetter
/// (KerML validateSubsettingFeaturingTypes, narrowed to chain targets).
/// Nesting the subsetter in a conforming type resolves it — and the
/// redefinitions inside keep resolving either way.
#[test]
fn chain_subsetting_featuring_accessibility() {
    // Package-level subsetter: no owner conforms to the chain root's
    // featuring type — warn (the redefinition of `rating` still works).
    let msgs = sem_warnings(
        "package S {
             part def Housing {
                 part slot : Frame;
             }
             part def Frame {
                 part cell { attribute rating; }
             }
             part merged :> Housing::slot.cell {
                 attribute :>> rating = 2;
             }
         }",
    );
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(msgs[0].contains("featured in `Housing`"), "{msgs:#?}");
    // Nested in a conforming type: clean.
    assert!(
        sem_warnings(
            "package S {
             part def Housing {
                 part slot : Frame;
             }
             part def Frame {
                 part cell { attribute rating; }
             }
             part def Wide :> Housing {
                 part merged :> slot.cell {
                     attribute :>> rating = 2;
                 }
             }
         }"
        )
        .is_empty()
    );
}

/// Invocation arity, the over-application side: more positional
/// arguments than the callee's declared `in` parameters can never bind
/// — warn (the under-application side already warns about unbound
/// trailing parameters). Exact-arity calls stay silent.
#[test]
fn invocation_over_application_warns() {
    let msgs = sem_warnings(
        "package O {
             calc def half { in x; x }
             attribute a = 4;
             attribute b = 6;
             attribute over = half(a, b);
             attribute good = half(a);
         }",
    );
    assert_eq!(msgs.len(), 1, "{msgs:#?}");
    assert!(
        msgs[0].contains("supplies 2 arguments for 1 parameter"),
        "{msgs:#?}"
    );
}

#[test]
fn target_successions_must_be_adjacent_to_their_anchor() {
    let valid = check_sysml(
        "action def A {
            action firstAction;
            then secondAction;
            then thirdAction;
            first firstAction;
            then secondAction;
        }",
    );
    assert!(valid.is_empty(), "{valid:#?}");

    let diagnostics = check_sysml(
        "action def A {
            then orphan;
            action firstAction;
            attribute separator;
            then nonAdjacent;
        }",
    );
    assert_eq!(
        diagnostics
            .iter()
            .filter(|d| d.contains("must immediately follow"))
            .count(),
        2,
        "{diagnostics:#?}"
    );
}
