//! Reads that answer from an index — the elements a membership owns, the
//! specialization index — answer what a scan of the whole table answers.

use super::ResolvedModel;
use crate::metaclass::is_a;
use crate::model::Model;
use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::Arc;

/// Calculations whose bodies run statements, reached through typing,
/// subclassification, redefinition and library specializations, beside
/// ones that do not.
const CALCULATIONS: &str = "package Calcs {
    private import ScalarValues::*;
    calc def Halve { in n : Real; attribute i : Real = n; assign i := i / 2; return result : Real = i; }
    calc def Quarter :> Halve;
    calc def Plain { in x : Real; return : Real = x + 1; }
    calc halve : Halve;
    calc quarter : Quarter;
    calc plain : Plain;
    part def Holder { calc h : Halve; calc p : Plain; }
    part holder : Holder { calc :>> h; calc :>> p; }
    requirement def Small { subject s : Holder; require constraint { true } }
    part ctx { requirement small : Small; satisfy small by holder; }
}";

/// Each owned element's owning relationship lists it, and each element
/// a relationship lists names that relationship as its owner.
fn assert_ownership_pairs(r: &ResolvedModel, label: &str) {
    for (i, row) in r.b.elements.iter().enumerate() {
        if let Some(rel) = row.owning_relationship {
            assert!(
                r.b.elements[rel].children.contains(&i),
                "{label}: row {i} names {rel} as its owner, which does not list it"
            );
        }
        for &child in &row.children {
            assert_eq!(
                r.b.elements[child].owning_relationship,
                Some(i),
                "{label}: row {i} lists {child}, which names another owner"
            );
        }
    }
}

/// [`ResolvedModel::members_under`] for every build element and every
/// membership metaclass it owns, against a scan of every row.
fn assert_members_like_a_scan(r: &ResolvedModel, label: &str) -> usize {
    let mut claimed: HashMap<usize, Vec<usize>> = HashMap::new();
    for (i, row) in r.b.elements.iter().enumerate() {
        if let Some(rel) = row.owning_relationship {
            claimed.entry(rel).or_default().push(i);
        }
    }
    let mut checked = 0;
    for e in r.b.lib_boundary..r.b.elements.len() {
        let kinds: HashSet<&'static str> = r.b.elements[e]
            .owned_relationships
            .iter()
            .map(|&rel| r.b.elements[rel].ty)
            .filter(|ty| ty.ends_with("Membership"))
            .collect();
        for kind in kinds {
            let mut scanned: Vec<usize> = r.b.elements[e]
                .owned_relationships
                .iter()
                .filter(|&&rel| r.b.elements[rel].ty == kind)
                .flat_map(|rel| claimed.get(rel).into_iter().flatten().copied())
                .collect();
            scanned.sort_unstable();
            scanned.dedup();
            assert_eq!(r.members_under(e, kind), scanned, "{label}: {kind} of {e}");
            checked += 1;
        }
    }
    checked
}

/// [`super::Builder::calculation_requires_execution`] through the index
/// for every element from `from` on, against reachability over every
/// table entry, whatever its kind. Answers how many elements require
/// execution.
fn assert_execution_like_the_table(r: &mut ResolvedModel, from: usize, label: &str) -> usize {
    let b = &mut r.b;
    let mut owners_of: HashMap<usize, Vec<usize>> = HashMap::new();
    for (i, &(owner, _, _, _)) in b.spec_targets.iter().enumerate() {
        if let Some(target) = b.spec_resolved.get(i).copied().flatten() {
            owners_of.entry(target).or_default().push(owner);
        }
    }
    let mut reaching: HashSet<usize> = b.executable_calculations.clone();
    let mut stack: Vec<usize> = reaching.iter().copied().collect();
    while let Some(target) = stack.pop() {
        for &owner in owners_of.get(&target).into_iter().flatten() {
            if reaching.insert(owner) {
                stack.push(owner);
            }
        }
    }
    for e in from..b.elements.len() {
        assert_eq!(
            b.indexed_calculation_requires_execution(e),
            reaching.contains(&e),
            "{label}: element {e}"
        );
    }
    assert!(
        b.executable_calculations.is_empty() || b.spec_index.is_some(),
        "{label}: a settled build reads the index"
    );
    reaching.len()
}

fn standard_library() -> Option<Arc<crate::prepared::PreparedLibrary>> {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../spec-refs/SysML-v2-Release/sysml.library");
    if !path.exists() {
        return None;
    }
    let mut model = Model::new();
    model.load_library_dir(&path).unwrap();
    Some(model.prepare_library().unwrap())
}

fn collect(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect(&path, out);
        } else if path.extension().is_some_and(|e| e == "sysml") {
            out.push(path);
        }
    }
}

/// Every directory of the corpus's example, training and validation
/// models as one workspace, the external corpus model when present, and
/// the calculations above, on the prepared standard library; every eighth
/// of them, the external model and the calculations again with the
/// implied relationships materialized (a whole-model pass, the sweep's
/// main cost).
#[test]
fn corpus_workspaces_read_owned_members_and_executing_calculations_like_a_scan() {
    let Some(library) = standard_library() else {
        return;
    };
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../spec-refs");
    let mut workspaces: std::collections::BTreeMap<String, Vec<PathBuf>> = Default::default();
    let mut files = Vec::new();
    for dir in ["examples", "training", "validation"] {
        collect(
            &root.join("SysML-v2-Release/sysml/src").join(dir),
            &mut files,
        );
    }
    for file in files {
        let dir = file.parent().unwrap().display().to_string();
        workspaces.entry(dir).or_default().push(file);
    }
    let mut external = Vec::new();
    collect(&root.join("apollo-11-sysml-v2"), &mut external);
    if !external.is_empty() {
        workspaces.insert("external".into(), external);
    }
    let mut units: Vec<(String, Vec<(String, String)>)> = workspaces
        .into_iter()
        .map(|(label, mut files)| {
            files.sort();
            let texts = files
                .iter()
                .map(|file| {
                    (
                        file.file_name().unwrap().to_string_lossy().into_owned(),
                        std::fs::read_to_string(file).unwrap(),
                    )
                })
                .collect();
            (label, texts)
        })
        .collect();
    units.push((
        "calculations".into(),
        vec![("calcs.sysml".into(), CALCULATIONS.into())],
    ));
    let (mut members, mut executing, mut materialized) = (0, 0, 0);
    for (k, (label, texts)) in units.iter().enumerate() {
        let mut model = Model::new();
        Arc::clone(&library).install(&mut model).unwrap();
        for (name, text) in texts {
            model.add_source(name.clone(), text);
        }
        let mut r = ResolvedModel::build(&model);
        assert_rows_carry_their_index(&r);
        assert_ownership_pairs(&r, label);
        members += assert_members_like_a_scan(&r, label);
        // The library's rows are the same in every build: walk them once.
        let from = if k == 0 { 0 } else { r.b.lib_boundary };
        let reaching = assert_execution_like_the_table(&mut r, from, label);
        if label == "calculations" {
            // Halve, Quarter, halve, quarter, Holder::h, holder::h
            assert!(reaching >= 6, "{reaching} elements require execution");
        }
        executing += reaching;
        if k % 8 == 0 || label == "external" || label == "calculations" {
            r.ensure_implied();
            assert_ownership_pairs(&r, label);
            members += assert_members_like_a_scan(&r, label);
            materialized += 1;
        }
    }
    eprintln!(
        "{} workspaces ({materialized} materialized), {members} member reads, {executing} executing",
        units.len()
    );
    assert!(units.len() > 80, "{} workspaces", units.len());
    assert!(materialized > 10, "{materialized} materialized");
    assert!(members > 10_000, "{members} member reads");
    assert!(executing > 0);
}

/// A build still lowering may hold an index made from a partial table:
/// the walk scans instead, and the indexing variant leaves the index
/// unbuilt.
#[test]
fn an_unsettled_table_is_scanned() {
    let mut model = Model::new();
    let parsed = model.add_source(
        "calcs.sysml",
        "calc def Halve { in n; attribute i = n; assign i := i / 2; return result = i; }
         calc def Quarter :> Halve;
         calc quarter : Quarter;
         calc def Plain { in x; x + 1 }
         calc plain : Plain;",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut r = ResolvedModel::build(&model);
    let quarter = r.resolve_qualified("quarter").unwrap().0;
    let plain = r.resolve_qualified("plain").unwrap().0;
    r.b.semantic_ready = false;
    r.b.spec_index = None;
    assert!(r.b.indexed_calculation_requires_execution(quarter));
    assert!(r.b.spec_index.is_none());
    r.b.spec_index = Some(Default::default());
    assert!(r.b.calculation_requires_execution(quarter));
    assert!(!r.b.calculation_requires_execution(plain));
    r.b.semantic_ready = true;
    r.b.spec_index = None;
    assert!(r.b.indexed_calculation_requires_execution(quarter));
    assert!(!r.b.indexed_calculation_requires_execution(plain));
    assert!(r.b.spec_index.is_some());
}

/// The conformance reader answers from a memo of each element's closure under
/// the typing and specialization rows, and the memo follows the rows: a
/// resolved target written after it was built starts a new one.
#[test]
fn indexed_conformance_is_memoized_per_closure_and_follows_the_resolved_targets() {
    let mut model = Model::new();
    let parsed = model.add_source(
        "closure.kerml",
        "classifier A; classifier B specializes A; classifier C specializes B; classifier D;",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut r = ResolvedModel::build(&model);
    let (a, b, c, d) = (
        r.resolve_qualified("A").unwrap().0,
        r.resolve_qualified("B").unwrap().0,
        r.resolve_qualified("C").unwrap().0,
        r.resolve_qualified("D").unwrap().0,
    );
    assert!(r.b.indexed_conforms(c, a));
    assert!(r.b.indexed_conforms(c, b));
    assert!(r.b.indexed_conforms(c, c));
    assert!(!r.b.indexed_conforms(c, d));
    assert!(!r.b.indexed_conforms(a, c));
    let memo = r.b.spec_memo.as_ref().expect("built by the first question");
    assert_eq!(memo.closures.get(&c).map(|closure| closure.len()), Some(3));
    assert!(
        memo.closures.contains_key(&a),
        "the reverse question walked A's closure"
    );
    // Cutting B's specialization of A changes C's closure once the memo
    // sees the new resolved-target revision.
    let row = (0..r.b.spec_targets.len())
        .find(|&i| r.b.spec_targets[i].0 == b && r.b.spec_targets[i].1 == "Subclassification")
        .expect("B specializes A is a subclassification row");
    assert_eq!(r.b.spec_resolved[row], Some(a));
    r.b.spec_resolved[row] = None;
    assert!(
        !r.b.indexed_conforms(c, a),
        "the memo was restarted for the new revision"
    );
    assert!(r.b.indexed_conforms(c, b));
    r.b.spec_resolved[row] = Some(a);
    assert!(r.b.indexed_conforms(c, a));
}

/// The shared redefinition-target reader lists what the direct reader lists,
/// in its order, and follows a written target like the closure memo.
#[test]
fn shared_redefinition_targets_match_the_direct_reader() {
    let mut model = Model::new();
    let parsed = model.add_source(
        "redefinitions.kerml",
        "classifier A { feature x; feature y; } classifier B specializes A { feature :>> x; feature z :>> y; }",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut r = ResolvedModel::build(&model);
    let bx = r.resolve_qualified("B::x").unwrap().0;
    let z = r.resolve_qualified("B::z").unwrap().0;
    let ay = r.resolve_qualified("A::y").unwrap().0;
    for e in [bx, z, ay] {
        let direct = r.b.indexed_redefinition_targets(e);
        let shared = r.b.indexed_redefinition_targets_shared(e);
        assert_eq!(&shared[..], &direct[..], "element {e}");
        let again = r.b.indexed_redefinition_targets_shared(e);
        assert!(
            Arc::ptr_eq(&shared, &again),
            "the second answer is the memoized one"
        );
    }
    assert_eq!(&r.b.indexed_redefinition_targets_shared(z)[..], &[ay]);
    let row = (0..r.b.spec_targets.len())
        .find(|&i| r.b.spec_targets[i].0 == z && r.b.spec_targets[i].1 == "Redefinition")
        .expect("z redefines y");
    r.b.spec_resolved[row] = None;
    assert!(r.b.indexed_redefinition_targets_shared(z).is_empty());
    r.b.spec_resolved[row] = Some(ay);
    assert_eq!(&r.b.indexed_redefinition_targets_shared(z)[..], &[ay]);
}

/// A specialization row written, a rebuilt index and the lookup-cache reset
/// all start the memo over; cycles and self-loops answer as the recorded
/// walk does.
#[test]
fn the_specialization_memo_follows_the_rows_and_agrees_with_the_recorded_walk() {
    let mut model = Model::new();
    let parsed = model.add_source(
        "cycles.kerml",
        "classifier A specializes B; classifier B specializes A; classifier S specializes S; classifier T specializes A;",
    );
    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
    let mut r = ResolvedModel::build(&model);
    let elements: Vec<usize> = ["A", "B", "S", "T"]
        .iter()
        .map(|name| r.resolve_qualified(name).unwrap().0)
        .collect();
    let mut read = Vec::new();
    for &sub in &elements {
        for &sup in &elements {
            let recorded = r.b.recorded_conforms(sub, sup, &mut read);
            assert_eq!(
                r.b.indexed_conforms(sub, sup),
                recorded,
                "{sub} conforms {sup}"
            );
        }
    }
    let (a, t) = (elements[0], elements[3]);
    assert!(r.b.spec_memo.is_some());
    // A row written through the table moves its revision: the memo restarts.
    let row = (0..r.b.spec_targets.len())
        .find(|&i| r.b.spec_targets[i].0 == t)
        .expect("T specializes A");
    let written = r.b.spec_targets[row].clone();
    r.b.spec_targets[row] = written;
    assert!(r.b.indexed_conforms(t, a));
    let memo = r.b.spec_memo.as_ref().unwrap();
    assert_eq!(
        memo.closures.len(),
        1,
        "only the question asked since the write"
    );
    // A rebuilt index and the lookup-cache reset drop it.
    r.b.spec_index = None;
    assert!(r.b.indexed_conforms(t, a));
    assert_eq!(r.b.spec_memo.as_ref().unwrap().closures.len(), 1);
    r.b.reset_lookup_caches();
    assert!(r.b.spec_memo.is_none());
}

/// A member listed under both its names hides, and is hidden, the same way
/// whichever of its name groups the implicit-redefinition step meets first.
/// In the diamond `C :> B, D`, `A::a` reaches `C` unreduced through `D`;
/// `B::a` (short name `s`) hides it, and `C::s` hides `B::a`, so `C`
/// inherits neither — also when the `s` group is decided before the `a` one.
#[test]
fn implicit_redefinition_does_not_depend_on_the_order_of_name_groups() {
    for source in [
        "part def A { part a; } part def B :> A { part <s> a; } part def D :> A; part def C :> B, D { part s; }",
        "part def A { part a; } part def B :> A { part <s> a; } part def D :> A; part def C :> D, B { part s; part other; }",
    ] {
        let mut model = Model::new();
        let parsed = model.add_source("two-keys.sysml", source);
        assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
        let mut r = ResolvedModel::build(&model);
        let c = r.resolve_qualified("C").unwrap().0;
        let scope = *r.b.elem_scope.get(&c).unwrap();
        let aa = r.resolve_qualified("A::a").unwrap().0;
        let ba = r.resolve_qualified("B::a").unwrap().0;
        for include_implied in [false, true] {
            let bindings = r.b.inherited_bindings(scope, include_implied);
            let members: Vec<usize> = bindings.members.iter().map(|&(m, _)| m).collect();
            assert!(!members.contains(&aa), "A::a is hidden by B::a ({source})");
            assert!(!members.contains(&ba), "B::a is hidden by C::s ({source})");
        }
    }
}

/// The implicit same-name redefinitions a projection decides are the same
/// whether a group is walked pair by pair or owner by owner: a type whose
/// bases own many same-named usages — unrelated owners, owners whose types
/// strictly conform, and an owner that redefines by position — hides the
/// same members and records the same pairs either way, and the collisions
/// reported do not change.
#[test]
fn implicit_redefinitions_are_the_same_pair_by_pair_and_owner_by_owner() {
    let mut source = String::from(
        "package P { part def Base { part p; } part def Mid :> Base { part p; } part def Leaf :> Mid { part p; } ",
    );
    for i in 0..12 {
        source.push_str(&format!("part def U{i} {{ part p; attribute a; }} "));
    }
    source.push_str("part def All :> Leaf");
    for i in 0..12 {
        source.push_str(&format!(", U{i}"));
    }
    source.push_str(" { part q; } part def Also :> Mid, U0, U1 { part p; } }");
    let outcome = |limit: usize| {
        crate::json::with_pairwise_group_limit(limit, || {
            let mut model = Model::new();
            model.add_source("m.sysml", &source);
            let mut r = ResolvedModel::build(&model);
            let mut projections = Vec::new();
            for name in ["P::All", "P::Also", "P::Leaf"] {
                let e = r.resolve_qualified(name).expect(name).0;
                let scope = r.b.elem_scope.get(&e).copied().expect("a body");
                let bindings = r.b.inherited_bindings(scope, true);
                let mut members: Vec<usize> = bindings.members.iter().map(|&(m, _)| m).collect();
                members.sort_unstable();
                let mut pairs = bindings.implicit_redefinitions.clone();
                pairs.sort_unstable();
                projections.push((members, pairs));
            }
            let collisions: Vec<String> = crate::check::validate_semantics(&model)
                .into_iter()
                .map(|(_, d)| d.message)
                .filter(|m| m.contains("inherited"))
                .collect();
            (projections, collisions)
        })
    };
    let (pairwise, owners) = (outcome(usize::MAX), outcome(0));
    assert_eq!(pairwise, owners);
    assert!(
        pairwise.0.iter().any(|(_, pairs)| !pairs.is_empty()),
        "some member is hidden by a same-named usage of a conforming owner"
    );
}

/// A large same-name group costs the owner walk fewer steps than the
/// pairwise one: under a budget the pairwise walk exhausts on, the owner
/// walk completes with the pairs the unbudgeted reduction decides.
#[test]
fn the_owner_walk_completes_under_a_budget_the_pairwise_walk_exhausts() {
    let mut source = String::from("package P { part def Mid { part p; } ");
    for i in 0..40 {
        source.push_str(&format!("part def U{i} :> Mid {{ part p; }} "));
    }
    source.push_str("part def All :> Mid");
    for i in 0..40 {
        source.push_str(&format!(", U{i}"));
    }
    source.push_str(" { part q; } }");
    let mut model = Model::new();
    model.add_source("m.sysml", &source);
    let mut r = ResolvedModel::build(&model);
    let all = r.resolve_qualified("P::All").expect("All").0;
    // The unreduced candidates: every base's `p` membership.
    let memberships: Vec<usize> = (0..40)
        .map(|i| format!("P::U{i}::p"))
        .chain(std::iter::once("P::Mid::p".to_string()))
        .map(|name| {
            let e = r.resolve_qualified(&name).expect(&name).0;
            r.b.elements[e].owning_relationship.expect("a membership")
        })
        .collect();
    let candidates = || crate::json::MembershipProjection {
        membership_order: memberships.clone(),
        truncated: false,
        incomplete: false,
        implicit_redefinitions: Vec::new(),
    };
    let reduce = |r: &mut ResolvedModel, limit: usize, steps: Option<&mut usize>| {
        crate::json::with_pairwise_group_limit(limit, || {
            let reduced =
                r.b.reduce_membership_projection(Some(all), false, candidates(), steps);
            let mut pairs = reduced.implicit_redefinitions;
            pairs.sort_unstable();
            (reduced.incomplete, reduced.membership_order, pairs)
        })
    };
    let (_, expected_order, expected_pairs) = reduce(&mut r, usize::MAX, None);
    assert_eq!(expected_pairs.len(), 40, "every U{{i}}::p hides Mid::p");
    // What the owner walk charges, then a budget just wide enough for it.
    let mut used = 0;
    let (incomplete, order, pairs) = reduce(&mut r, 0, Some(&mut used));
    assert!(!incomplete && order == expected_order && pairs == expected_pairs);
    let budget = crate::eval::MAX_STEPS - used - 1;
    let mut steps = budget;
    let (incomplete, _, _) = reduce(&mut r, usize::MAX, Some(&mut steps));
    assert!(incomplete, "the pairwise walk exhausts the budget");
    let mut steps = budget;
    let (incomplete, order, pairs) = reduce(&mut r, 0, Some(&mut steps));
    assert!(!incomplete, "the owner walk completes");
    assert_eq!((order, pairs), (expected_order, expected_pairs));
}

/// The protected-access test reads the kept base closures and answers as
/// the walk over the bases did, for every pair of scopes of a model with
/// specialization cycles, a self-specialization and nested types.
#[test]
fn protected_access_reads_the_base_closures_as_the_walk_answered() {
    let mut model = crate::model::Model::new();
    model.add_source(
        "m.sysml",
        "package P { part def A :> B { protected part x : D; } part def B :> A; part def C :> A { part y : D; } part def D :> D; part def E { part def F :> C { part z : D; } part def G :> F, B; } part def H; }",
    );
    let mut r = crate::json::ResolvedModel::build(&model);
    let scopes = r.b.scopes.len();
    for origin in 0..scopes {
        for target in 0..scopes {
            let walked = r.b.scope_can_access_protected_walked(origin, target);
            assert_eq!(
                r.b.scope_can_access_protected(origin, target),
                walked,
                "{origin} → {target}"
            );
        }
    }
}

/// Every row's cached metaclass index is its metaclass's: the literals set
/// both, and a row retyped later — a chain member's membership, a
/// conjugated port's typing — is retyped through `set_ty`.
#[test]
fn every_row_carries_its_metaclass_index() {
    let mut model = Model::new();
    model.add_source(
        "m.sysml",
        "package P { port def Q { attribute v; } part def A { port p : Q; port c : ~Q; attribute a; } part def B { part x : A; part y : A { port :>> p; attribute :>> a; } attribute z = x.a; } requirement def R; part def S { part sub; } part s : S; satisfy requirement r : R by s.sub; }",
    );
    let r = ResolvedModel::build(&model);
    assert_rows_carry_their_index(&r);
    // The satisfaction's subject is a chain: the membership its feature
    // reference expression owns, made as a `Membership`, is retyped
    // `OwningMembership` — the row above checked that its index followed.
    assert!(
        (0..r.b.elements.len())
            .filter(|&e| r.b.elements[e].ty == "FeatureReferenceExpression")
            .any(|fre| {
                r.b.elements[fre]
                    .owned_relationships
                    .iter()
                    .any(|&rel| is_a!(r.b.elements[rel], "OwningMembership"))
            }),
        "a chain subject's membership is an OwningMembership"
    );
}

fn assert_rows_carry_their_index(r: &ResolvedModel) {
    for e in 0..r.b.elements.len() {
        let row = &r.b.elements[e];
        assert_eq!(
            row.meta,
            crate::metaclass::meta_of(row.ty),
            "row {e} typed {}",
            row.ty
        );
    }
}
