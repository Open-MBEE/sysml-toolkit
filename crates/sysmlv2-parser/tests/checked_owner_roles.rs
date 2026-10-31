//! The owner-dependent library roles (SysML 8.3.16–8.3.18): the planner
//! plans them from a usage's place in its owner and the checked member
//! lists require them, through one list. A composite action in an action
//! is a subaction, with its kind's role; a part's actions, states, performs,
//! exhibits and ports take the part's roles; a composite state in a state
//! is a substate, exclusive or not by the owner's parallelism; a
//! transition takes `stateTransitions` or `decisionTransitions` by its
//! owner and source, a target transition (`if g then t;`, `else t;`,
//! `accept … then t;`) by the last action before it; a trigger is the
//! transition's `accepter` and an effect its `effect`; an if with an else
//! is an `ifThenElseActions`; a requirement's, case's, calculation's,
//! item's and view's members take the roles of SysML 8.3.19–8.3.25
//! (`subrequirements`, `actors`, `subcases`, `subcalculations`,
//! `checkedConstraints`, `subviews`, a view rendering's redefinition of
//! `viewRendering`, and the rest).

#![cfg(feature = "json")]

use sysmlv2_parser::{
    json::{ClosurePolicy, DerivedValue, ElementRef, Reference, ResolvedModel},
    model::Model,
};

const SUPERTYPES: &str = "Core-Types-Type-supertypes_Boolean";
const ALL_SUPERTYPES: &str = "Core-Types-Type-allSupertypes_";

const SOURCE: &str = "package Ro {
    attribute def Sig;
    port def P { in attribute a : ScalarValues::Real; }
    part def Veh {
        port p : P;
        port q : P { port sub : P; }
        action go;
        perform action run;
        state st;
        exhibit state ex;
    }
    action def A {
        action a1;
        action a2;
        attribute x;
        assign x := 1;
        accept sig : Sig;
        if true { action t1; } else { action e1; }
        if false { action t2; }
        while true { action w1; }
        for i in 1..2 { action f1; }
        decide d;
        if true then a1;
        else a2;
    }
    state def S parallel { state p1; state p2; }
    state def T {
        entry; then s1;
        state s1 { entry action e1; do action d1; exit; }
        state s2;
        transition t first s1 accept sig : Sig do action eff then s2;
        transition u first s2 then s1;
        if true then s1;
        else s2;
    }
    action top;
    state def U { do top; }
    occurrence def OD { event occurrence ev; }
    event occurrence lone;
    item def I { part p; item j; constraint c; }
    concern def Cn;
    requirement def RD {
        subject s; actor act; stakeholder sh;
        assume constraint asm; require constraint req;
        requirement sub; frame concern fc : Cn;
    }
    requirement r : RD;
    case def CD { actor act; case sub; }
    analysis def AD { analysis sub; }
    verification def VD { objective { verify r; } verification sub; }
    verification def VD2 :> VD { objective { verify r; } }
    verification def VD3 :> VD2;
    verification v3 : VD3 { objective goal { verify r; } }
    use case def UD { use case sub; include use case inc : UD; }
    calc def CalcD { calc sub; }
    rendering def RenD { rendering sub; }
    view def ViewD { view sub; render rendering rend : RenD; viewpoint vp; }
}";

fn model() -> ResolvedModel {
    let mut model = Model::new();
    model
        .load_library_dir(&sysmlv2_testkit::library_dir())
        .unwrap();
    let unit = model.add_source("roles.sysml", SOURCE);
    assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
    let mut r = ResolvedModel::build(&model);
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: true,
    });
    r
}

fn qualified(r: &mut ResolvedModel, e: ElementRef) -> String {
    r.element_qualified_name(e)
        .unwrap_or_else(|| format!("<{}>", r.element_type(e)))
}

fn named(r: &mut ResolvedModel, path: &str) -> ElementRef {
    r.resolve_qualified(path)
        .unwrap_or_else(|| panic!("no {path}"))
}

fn owned(r: &mut ResolvedModel, kind: &str, owner: ElementRef) -> Vec<ElementRef> {
    r.elements_of_metaclass(kind)
        .into_iter()
        .filter(|&e| r.owner(e) == Some(owner))
        .collect()
}

fn supertypes(
    r: &mut ResolvedModel,
    e: ElementRef,
    operation: &str,
    arguments: &[DerivedValue],
) -> Vec<String> {
    let what = qualified(r, e);
    match r
        .invoke_operation(e, operation, arguments)
        .unwrap_or_else(|err| panic!("{what} {operation}: {err}"))
        .value
    {
        DerivedValue::References(list) => list
            .into_iter()
            .map(|reference| match reference {
                Reference::Element(e) => qualified(r, e),
                other => panic!("{other:?}"),
            })
            .collect(),
        other => panic!("{other:?}"),
    }
}

/// The complete direct bases, and the member lists answering.
fn direct(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    let what = qualified(r, e);
    r.property(e, "feature")
        .unwrap_or_else(|err| panic!("{what}.feature: {err}"));
    supertypes(r, e, SUPERTYPES, &[DerivedValue::Bool(false)])
}

/// The planned implied relationships' targets.
fn implied(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    let mut targets = Vec::new();
    for edge in r.implied_relationships(e) {
        for target in r.relationship_ends(edge).1 {
            match target {
                Reference::Element(t) => targets.push(qualified(r, t)),
                other => panic!("{other:?}"),
            }
        }
    }
    targets
}

#[test]
fn subactions_substates_and_part_roles_follow_the_owner() {
    let mut r = model();
    for (path, bases) in [
        // A composite action in an action definition: the kind's `actions`
        // is reached through `subactions` and minimized away.
        ("Ro::A::a1", vec!["Actions::Action::subactions"]),
        // A part's action, performed action, state and exhibited state.
        ("Ro::Veh::go", vec!["Parts::Part::ownedActions"]),
        ("Ro::Veh::run", vec!["Parts::Part::performedActions"]),
        ("Ro::Veh::st", vec!["Parts::Part::ownedStates"]),
        ("Ro::Veh::ex", vec!["Parts::Part::exhibitedStates"]),
        // A part's port and a port's port.
        ("Ro::Veh::p", vec!["Ro::P", "Parts::Part::ownedPorts"]),
        ("Ro::Veh::q::sub", vec!["Ro::P", "Ports::Port::subports"]),
        // Substates of a parallel and of an exclusive state definition.
        ("Ro::S::p1", vec!["States::StateAction::substates"]),
        ("Ro::T::s1", vec!["States::StateAction::exclusiveStates"]),
        ("Ro::T::s2", vec!["States::StateAction::exclusiveStates"]),
        // A state-owned transition whose source is a state, triggered or not.
        ("Ro::T::t", vec!["States::StateAction::stateTransitions"]),
        ("Ro::T::u", vec!["States::StateAction::stateTransitions"]),
        // A package-owned action has kind roles alone.
        ("Ro::top", vec!["Actions::actions"]),
    ] {
        let e = named(&mut r, path);
        assert_eq!(direct(&mut r, e), bases, "{path}");
    }
    // A state's entry and do actions are performed actions the lowering
    // writes as references: no subaction role (and the do action takes
    // none either, not being composite); each redefines the state
    // action's feature of its kind, which reaches the kind role.
    for (path, base) in [
        ("Ro::T::s1::e1", "States::StateAction::entryAction"),
        ("Ro::T::s1::d1", "States::StateAction::doAction"),
    ] {
        let e = named(&mut r, path);
        assert_eq!(direct(&mut r, e), [base], "{path}");
    }
}

#[test]
fn loops_ifs_triggers_effects_and_decision_transitions_take_their_roles() {
    let mut r = model();
    let a = named(&mut r, "Ro::A");
    let t = named(&mut r, "Ro::T::t");
    // The kind-specific subaction roles, each minimizing its kind role away.
    for (kind, role) in [
        ("WhileLoopActionUsage", "Actions::Action::whileLoops"),
        ("ForLoopActionUsage", "Actions::Action::forLoops"),
    ] {
        let loops = owned(&mut r, kind, a);
        assert_eq!(loops.len(), 1, "{kind}");
        assert_eq!(direct(&mut r, loops[0]), [role], "{kind}");
    }
    // An if with an else is an `ifThenElseActions`; without one an
    // `ifThenActions`; both are `ifSubactions` of their action.
    let ifs = owned(&mut r, "IfActionUsage", a);
    assert_eq!(ifs.len(), 2);
    let mut kinds: Vec<Vec<String>> = ifs.iter().map(|&e| direct(&mut r, e)).collect();
    kinds.sort();
    // `ifSubactions` subsets `ifThenActions`, so an if without an else
    // keeps the owner role alone; `ifThenElseActions` is not reached
    // through it and stays.
    assert_eq!(
        kinds,
        [
            vec!["Actions::Action::ifSubactions"],
            vec![
                "Actions::ifThenElseActions",
                "Actions::Action::ifSubactions"
            ],
        ]
    );
    // The accept action in an action is an `acceptSubactions`; the trigger
    // of a transition is its `accepter` and no `acceptActions`.
    let accept = owned(&mut r, "AcceptActionUsage", a);
    assert_eq!(accept.len(), 1);
    assert_eq!(
        direct(&mut r, accept[0]),
        ["Actions::Action::acceptSubactions"]
    );
    let trigger = owned(&mut r, "AcceptActionUsage", t);
    assert_eq!(trigger.len(), 1);
    let bases = direct(&mut r, trigger[0]);
    assert!(
        bases.contains(&"Actions::TransitionAction::accepter".to_string()),
        "{bases:?}"
    );
    assert!(
        !bases.contains(&"Actions::acceptActions".to_string()),
        "{bases:?}"
    );
    let all = supertypes(&mut r, trigger[0], ALL_SUPERTYPES, &[]);
    assert!(
        !all.contains(&"Actions::acceptActions".to_string()),
        "{all:?}"
    );
    // The transition's effect action.
    let effect = owned(&mut r, "PerformActionUsage", t);
    assert_eq!(effect.len(), 1);
    assert_eq!(
        direct(&mut r, effect[0]),
        ["Actions::TransitionAction::effect"]
    );
    // The guarded successions after `decide d` are action-owned target
    // transitions: their source is the last action before them, the
    // decision node, so they are `decisionTransitions` (which reaches the
    // kind role and `subactions`). Their first, empty parameter pairs with
    // the transition action's link source.
    let transitions = owned(&mut r, "TransitionUsage", a);
    assert_eq!(transitions.len(), 2);
    let decision = owned(&mut r, "DecisionNode", a);
    assert_eq!(decision.len(), 1);
    for transition in transitions {
        assert_eq!(
            direct(&mut r, transition),
            ["Actions::Action::decisionTransitions"]
        );
        assert_eq!(r.transition_parts(transition).source, Some(decision[0]));
        assert_eq!(r.implicit_transition_source(transition), Some(decision[0]));
        let parameters = owned(&mut r, "ReferenceUsage", transition);
        assert_eq!(parameters.len(), 1);
        let planned = implied(&mut r, parameters[0]);
        assert!(
            planned.contains(&"Actions::TransitionAction::transitionLinkSource".to_string()),
            "{planned:?}"
        );
    }
    // A state's target transitions (`if true then s1; else s2;` after
    // `state s2`) leave the last state before them: `stateTransitions`,
    // the derived source, and the transition succession's source end
    // referencing that state.
    let t_def = named(&mut r, "Ro::T");
    let s2 = named(&mut r, "Ro::T::s2");
    let targets: Vec<ElementRef> = owned(&mut r, "TransitionUsage", t_def)
        .into_iter()
        .filter(|&e| r.element_name(e).is_none())
        .collect();
    assert_eq!(targets.len(), 2);
    for transition in targets {
        assert_eq!(
            direct(&mut r, transition),
            ["States::StateAction::stateTransitions"]
        );
        assert_eq!(r.transition_parts(transition).source, Some(s2));
        assert_eq!(r.implicit_transition_source(transition), Some(s2));
        let successions = owned(&mut r, "SuccessionAsUsage", transition);
        assert_eq!(successions.len(), 1);
        let ends = owned(&mut r, "ReferenceUsage", successions[0]);
        assert_eq!(ends.len(), 2);
        let planned = implied(&mut r, ends[0]);
        assert!(planned.contains(&"Ro::T::s2".to_string()), "{planned:?}");
    }
    // A transition's guard expression is the transition action's guard,
    // which the library declares on the kernel's transition performance.
    let guarded = owned(&mut r, "TransitionUsage", a)[0];
    let guards = owned(&mut r, "LiteralBoolean", guarded);
    assert_eq!(guards.len(), 1);
    let guard = guards[0];
    assert_eq!(
        r.owning_membership_type(guard),
        Some("TransitionFeatureMembership")
    );
    let planned = implied(&mut r, guard);
    assert!(
        planned.contains(&"TransitionPerformances::TransitionPerformance::guard".to_string()),
        "{planned:?}"
    );
    assert!(
        direct(&mut r, guard)
            .contains(&"TransitionPerformances::TransitionPerformance::guard".to_string()),
        "{:?}",
        direct(&mut r, guard)
    );
    // A written source is read as written.
    let t = named(&mut r, "Ro::T::t");
    assert!(r.implicit_transition_source(t).is_none());
    let s1 = named(&mut r, "Ro::T::s1");
    assert_eq!(r.transition_parts(t).source, Some(s1));
    // A triggered state transition's first parameter is the link source's
    // slot and its second the payload: they pair with the state transition
    // action's parameters through `stateTransitions`.
    let parameters = owned(&mut r, "ReferenceUsage", t);
    assert_eq!(parameters.len(), 2);
    let planned: Vec<Vec<String>> = parameters.iter().map(|&p| implied(&mut r, p)).collect();
    assert!(
        planned[0].contains(&"States::StateTransitionAction::transitionLinkSource".to_string()),
        "{planned:?}"
    );
    assert!(
        planned[1].contains(&"States::StateTransitionAction::payload".to_string()),
        "{planned:?}"
    );
}

#[test]
fn the_planner_writes_the_owner_roles_as_implied_subsettings() {
    let mut r = model();
    // The planned rows name the owner role; the kind role a path reaches
    // is not written twice.
    let a1 = named(&mut r, "Ro::A::a1");
    assert_eq!(implied(&mut r, a1), ["Actions::Action::subactions"]);
    let p1 = named(&mut r, "Ro::S::p1");
    assert_eq!(implied(&mut r, p1), ["States::StateAction::substates"]);
    let go = named(&mut r, "Ro::Veh::go");
    assert_eq!(implied(&mut r, go), ["Parts::Part::ownedActions"]);
    let p = named(&mut r, "Ro::Veh::p");
    assert_eq!(implied(&mut r, p), ["Parts::Part::ownedPorts"]);
}

/// The names in `e`'s inherited view.
fn view(r: &mut ResolvedModel, e: ElementRef) -> Vec<String> {
    let features = r.effective_features(e, true);
    features.into_iter().map(|f| qualified(r, f)).collect()
}

#[test]
fn the_inherited_view_follows_the_owner_roles() {
    let mut r = model();
    let has = |seen: &[String], name: &str| seen.iter().any(|f| f == name);
    // A state's sourced transition inherits through `stateTransitions`:
    // the state transition action's features are in view, and the
    // transition action's link source, which the transition's first
    // parameter redefines through the state transition action's, is
    // hidden with it.
    let t = named(&mut r, "Ro::T::t");
    let seen = view(&mut r, t);
    assert!(
        has(
            &seen,
            "StatePerformances::StateTransitionPerformance::acceptable"
        ),
        "{seen:?}"
    );
    assert!(
        !has(&seen, "Actions::TransitionAction::transitionLinkSource"),
        "{seen:?}"
    );
    assert!(
        !has(&seen, "States::StateTransitionAction::payload"),
        "{seen:?}"
    );
    // An untriggered one keeps the payload it does not redefine.
    let u = named(&mut r, "Ro::T::u");
    let seen = view(&mut r, u);
    assert!(
        has(&seen, "States::StateTransitionAction::payload"),
        "{seen:?}"
    );
    assert!(
        !has(&seen, "Actions::TransitionAction::transitionLinkSource"),
        "{seen:?}"
    );
    // An if's parameters hide the if-then action's, through
    // `ifThenElseActions` when it has an else.
    let a = named(&mut r, "Ro::A");
    for e in owned(&mut r, "IfActionUsage", a) {
        let seen = view(&mut r, e);
        assert!(!has(&seen, "Actions::IfThenAction::ifTest"), "{seen:?}");
        assert!(!has(&seen, "Actions::IfThenAction::thenClause"), "{seen:?}");
    }
    // An assignment's target redefines `assignments::target`, which
    // redefines `assignmentActions::target`: neither stays in view.
    let assignments = owned(&mut r, "AssignmentActionUsage", a);
    assert_eq!(assignments.len(), 1);
    let seen = view(&mut r, assignments[0]);
    assert!(
        !has(&seen, "Actions::Action::assignments::target"),
        "{seen:?}"
    );
    assert!(
        !has(&seen, "Actions::assignmentActions::target"),
        "{seen:?}"
    );
}

#[test]
fn requirements_cases_calculations_and_views_take_their_owner_roles() {
    let mut r = model();
    // Each planned as an implied subsetting and among all supertypes; the
    // complete direct bases of a few, minimized to the owner role.
    for (path, role) in [
        ("Ro::I::c", "Items::Item::checkedConstraints"),
        (
            "Ro::RD::sub",
            "Requirements::RequirementCheck::subrequirements",
        ),
        ("Ro::RD::act", "Requirements::RequirementCheck::actors"),
        ("Ro::RD::sh", "Requirements::RequirementCheck::stakeholders"),
        ("Ro::RD::asm", "Requirements::RequirementCheck::assumptions"),
        ("Ro::RD::req", "Requirements::RequirementCheck::constraints"),
        ("Ro::RD::fc", "Requirements::RequirementCheck::concerns"),
        ("Ro::CD::act", "Cases::Case::actors"),
        ("Ro::CD::sub", "Cases::Case::subcases"),
        (
            "Ro::AD::sub",
            "AnalysisCases::AnalysisCase::subAnalysisCases",
        ),
        (
            "Ro::VD::sub",
            "VerificationCases::VerificationCase::subVerificationCases",
        ),
        ("Ro::UD::sub", "UseCases::UseCase::subUseCases"),
        ("Ro::UD::inc", "UseCases::UseCase::includedUseCases"),
        (
            "Ro::CalcD::sub",
            "Calculations::Calculation::subcalculations",
        ),
        ("Ro::RenD::sub", "Views::Rendering::subrenderings"),
        ("Ro::ViewD::sub", "Views::View::subviews"),
        ("Ro::ViewD::vp", "Views::View::viewpointSatisfactions"),
    ] {
        let e = named(&mut r, path);
        let planned = implied(&mut r, e);
        assert!(planned.contains(&role.to_string()), "{path}: {planned:?}");
        let all = supertypes(&mut r, e, ALL_SUPERTYPES, &[]);
        assert!(all.contains(&role.to_string()), "{path}: {all:?}");
    }
    for (path, bases) in [
        (
            "Ro::RD::sub",
            vec!["Requirements::RequirementCheck::subrequirements"],
        ),
        ("Ro::CD::sub", vec!["Cases::Case::subcases"]),
        (
            "Ro::CalcD::sub",
            vec!["Calculations::Calculation::subcalculations"],
        ),
        ("Ro::ViewD::sub", vec!["Views::View::subviews"]),
        (
            "Ro::UD::inc",
            vec!["Ro::UD", "UseCases::UseCase::includedUseCases"],
        ),
    ] {
        let e = named(&mut r, path);
        assert_eq!(direct(&mut r, e), bases, "{path}");
    }
    // The requirement a verification case's objective verifies.
    let objective = named(&mut r, "Ro::VD::obj");
    let verified = owned(&mut r, "RequirementUsage", objective);
    assert_eq!(verified.len(), 1);
    let planned = implied(&mut r, verified[0]);
    assert!(
        planned.contains(
            &"VerificationCases::VerificationCase::obj::requirementVerifications".to_string()
        ),
        "{planned:?}"
    );
    // A view's rendering redefines the view's `viewRendering`.
    let rendering = named(&mut r, "Ro::ViewD::rend");
    let planned = implied(&mut r, rendering);
    assert!(
        planned.contains(&"Views::View::viewRendering".to_string()),
        "{planned:?}"
    );
    let kinds: Vec<String> = r
        .implied_relationships(rendering)
        .into_iter()
        .map(|edge| r.element_type(edge).to_string())
        .collect();
    assert!(kinds.contains(&"Redefinition".to_string()), "{kinds:?}");
    // A viewpoint's kind role is the library's `viewpointChecks`.
    let viewpoint = named(&mut r, "Ro::ViewD::vp");
    let all = supertypes(&mut r, viewpoint, ALL_SUPERTYPES, &[]);
    assert!(
        all.contains(&"Views::viewpointChecks".to_string()),
        "{all:?}"
    );
}

#[test]
fn state_actions_redefine_the_state_action_features_and_take_their_names() {
    let mut r = model();
    // The redefinitions are planned, named or not.
    for (path, role) in [
        ("Ro::T::s1::e1", "States::StateAction::entryAction"),
        ("Ro::T::s1::d1", "States::StateAction::doAction"),
    ] {
        let e = named(&mut r, path);
        let planned = implied(&mut r, e);
        assert!(planned.contains(&role.to_string()), "{path}: {planned:?}");
    }
    // An unnamed one is named by what it redefines, as the pilot names it:
    // `entry;` of T is `T::entryAction`, `exit;` of s1 is `s1::exitAction`.
    let entry = named(&mut r, "Ro::T::entryAction");
    assert_eq!(r.owning_membership_kind(entry), Some("entry"));
    assert_eq!(r.element_name(entry), None);
    assert_eq!(
        r.element_effective_name(entry).as_deref(),
        Some("entryAction")
    );
    let planned = implied(&mut r, entry);
    assert!(
        planned.contains(&"States::StateAction::entryAction".to_string()),
        "{planned:?}"
    );
    let exit = named(&mut r, "Ro::T::s1::exitAction");
    assert_eq!(r.owning_membership_kind(exit), Some("exit"));
    assert_eq!(
        r.element_effective_name(exit).as_deref(),
        Some("exitAction")
    );
    let planned = implied(&mut r, exit);
    assert!(
        planned.contains(&"States::StateAction::exitAction".to_string()),
        "{planned:?}"
    );
    // A named one keeps its name.
    let e1 = named(&mut r, "Ro::T::s1::e1");
    assert_eq!(r.element_effective_name(e1).as_deref(), Some("e1"));
    // One that performs an action is named by it
    // (`PerformActionUsage::namingFeature`), ahead of the `doAction` it
    // still redefines: `do top;` is `U::top`, and `U::doAction` is not it.
    let performed = named(&mut r, "Ro::U::top");
    assert_eq!(r.owning_membership_kind(performed), Some("do"));
    assert_eq!(r.element_effective_name(performed).as_deref(), Some("top"));
    assert_ne!(r.resolve_qualified("Ro::U::doAction"), Some(performed));
    let planned = implied(&mut r, performed);
    assert!(
        planned.contains(&"States::StateAction::doAction".to_string()),
        "{planned:?}"
    );
}

#[test]
fn event_occurrences_in_occurrences_are_time_enclosed() {
    let mut r = model();
    // SysML `checkEventOccurrenceUsageSpecialization`: the kind role
    // `Occurrences::occurrences` is minimized away behind it.
    let ev = named(&mut r, "Ro::OD::ev");
    assert_eq!(
        direct(&mut r, ev),
        ["Occurrences::Occurrence::timeEnclosedOccurrences"]
    );
    let planned = implied(&mut r, ev);
    assert!(
        planned.contains(&"Occurrences::Occurrence::timeEnclosedOccurrences".to_string()),
        "{planned:?}"
    );
    // In a package the event keeps its kind role alone.
    let lone = named(&mut r, "Ro::lone");
    assert_eq!(direct(&mut r, lone), ["Occurrences::occurrences"]);
}

#[test]
fn objectives_redefine_the_specialized_cases_objectives() {
    let mut r = model();
    // SysML `checkRequirementUsageObjectiveRedefinition`: VD2's objective
    // redefines VD's (and is named `obj` by it); v3's named objective
    // redefines the one VD3 inherits from VD2.
    let obj2 = named(&mut r, "Ro::VD2::obj");
    let planned = implied(&mut r, obj2);
    assert!(planned.contains(&"Ro::VD::obj".to_string()), "{planned:?}");
    assert_eq!(r.element_effective_name(obj2).as_deref(), Some("obj"));
    let goal = named(&mut r, "Ro::v3::goal");
    let planned = implied(&mut r, goal);
    assert!(planned.contains(&"Ro::VD2::obj".to_string()), "{planned:?}");
    // The redefined objective is hidden from the specializing case's view;
    // the library objective stays redefined through the chain.
    let vd2 = named(&mut r, "Ro::VD2");
    let features = r.property(vd2, "feature").unwrap();
    let names: Vec<String> = features
        .as_array()
        .unwrap()
        .iter()
        .map(|v| {
            let id = v["@id"].as_str().unwrap().to_string();
            let e = r.element_by_id(&id).unwrap();
            r.element_qualified_name(e).unwrap_or_default()
        })
        .collect();
    assert!(names.contains(&"Ro::VD2::obj".to_string()), "{names:?}");
    assert!(!names.contains(&"Ro::VD::obj".to_string()), "{names:?}");
}
