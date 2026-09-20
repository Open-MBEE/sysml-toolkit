//! The derived-property read API, family by family, against the
//! specification's definition of each property (KerML/SysML clause 8.3;
//! the OCL rules in `spec-refs/derived-properties.json`) rather than
//! against the emitter's current output.

#![cfg(feature = "json")]

use sysmlv2_parser::json::{
    ClosurePolicy, Derived, DerivedValue, Derives, ElementRef, Reference, ResolvedModel,
    computed_names, derives,
};
use sysmlv2_parser::model::Model;

fn build(src: &str) -> ResolvedModel {
    let mut model = Model::new();
    model.add_source("m.sysml", src);
    assert!(
        !model.has_errors(),
        "test model must parse clean: {:?}",
        model
            .units()
            .iter()
            .flat_map(|u| u.diagnostics.iter())
            .collect::<Vec<_>>()
    );
    ResolvedModel::build(&model)
}

fn elem(r: &mut ResolvedModel, r_qn: &str) -> ElementRef {
    r.resolve_qualified(r_qn)
        .unwrap_or_else(|| panic!("no element {r_qn}"))
}

/// A single-valued composition or in-model reference.
fn one(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Option<ElementRef> {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::Element(x))
        | Derived::Value(DerivedValue::Reference(Reference::Element(x))) => Some(x),
        Derived::Value(DerivedValue::Null) => None,
        other => panic!("{name}: expected a single in-model reference, got {other:?}"),
    }
}

/// A multi-valued composition, or a reference list whose every target is
/// in the model.
fn many(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Vec<ElementRef> {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::Elements(v)) => v,
        Derived::Value(DerivedValue::References(v)) => v
            .into_iter()
            .map(|x| match x {
                Reference::Element(x) => x,
                other => panic!("{name}: a target outside the model: {other:?}"),
            })
            .collect(),
        other => panic!("{name}: expected a reference list, got {other:?}"),
    }
}

fn refs(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Vec<Reference> {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::References(v)) => v,
        Derived::Value(DerivedValue::Reference(x)) => vec![x],
        Derived::Value(DerivedValue::Null) => Vec::new(),
        other => panic!("{name}: expected references, got {other:?}"),
    }
}

fn names(r: &mut ResolvedModel, v: &[ElementRef]) -> Vec<String> {
    v.iter()
        .map(|&x| {
            r.element_effective_name(x)
                .unwrap_or_else(|| r.element_type(x).to_string())
        })
        .collect()
}

#[test]
fn tri_state_distinguishes_undeclared_uncomputed_and_value() {
    let mut r = build("package P { part def V { attribute mass; } }");
    let v = elem(&mut r, "P::V");
    // A Definition declares `ownedFeature`; a Package does not.
    assert!(matches!(r.derived(v, "ownedFeature"), Derived::Value(_)));
    let p = elem(&mut r, "P");
    assert_eq!(r.derived(p, "ownedFeature"), Derived::NotDeclared);
    // An owned property is never answered as derived.
    assert_eq!(r.derived(v, "declaredName"), Derived::NotDeclared);
    // Declared but not yet computed by the layer.
    let mass = elem(&mut r, "P::V::mass");
    assert_eq!(r.derived(mass, "mayTimeVary"), Derived::NotComputed);
    // A name that is derived on Namespace and owned on MembershipImport.
    assert_eq!(
        derives("Package", "importedMembership"),
        Derives::Passthrough
    );
    assert_eq!(
        derives("MembershipImport", "importedMembership"),
        Derives::NotDeclared
    );
    // Static fidelity.
    assert_eq!(derives("PartDefinition", "ownedFeature"), Derives::Exact);
    assert_eq!(derives("PartDefinition", "feature"), Derives::Passthrough);
    assert_eq!(derives("PartDefinition", "nosuch"), Derives::NotDeclared);
}

#[test]
fn element_family_follows_the_owning_relationship() {
    // owner = owningRelationship.owningRelatedElement; owningMembership is
    // the owning relationship when it is a Membership; owningNamespace is
    // that membership's owner; ownedElement = ownedRelationship.ownedRelatedElement.
    let mut r = build(
        "package P {
            part def V { attribute mass; }
            part def W :> V;
         }",
    );
    let p = elem(&mut r, "P");
    let v = elem(&mut r, "P::V");
    let mass = elem(&mut r, "P::V::mass");
    assert_eq!(one(&mut r, mass, "owner"), Some(v));
    assert_eq!(one(&mut r, v, "owner"), Some(p));
    // The unit's root Namespace owns the package and has no owner itself.
    let root = one(&mut r, p, "owner").expect("the document root owns P");
    assert_eq!(r.element_type(root), "Namespace");
    assert_eq!(one(&mut r, root, "owner"), None);
    assert_eq!(one(&mut r, root, "owningMembership"), None);
    let om = one(&mut r, mass, "owningMembership").expect("owning membership");
    assert_eq!(r.element_type(om), "FeatureMembership");
    assert_eq!(one(&mut r, mass, "owningNamespace"), Some(v));
    // The memberships are V's owned elements' carriers; ownedElement lists
    // the elements those relationships own, mass included.
    let owned = many(&mut r, v, "ownedElement");
    assert!(owned.contains(&mass));
    // A relationship owned directly by its related element has no owning
    // relationship, hence no owner per the specification.
    let w = elem(&mut r, "P::W");
    let sub = r
        .owned_relationships(w)
        .into_iter()
        .find(|&x| r.element_type(x) == "Subclassification")
        .expect("W owns its Subclassification");
    assert_eq!(one(&mut r, sub, "owner"), None);
    assert_eq!(one(&mut r, sub, "owningMembership"), None);
    assert!(matches!(
        r.derived(v, "isLibraryElement"),
        Derived::Value(DerivedValue::Bool(false))
    ));
    // The specific side owns its Subclassification and is its owningType /
    // owningClassifier.
    assert_eq!(one(&mut r, sub, "owningType"), Some(w));
    assert_eq!(one(&mut r, sub, "owningClassifier"), Some(w));
}

#[test]
fn library_element_follows_library_packages_not_units() {
    // isLibraryElement = libraryNamespace() <> null: a `library package`
    // in an ordinary unit makes its contents library elements.
    let mut r = build(
        "library package L { part def T; }
         package P { part def U; }",
    );
    let t = elem(&mut r, "L::T");
    let u = elem(&mut r, "P::U");
    assert_eq!(
        r.derived(t, "isLibraryElement"),
        Derived::Value(DerivedValue::Bool(true))
    );
    assert_eq!(
        r.derived(u, "isLibraryElement"),
        Derived::Value(DerivedValue::Bool(false))
    );
    assert!(!r.is_library_element(t), "not from a library unit");
}

#[test]
fn standalone_relationship_has_no_owning_type() {
    // KerML spells a standalone specialization as a member.
    let mut model = Model::new();
    model.add_source(
        "m.kerml",
        "package P {
            classifier A; classifier B;
            specialization S subclassifier B specializes A;
         }",
    );
    assert!(!model.has_errors());
    let mut r = ResolvedModel::build(&model);
    let s = r
        .elements_of_metaclass("Subclassification")
        .into_iter()
        .find(|&x| !r.is_library_element(x))
        .expect("the standalone specialization");
    assert_eq!(one(&mut r, s, "owningType"), None);
    assert_eq!(one(&mut r, s, "owningClassifier"), None);
    // It rides a membership: owner is P.
    let p = elem(&mut r, "P");
    assert_eq!(one(&mut r, s, "owner"), Some(p));
}

#[test]
fn namespace_family_selects_membership_kinds() {
    let mut r = build(
        "package P {
            part def V { attribute mass; }
            alias M for V;
            import V::*;
            part x : V;
         }",
    );
    let p = elem(&mut r, "P");
    let v = elem(&mut r, "P::V");
    let x = elem(&mut r, "P::x");
    // ownedMembership: every owned Membership, aliases included; ownedMember:
    // the owned members of the *owning* memberships only.
    let ms = many(&mut r, p, "ownedMembership");
    assert_eq!(ms.len(), 3, "V, the alias, x");
    let alias = ms
        .iter()
        .copied()
        .find(|&m| r.membership_is_alias(m))
        .expect("alias membership listed");
    let om = many(&mut r, p, "ownedMember");
    assert_eq!(names(&mut r, &om), ["V", "x"]);
    // member = membership.memberElement: the alias contributes its target.
    let members = many(&mut r, p, "member");
    assert_eq!(members, [v, v, x], "V, the alias's target V, x");
    assert!(r.membership_member(alias) == Some(v));
    // ownedImport: the Import relationships.
    let imports = many(&mut r, p, "ownedImport");
    assert_eq!(imports.len(), 1);
    assert_eq!(r.element_type(imports[0]), "NamespaceImport");
    assert_eq!(one(&mut r, imports[0], "importOwningNamespace"), Some(p));
    assert_eq!(one(&mut r, imports[0], "importedElement"), Some(v));
    // A membership's namespace and owned member.
    let vm = one(&mut r, v, "owningMembership").unwrap();
    assert_eq!(one(&mut r, vm, "membershipOwningNamespace"), Some(p));
    assert_eq!(one(&mut r, vm, "ownedMemberElement"), Some(v));
    assert_eq!(
        r.derived(vm, "ownedMemberFeature"),
        Derived::NotDeclared,
        "an OwningMembership is not a FeatureMembership"
    );
}

#[test]
fn type_and_feature_family_use_feature_memberships_only() {
    let mut r = build(
        "package P {
            part def V {
                attribute mass;
                part def Nested;
                variant part alt;
            }
            part v : V { part w; }
         }",
    );
    let v = elem(&mut r, "P::V");
    let mass = elem(&mut r, "P::V::mass");
    // ownedFeature reads the FeatureMembership kinds: the nested definition
    // (an OwningMembership) and the variant (a VariantMembership — an
    // OwningMembership, not a FeatureMembership, though its member is a
    // feature) do not count.
    let of = many(&mut r, v, "ownedFeature");
    assert_eq!(names(&mut r, &of), ["mass"]);
    let fms = many(&mut r, v, "ownedFeatureMembership");
    assert_eq!(fms.len(), 1);
    assert_eq!(one(&mut r, fms[0], "ownedMemberFeature"), Some(mass));
    assert_eq!(one(&mut r, fms[0], "owningType"), Some(v));
    // ownedMember still lists all three owning memberships' members.
    assert_eq!(many(&mut r, v, "ownedMember").len(), 3);
    // Feature side.
    assert_eq!(one(&mut r, mass, "owningType"), Some(v));
    assert_eq!(one(&mut r, mass, "owningFeatureMembership"), Some(fms[0]));
    assert_eq!(one(&mut r, mass, "owningDefinition"), Some(v));
    assert_eq!(one(&mut r, mass, "owningUsage"), None);
    assert_eq!(one(&mut r, mass, "endOwningType"), None);
    let vu = elem(&mut r, "P::v");
    let w = elem(&mut r, "P::v::w");
    assert_eq!(one(&mut r, w, "owningUsage"), Some(vu));
    assert_eq!(one(&mut r, w, "owningDefinition"), None);
    // A package-owned usage has no owning type.
    assert_eq!(one(&mut r, vu, "owningType"), None);
    assert_eq!(one(&mut r, vu, "owningFeatureMembership"), None);
}

#[test]
fn end_owning_type_needs_an_end_feature_membership() {
    let mut r = build(
        "package P {
            part def A; part def B;
            connection def C { end a : A; end b : B; }
         }",
    );
    let c = elem(&mut r, "P::C");
    let a = elem(&mut r, "P::C::a");
    assert_eq!(one(&mut r, a, "endOwningType"), Some(c));
    assert_eq!(one(&mut r, a, "owningType"), Some(c));
    let fm = one(&mut r, a, "owningFeatureMembership").unwrap();
    assert_eq!(r.element_type(fm), "EndFeatureMembership");
}

#[test]
fn passthrough_names_answer_the_owned_side() {
    // `feature` and `featureMembership` union the inherited memberships in
    // the specification; at the passthrough level they answer the owned
    // side, exactly as the full form does.
    let mut r = build(
        "package P {
            part def Base { attribute x; }
            part def Sub :> Base { attribute y; }
         }",
    );
    let sub = elem(&mut r, "P::Sub");
    let f = many(&mut r, sub, "feature");
    assert_eq!(names(&mut r, &f), ["y"]);
    assert_eq!(derives("PartDefinition", "feature"), Derives::Passthrough);
    assert_eq!(
        many(&mut r, sub, "featureMembership"),
        many(&mut r, sub, "ownedFeatureMembership")
    );
    // The exact inherited view is the accessor, not the passthrough name.
    let inh = r.inherited_features(sub, false);
    assert_eq!(names(&mut r, &inh), ["x"]);
}

#[test]
fn chain_targets_ride_owning_memberships() {
    // `first a.b` owns its synthesized chain feature through an
    // OwningMembership (SysML.xtext `TransitionSourceMember`), so the
    // chain feature is an owned member and that membership its owning
    // membership.
    let mut r = build(
        "package P {
            part def V { part a { part b; } }
            state def S {
                part v : V;
                state s2;
                transition first v.a then s2;
            }
         }",
    );
    let s = elem(&mut r, "P::S");
    let transitions = r.elements_of_metaclass("TransitionUsage");
    let t = transitions
        .into_iter()
        .find(|&t| one(&mut r, t, "owner") == Some(s))
        .expect("the transition");
    let owned = many(&mut r, t, "ownedMember");
    let chain = owned
        .iter()
        .copied()
        .find(|&f| r.element_type(f) == "Feature")
        .expect("the source chain feature is an owned member");
    let m = one(&mut r, chain, "owningMembership").expect("owning membership");
    assert_eq!(r.element_type(m), "OwningMembership");
    assert_eq!(one(&mut r, m, "ownedMemberElement"), Some(chain));
    assert!(many(&mut r, t, "member").contains(&chain));
}

#[test]
fn membership_import_imports_the_member() {
    let mut r = build(
        "package P {
            package L { part def T; }
            package U { import L::T; }
         }",
    );
    let u = elem(&mut r, "P::U");
    let t = elem(&mut r, "P::L::T");
    let imports = many(&mut r, u, "ownedImport");
    assert_eq!(imports.len(), 1);
    assert_eq!(r.element_type(imports[0]), "MembershipImport");
    assert_eq!(one(&mut r, imports[0], "importedElement"), Some(t));
}

#[test]
fn kind_filtered_compositions_are_conformance_inclusive() {
    // `ownedPart = ownedUsage->selectByKind(PartUsage)` and friends: a part
    // is also an item and an occurrence; a state is an action; a
    // requirement is a constraint. Nested* mirror owned* on usages.
    let mut r = build(
        "package P {
            part def V {
                attribute mass;
                part wheel;
                port p;
                ref item cargo;
                action a;
                state s;
                constraint c;
                requirement req;
            }
            part v : V { part w; }
         }",
    );
    let v = elem(&mut r, "P::V");
    let list = |r: &mut ResolvedModel, e, n: &str| -> Vec<String> {
        let items = many(r, e, n);
        names(r, &items)
    };
    assert_eq!(list(&mut r, v, "ownedPart"), ["wheel"]);
    assert_eq!(
        list(&mut r, v, "ownedItem"),
        ["wheel", "cargo"],
        "a part is an item"
    );
    assert!(
        list(&mut r, v, "ownedOccurrence").len() >= 5,
        "parts, ports, items, actions, states are occurrences: {:?}",
        list(&mut r, v, "ownedOccurrence")
    );
    assert_eq!(list(&mut r, v, "ownedAttribute"), ["mass"]);
    assert_eq!(list(&mut r, v, "ownedPort"), ["p"]);
    assert_eq!(
        list(&mut r, v, "ownedAction"),
        ["a", "s"],
        "a state is an action"
    );
    assert_eq!(list(&mut r, v, "ownedState"), ["s"]);
    assert_eq!(
        list(&mut r, v, "ownedConstraint"),
        ["c", "req"],
        "a requirement is a constraint"
    );
    assert_eq!(list(&mut r, v, "ownedRequirement"), ["req"]);
    // Definitions declare owned*, usages declare nested*.
    assert_eq!(r.derived(v, "nestedPart"), Derived::NotDeclared);
    let vu = elem(&mut r, "P::v");
    assert_eq!(list(&mut r, vu, "nestedPart"), ["w"]);
    assert_eq!(r.derived(vu, "ownedPart"), Derived::NotDeclared);
    // Static fidelity: exact over an exact base, passthrough over `usage`.
    assert_eq!(derives("PartDefinition", "ownedPart"), Derives::Exact);
    assert_eq!(derives("ActionDefinition", "action"), Derives::Passthrough);
    assert_eq!(derives("PartUsage", "nestedPart"), Derives::Exact);
}

#[test]
fn definition_back_references_follow_the_declared_type() {
    // `partDefinition` is the usage's definitions that are PartDefinitions
    // (through itemDefinition / occurrenceDefinition), `attributeDefinition`
    // its DataType definitions; a single-valued one takes the first match.
    let mut r = build(
        "package P {
            part def V;
            attribute def Mass;
            part v : V;
            attribute m : Mass;
            action def Go;
            action go : Go;
         }",
    );
    let v = elem(&mut r, "P::v");
    let vd = elem(&mut r, "P::V");
    assert_eq!(many(&mut r, v, "definition"), [vd]);
    assert_eq!(many(&mut r, v, "occurrenceDefinition"), [vd]);
    assert_eq!(many(&mut r, v, "itemDefinition"), [vd]);
    assert_eq!(many(&mut r, v, "partDefinition"), [vd]);
    let m = elem(&mut r, "P::m");
    let md = elem(&mut r, "P::Mass");
    assert_eq!(many(&mut r, m, "attributeDefinition"), [md]);
    assert_eq!(r.derived(m, "partDefinition"), Derived::NotDeclared);
    let go = elem(&mut r, "P::go");
    let god = elem(&mut r, "P::Go");
    assert_eq!(many(&mut r, go, "actionDefinition"), [god]);
    assert_eq!(derives("ActionUsage", "actionDefinition"), Derives::Exact);
    // A composition over a passthrough base is passthrough; the same
    // name on FlowDefinition is another property (`associationEnd`).
    assert_eq!(derives("FlowUsage", "flowEnd"), Derives::Passthrough);
    assert_eq!(derives("FlowDefinition", "flowEnd"), Derives::NotComputed);
}

#[test]
fn direction_and_end_filters() {
    let mut r = build(
        "package P {
            action def A { in item x; out item y; inout item z; item w; }
            connection def C { end e1 : A; end e2 : A; }
         }",
    );
    let a = elem(&mut r, "P::A");
    let list = |r: &mut ResolvedModel, e, n: &str| -> Vec<String> {
        let items = many(r, e, n);
        names(r, &items)
    };
    assert_eq!(list(&mut r, a, "directedFeature"), ["x", "y", "z"]);
    // Feature order, per the OCL — `inout` is not moved after the one-way
    // features.
    assert_eq!(list(&mut r, a, "input"), ["x", "z"]);
    assert_eq!(list(&mut r, a, "output"), ["y", "z"]);
    let mut r2 = build("package Q { action def B { inout item z; in item x; out item y; } }");
    let b = elem(&mut r2, "Q::B");
    let items = many(&mut r2, b, "input");
    assert_eq!(names(&mut r2, &items), ["z", "x"]);
    let items = many(&mut r2, b, "output");
    assert_eq!(names(&mut r2, &items), ["z", "y"]);
    assert_eq!(list(&mut r, a, "directedUsage"), ["x", "y", "z"]);
    let c = elem(&mut r, "P::C");
    assert_eq!(list(&mut r, c, "ownedEndFeature"), ["e1", "e2"]);
    assert_eq!(list(&mut r, c, "endFeature"), ["e1", "e2"]);
    assert_eq!(
        derives("ConnectionDefinition", "endFeature"),
        Derives::Passthrough
    );
}

#[test]
fn type_closes_over_typing_features() {
    // Feature::type walks the typing features: a feature typed only
    // through subsetting, redefinition or a chain inherits its target's
    // types, so the definition back-references follow.
    let mut r = build(
        "package P {
            part def V;
            part v : V;
            part w :> v;
            part x :>> w;
            part y : V { part z :> v; }
         }",
    );
    let vd = elem(&mut r, "P::V");
    for qn in ["P::v", "P::w", "P::x", "P::y::z"] {
        let f = elem(&mut r, qn);
        assert_eq!(many(&mut r, f, "type"), [vd], "{qn}");
        assert_eq!(many(&mut r, f, "partDefinition"), [vd], "{qn}");
    }
}

#[test]
fn a_composition_is_not_computed_where_its_base_is_another_property() {
    // `action` on a StateSubactionMembership is a single required
    // reference (the owned member), not `usage->selectByKind(ActionUsage)`:
    // a membership-side name, exact there.
    assert_eq!(
        derives("StateSubactionMembership", "action"),
        Derives::Exact
    );
    assert_eq!(
        derives("RequirementConstraintMembership", "ownedConstraint"),
        Derives::Exact
    );
    assert_eq!(derives("ActionDefinition", "action"), Derives::Passthrough);
    let mut r = build(
        "package P {
            state def S { state s1; entry action a; }
         }",
    );
    let m = r
        .elements_of_metaclass("StateSubactionMembership")
        .into_iter()
        .find(|&x| !r.is_library_element(x))
        .expect("the entry membership");
    assert!(matches!(
        r.derived(m, "action"),
        Derived::Value(DerivedValue::Element(_))
    ));
    // Compositions over the owned relationships are exact.
    assert_eq!(derives("PartDefinition", "ownedDisjoining"), Derives::Exact);
    assert_eq!(derives("PartUsage", "nestedEnumeration"), Derives::Exact);
    assert_eq!(derives("PortUsage", "portDefinition"), Derives::Exact);
    assert_eq!(
        derives("ConjugatedPortTyping", "portDefinition"),
        Derives::NotComputed
    );
}

#[test]
fn annotation_family_reads_both_shapes() {
    // This toolkit emits the `about` shape: the annotating element owns
    // the Annotation, which names the annotated element.
    let mut r = build(
        "package P {
            part def V;
            comment C about V /* hi */
            doc /* on P */
         }",
    );
    let p = elem(&mut r, "P");
    let v = elem(&mut r, "P::V");
    let c = elem(&mut r, "P::C");
    let ann = many(&mut r, c, "annotation");
    assert_eq!(ann.len(), 1);
    assert_eq!(r.element_type(ann[0]), "Annotation");
    assert_eq!(many(&mut r, c, "ownedAnnotatingRelationship"), ann);
    assert!(many(&mut r, c, "ownedAnnotation").is_empty());
    assert_eq!(many(&mut r, c, "annotatedElement"), [v]);
    // The Annotation's own ends.
    assert_eq!(one(&mut r, ann[0], "annotatingElement"), Some(c));
    assert_eq!(one(&mut r, ann[0], "owningAnnotatingElement"), Some(c));
    assert_eq!(one(&mut r, ann[0], "ownedAnnotatingElement"), None);
    assert_eq!(one(&mut r, ann[0], "owningAnnotatedElement"), None);
    // `annotatedElement` is owned on Annotation, derived on the
    // annotating element.
    assert_eq!(r.derived(ann[0], "annotatedElement"), Derived::NotDeclared);
    assert_eq!(one(&mut r, c, "owningAnnotatingRelationship"), None);
    // An annotating element with no Annotation annotates its owner.
    let doc = r
        .elements_of_metaclass("Documentation")
        .into_iter()
        .find(|&x| !r.is_library_element(x))
        .expect("the doc");
    assert!(many(&mut r, doc, "annotation").is_empty());
    assert_eq!(many(&mut r, doc, "annotatedElement"), [p]);
    assert_eq!(one(&mut r, doc, "documentedElement"), Some(p));
    // `representedElement` is a TextualRepresentation property.
    assert_eq!(r.derived(doc, "representedElement"), Derived::NotDeclared);
}

#[test]
fn text_multiplicity_reference_and_conjugator() {
    let mut r = build(
        "package P {
            requirement def R { doc /* must hold */ doc /* and also */ }
            part def V { part w[2]; ref part x; }
            port def Q; part p2 : ~Q;
         }",
    );
    let req = elem(&mut r, "P::R");
    assert_eq!(
        r.derived(req, "text"),
        Derived::Value(DerivedValue::Strings(vec![
            "must hold ".into(),
            "and also ".into()
        ]))
    );
    let w = elem(&mut r, "P::V::w");
    let m = one(&mut r, w, "multiplicity").expect("w[2] has a multiplicity");
    assert_eq!(r.element_type(m), "MultiplicityRange");
    let x = elem(&mut r, "P::V::x");
    assert_eq!(
        r.derived(x, "isReference"),
        Derived::Value(DerivedValue::Bool(true))
    );
    assert_eq!(
        r.derived(w, "isReference"),
        Derived::Value(DerivedValue::Bool(false))
    );
    // A conjugated port definition owns its PortConjugation.
    let cpd = r
        .elements_of_metaclass("ConjugatedPortDefinition")
        .into_iter()
        .find(|&x| !r.is_library_element(x))
        .expect("`~Q` synthesizes a conjugated port definition");
    let c = one(&mut r, cpd, "ownedConjugator").expect("the conjugator");
    assert_eq!(r.element_type(c), "PortConjugation");
    let orig = one(&mut r, cpd, "originalPortDefinition").expect("original");
    assert_eq!(r.element_type(orig), "PortDefinition");
}

fn string(r: &mut ResolvedModel, e: ElementRef, name: &str) -> Option<String> {
    match r.derived(e, name) {
        Derived::Value(DerivedValue::Str(s)) => Some(s),
        Derived::Value(DerivedValue::Null) => None,
        other => panic!("{name}: expected a string, got {other:?}"),
    }
}

/// `Element::name` / `shortName` / `qualifiedName` per KerML 8.2.3.5: an
/// unnamed feature is named by the feature it redefines (recursively),
/// references, or chains to; `qualifiedName` falls back to the short name
/// where `name` does not.
#[test]
fn names_follow_the_naming_feature() {
    let mut r = build(
        "package P {
            part def Tank { attribute mass = 1; }
            part base { part tank : Tank; part <spare> : Tank; part <'fuel tank'> ft : Tank; }
            part actual :> base {
                part :>> tank { attribute :>> mass = 2; }
                part :>> spare;
                part :>> ft;
                part aka :>> tank;
                part <x> :>> ft;
            }
        }",
    );
    let tank = elem(&mut r, "P::actual::tank");
    assert_eq!(string(&mut r, tank, "name").as_deref(), Some("tank"));
    assert_eq!(string(&mut r, tank, "shortName"), None);
    assert_eq!(
        string(&mut r, tank, "qualifiedName").as_deref(),
        Some("P::actual::tank")
    );
    let mass = elem(&mut r, "P::actual::tank::mass");
    assert_eq!(string(&mut r, mass, "name").as_deref(), Some("mass"));
    assert_eq!(
        string(&mut r, mass, "qualifiedName").as_deref(),
        Some("P::actual::tank::mass")
    );
    // A naming feature with only a short name: `name` stays null,
    // `shortName` is the naming feature's, and `qualifiedName` uses it.
    let spare = elem(&mut r, "P::actual::spare");
    assert_eq!(string(&mut r, spare, "name"), None);
    assert_eq!(string(&mut r, spare, "shortName").as_deref(), Some("spare"));
    assert_eq!(
        string(&mut r, spare, "qualifiedName").as_deref(),
        Some("P::actual::spare")
    );
    // Both names come from the naming feature.
    let ft = elem(&mut r, "P::actual::ft");
    assert_eq!(string(&mut r, ft, "name").as_deref(), Some("ft"));
    assert_eq!(
        string(&mut r, ft, "shortName").as_deref(),
        Some("fuel tank")
    );
    // Declaring either name makes both names the declared ones (KerML
    // `effectiveName()`: `if declaredShortName <> null or declaredName <>
    // null then declaredName …`): no short name from the naming feature
    // beside a declared name, and no name beside a declared short name.
    let aka = elem(&mut r, "P::actual::aka");
    assert_eq!(string(&mut r, aka, "name").as_deref(), Some("aka"));
    assert_eq!(string(&mut r, aka, "shortName"), None);
    let x = elem(&mut r, "P::actual::x");
    assert_eq!(string(&mut r, x, "name"), None);
    assert_eq!(string(&mut r, x, "shortName").as_deref(), Some("x"));
    assert_eq!(
        string(&mut r, x, "qualifiedName").as_deref(),
        Some("P::actual::x")
    );
    // The public accessors agree with the spec names; the lookup name
    // keeps the declared-or-short-or-written notion.
    assert_eq!(r.element_effective_name(spare), None);
    assert_eq!(r.element_short_name(spare).as_deref(), Some("spare"));
    assert_eq!(r.element_lookup_name(spare).as_deref(), Some("spare"));
    assert_eq!(r.element_declared_short_name(spare), None);
}

/// Implied positional names: the members whose owned feature implicitly
/// redefines a library feature take that feature's name — connector ends,
/// succession ends, return parameters, subjects, invocation arguments.
#[test]
fn implied_positional_names() {
    let mut r = build(
        "package P {
            part def Tank;
            part a : Tank; part b : Tank;
            connection c connect a to b;
            action def A {
                action x; action y;
                succession first x then y;
            }
            calc def Sum { in p; in q; return : Tank; }
            attribute total = Sum(1, 2);
            calc def Gap { in : Tank; in q; return : Tank; }
            attribute gapped = Gap(1, 2);
            calc def Both { inout m; in n; return : Tank; }
            attribute both = Both(1, 2);
            requirement def R { subject : Tank; }
            use case def U { actor : Tank; }
        }",
    );
    let c = elem(&mut r, "P::c");
    let ends = many(&mut r, c, "ownedEndFeature");
    assert_eq!(ends.len(), 2);
    assert_eq!(string(&mut r, ends[0], "name").as_deref(), Some("source"));
    assert_eq!(string(&mut r, ends[1], "name").as_deref(), Some("target"));
    assert_eq!(
        string(&mut r, ends[1], "qualifiedName").as_deref(),
        Some("P::c::target")
    );
    // Succession ends.
    let a = elem(&mut r, "P::A");
    let succession = many(&mut r, a, "ownedFeature")
        .into_iter()
        .find(|&f| r.element_type(f) == "SuccessionAsUsage")
        .expect("succession");
    let ends = many(&mut r, succession, "ownedEndFeature");
    assert_eq!(
        string(&mut r, ends[0], "name").as_deref(),
        Some("earlierOccurrence")
    );
    assert_eq!(
        string(&mut r, ends[1], "name").as_deref(),
        Some("laterOccurrence")
    );
    // The unnamed return parameter and subject.
    let sum = elem(&mut r, "P::Sum");
    let ret = many(&mut r, sum, "ownedFeature")
        .into_iter()
        .find(|&f| string(&mut r, f, "name").as_deref() == Some("result"))
        .expect("return parameter named result");
    assert_eq!(
        string(&mut r, ret, "qualifiedName").as_deref(),
        Some("P::Sum::result")
    );
    let req = elem(&mut r, "P::R");
    assert!(
        many(&mut r, req, "ownedFeature")
            .into_iter()
            .any(|f| string(&mut r, f, "name").as_deref() == Some("subj"))
    );
    // Positional invocation arguments take the callee's `in` parameter
    // names, in order.
    let total = elem(&mut r, "P::total");
    let invocation = many(&mut r, total, "ownedElement")
        .into_iter()
        .find(|&e| r.element_type(e) == "InvocationExpression")
        .expect("invocation");
    let args: Vec<String> = many(&mut r, invocation, "ownedFeature")
        .into_iter()
        .filter_map(|f| string(&mut r, f, "name"))
        .collect();
    assert_eq!(args, vec!["p".to_string(), "q".to_string()]);
    // An unnamed input parameter holds its position; `inout` counts.
    let arg_names = |r: &mut ResolvedModel, owner: &str| -> Vec<Option<String>> {
        let e = elem(r, owner);
        let invocation = many(r, e, "ownedElement")
            .into_iter()
            .find(|&e| r.element_type(e) == "InvocationExpression")
            .expect("invocation");
        many(r, invocation, "ownedFeature")
            .into_iter()
            .map(|f| string(r, f, "name"))
            .collect()
    };
    let gapped = arg_names(&mut r, "P::gapped");
    assert!(gapped.contains(&Some("q".to_string())));
    assert!(!gapped.contains(&Some("p".to_string())));
    assert_eq!(gapped.iter().flatten().count(), 1);
    let both: Vec<String> = arg_names(&mut r, "P::both").into_iter().flatten().collect();
    assert_eq!(both, vec!["m".to_string(), "n".to_string()]);
    // An actor parameter's reference carries no name.
    let u = elem(&mut r, "P::U");
    let actor = many(&mut r, u, "ownedFeature")
        .into_iter()
        .find(|&f| r.element_type(f) == "PartUsage")
        .expect("actor parameter");
    assert_eq!(string(&mut r, actor, "name"), None);
}

/// `qualifiedName` is null for an element without an `owningNamespace`
/// — a chain feature owned by its ReferenceSubsetting, an expression
/// owned by a FeatureValue — even when it has a name.
#[test]
fn qualified_name_needs_a_membership_chain() {
    let mut r = build(
        "package P {
            part def Tank { attribute mass; }
            part t : Tank; part t2 : Tank;
            attribute m = t.mass;
            connection c connect t.mass to t.mass;
            connection d connect t to t2;
        }",
    );
    let c = elem(&mut r, "P::c");
    let end = many(&mut r, c, "ownedEndFeature")[0];
    // The end references a chain feature it owns through the
    // ReferenceSubsetting; the chain is named by its last link but has
    // no owning namespace.
    let chain = many(&mut r, end, "ownedElement")
        .into_iter()
        .find(|&e| r.element_type(e) == "Feature" || r.element_type(e) == "ReferenceUsage")
        .expect("chain feature");
    assert_eq!(string(&mut r, chain, "name").as_deref(), Some("mass"));
    assert_eq!(string(&mut r, chain, "qualifiedName"), None);
    assert_eq!(r.element_qualified_name(chain), None);
    // The reference spelling joins the lookup names, not the
    // specification's: an end of `connect t to t2` is `P::d::source` by
    // its implied positional name but was written under no name at all.
    let d = elem(&mut r, "P::d");
    let end = many(&mut r, d, "ownedEndFeature")[0];
    assert_eq!(
        string(&mut r, end, "qualifiedName").as_deref(),
        Some("P::d::source")
    );
    assert_eq!(r.element_lookup_name(end), None);
    assert_eq!(r.element_reference_spelling(end), None);
}

/// A reference-typed property reports a target outside the model instead
/// of dropping it: an unresolved spelling by its text, an id the model
/// does not hold as external.
#[test]
fn references_outside_the_model_are_reported() {
    let mut r = build(
        "package P {
            attribute m : Real;
            comment about Base::Anything /* c */
            import ISQ::mass;
            part def T { attribute a; part sub; }
            part t : T;
            attribute x = t.sub;
            connection c connect t.a to t.sub;
        }",
    );
    let m = elem(&mut r, "P::m");
    assert_eq!(
        refs(&mut r, m, "type"),
        vec![Reference::Unresolved("Real".to_string())]
    );
    // The comment's target and the import's target never resolved.
    let p = elem(&mut r, "P");
    let comment = many(&mut r, p, "ownedElement")
        .into_iter()
        .find(|&e| r.element_type(e) == "Comment")
        .expect("comment");
    assert_eq!(
        refs(&mut r, comment, "annotatedElement"),
        vec![Reference::Unresolved("Base::Anything".to_string())]
    );
    let import = many(&mut r, p, "ownedImport")[0];
    assert_eq!(
        refs(&mut r, import, "importedElement"),
        vec![Reference::Unresolved("ISQ::mass".to_string())]
    );
    // `member` lists non-owning memberships' targets too (none here
    // outside the model).
    assert!(
        refs(&mut r, p, "member")
            .iter()
            .all(|x| x.element().is_some())
    );
    // A feature chain: `chainingFeature` in order, `featureTarget` the
    // last link, `self` for an unchained feature.
    let t = elem(&mut r, "P::t");
    assert_eq!(one(&mut r, t, "featureTarget"), Some(t));
    let c = elem(&mut r, "P::c");
    let end = many(&mut r, c, "ownedEndFeature")[1];
    let chain = many(&mut r, end, "ownedElement")
        .into_iter()
        .find(|&e| r.element_type(e) == "ReferenceUsage" || r.element_type(e) == "Feature")
        .expect("chain feature");
    let links = many(&mut r, chain, "chainingFeature");
    assert_eq!(names(&mut r, &links), vec!["t", "sub"]);
    let sub = elem(&mut r, "P::T::sub");
    assert_eq!(one(&mut r, chain, "featureTarget"), Some(sub));
    let chainings = many(&mut r, chain, "ownedFeatureChaining");
    assert_eq!(chainings.len(), 2);
    assert_eq!(one(&mut r, chainings[0], "featureChained"), Some(chain));
    // The value helpers.
    let v = r.derived(chain, "chainingFeature");
    if let Derived::Value(v) = v {
        assert_eq!(v.elements(), links);
        assert_eq!(v.element(), None);
    }
}

/// The implied relationships are relationship elements of the model once
/// asked for: the library specializations of each kind (SysML Tables
/// 31/32) and a variant's specialization of its variation. They are
/// listed by the relationship families, owned by their specific side,
/// and carry the endpoint families like any relationship — while the
/// explicit graph the resolver and lints iterate stays as built. None
/// exist for a model whose library bases are unknown.
#[test]
fn implied_relationships_are_materialized_on_demand() {
    let src = "package P {
            part def V;
            part def W :> V;
            enum def Color { red; green; }
            part v : V;
            part w :> v;
            part def Box { variant part small : V; variant part sized : Box; }
            variation part vb : Box { variant part tiny : V; }
            attribute c : Color;
        }";
    // Without a library or a name table: nothing, not even the variant
    // specializations, so `isImpliedIncluded = false` holds.
    let mut r = build(src);
    let red = elem(&mut r, "P::Color::red");
    assert!(r.implied_relationships(red).is_empty());
    assert_eq!(many(&mut r, red, "ownedSpecialization"), Vec::new());
    assert_eq!(refs(&mut r, red, "type"), Vec::new());
    // With the bases known.
    let mut r = build(src);
    let mut names = std::collections::HashMap::new();
    names.insert(
        uuid::Uuid::new_v4().to_string(),
        vec!["Parts".to_string(), "Part".to_string()],
    );
    r.set_library_names(&names);
    let explicit: Vec<ElementRef> = r.user_elements().collect();
    let typings_before = r.elements_of_metaclass("FeatureTyping");
    let red = elem(&mut r, "P::Color::red");
    let implied = r.implied_relationships(red);
    assert_eq!(implied.len(), 1);
    let typing = implied[0];
    assert!(r.is_implied(typing));
    assert_eq!(r.element_type(typing), "FeatureTyping");
    let color = elem(&mut r, "P::Color");
    assert_eq!(one(&mut r, typing, "owningType"), Some(red));
    assert_eq!(one(&mut r, typing, "owningFeature"), Some(red));
    let (source, target) = r.relationship_ends(typing);
    assert_eq!(source, vec![Reference::Element(red)]);
    assert_eq!(target, vec![Reference::Element(color)]);
    assert_eq!(
        refs(&mut r, typing, "relatedElement"),
        vec![Reference::Element(red), Reference::Element(color)]
    );
    assert_eq!(one(&mut r, typing, "owner"), None);
    assert_eq!(
        r.element_properties(typing)
            .get("isImplied")
            .and_then(|v| v.as_bool()),
        Some(true)
    );
    // The relationship families list it; the navigation accessor keeps
    // the explicit graph; `type` and the definition back-references follow
    // it.
    assert_eq!(many(&mut r, red, "ownedSpecialization"), vec![typing]);
    assert_eq!(many(&mut r, red, "ownedTyping"), vec![typing]);
    assert_eq!(r.owned_relationships(red), Vec::new());
    assert_eq!(many(&mut r, red, "type"), vec![color]);
    assert_eq!(one(&mut r, red, "enumerationDefinition"), Some(color));
    // A variant of a variation definition is typed by it — unless it
    // already is; a variant of a variation usage subsets it.
    let small = elem(&mut r, "P::Box::small");
    let boxdef = elem(&mut r, "P::Box");
    let rels = r.implied_relationships(small);
    assert_eq!(rels.len(), 1);
    assert_eq!(r.element_type(rels[0]), "FeatureTyping");
    assert_eq!(
        r.relationship_ends(rels[0]).1,
        vec![Reference::Element(boxdef)]
    );
    let sized = elem(&mut r, "P::Box::sized");
    assert!(r.implied_relationships(sized).is_empty());
    let tiny = elem(&mut r, "P::vb::tiny");
    let vb = elem(&mut r, "P::vb");
    let rels = r.implied_relationships(tiny);
    assert_eq!(rels.len(), 1);
    assert_eq!(r.element_type(rels[0]), "Subsetting");
    assert_eq!(r.relationship_ends(rels[0]).1, vec![Reference::Element(vb)]);
    // The explicit specialization stays where it was, first in the list.
    let w = elem(&mut r, "P::w");
    let subs = many(&mut r, w, "ownedSubsetting");
    assert_eq!(subs.len(), 1);
    assert!(!r.is_implied(subs[0]));
    // The element iteration is unchanged by the materialization.
    let after: Vec<ElementRef> = r.user_elements().collect();
    assert_eq!(after, explicit);
    assert_eq!(r.elements_of_metaclass("FeatureTyping"), typings_before);
    // Ids are the emitter's: uuid5(OID, "<owner id>/implied0").
    let expected = uuid::Uuid::new_v5(
        &uuid::Uuid::NAMESPACE_OID,
        format!("{}/implied0", r.element_id(red)).as_bytes(),
    );
    assert_eq!(r.element_id(typing), expected);
}

/// The checks read the explicit model: validating after the layer
/// materialized the implied relationships reports what validating before
/// did.
#[test]
fn materialization_does_not_change_the_checks() {
    let src = "package P {
            part def V;
            enum def Color { red; green; }
            connection def C { end part a : V; }
            attribute c : Color;
        }";
    let mut model = Model::new();
    model.add_source("m.sysml", src);
    let mut r = ResolvedModel::build(&model);
    let mut names = std::collections::HashMap::new();
    names.insert(
        uuid::Uuid::new_v4().to_string(),
        vec!["Connections".to_string(), "Connection".to_string()],
    );
    r.set_library_names(&names);
    let before = sysmlv2_parser::check::validate_model_with(&mut r, &model);
    let red = elem(&mut r, "P::Color::red");
    assert!(!r.implied_relationships(red).is_empty());
    let c = elem(&mut r, "P::C");
    assert!(!many(&mut r, c, "ownedSubclassification").is_empty());
    let after = sysmlv2_parser::check::validate_model_with(&mut r, &model);
    assert_eq!(
        format!("{before:?}"),
        format!("{after:?}"),
        "diagnostics must not depend on the implied relationships"
    );
}

/// With a library name table, the Tables 31/32 specializations target
/// the named library elements, which are outside the model.
#[test]
fn library_specializations_through_a_name_table() {
    let mut r = build("package P { part def V; part v : V; part w :> v; }");
    let part_id = uuid::Uuid::new_v4();
    let parts_id = uuid::Uuid::new_v4();
    let mut names = std::collections::HashMap::new();
    names.insert(
        part_id.to_string(),
        vec!["Parts".to_string(), "Part".to_string()],
    );
    names.insert(
        parts_id.to_string(),
        vec!["Parts".to_string(), "parts".to_string()],
    );
    r.set_library_names(&names);
    let v = elem(&mut r, "P::V");
    let sub = many(&mut r, v, "ownedSubclassification");
    assert_eq!(sub.len(), 1);
    assert_eq!(
        r.relationship_ends(sub[0]).1,
        vec![Reference::External(part_id)]
    );
    assert_eq!(one(&mut r, sub[0], "owningClassifier"), Some(v));
    // A usage typed but not subsetted still gets its implied subsetting;
    // one that subsets explicitly does not (anti-redundancy).
    let usage = elem(&mut r, "P::v");
    let subs = many(&mut r, usage, "ownedSubsetting");
    assert_eq!(subs.len(), 1);
    assert_eq!(
        r.relationship_ends(subs[0]).1,
        vec![Reference::External(parts_id)]
    );
    let w = elem(&mut r, "P::w");
    assert!(
        many(&mut r, w, "ownedSubsetting")
            .iter()
            .all(|&s| !r.is_implied(s))
    );
}

/// `source`/`target` (the navigation accessor — owned in the abstract
/// syntax) and the derived `relatedElement` for the relationship kinds.
#[test]
fn relationship_endpoints() {
    let mut r = build(
        "package Q { part def Z; }
        package P {
            import Q::*;
            part def V :> Z;
            part v : V;
            alias vv for v;
            dependency v to V;
            comment about v /* c */
        }",
    );
    let p = elem(&mut r, "P");
    let v_def = elem(&mut r, "P::V");
    let z = elem(&mut r, "Q::Z");
    let v = elem(&mut r, "P::v");
    let sub = many(&mut r, v_def, "ownedSubclassification")[0];
    assert_eq!(
        refs(&mut r, sub, "relatedElement"),
        vec![Reference::Element(v_def), Reference::Element(z)]
    );
    // Memberships: owner → member; an alias's member is its target.
    let alias = many(&mut r, p, "ownedMembership")
        .into_iter()
        .find(|&m| r.membership_is_alias(m))
        .expect("alias");
    assert_eq!(
        r.relationship_ends(alias),
        (vec![Reference::Element(p)], vec![Reference::Element(v)])
    );
    assert_eq!(r.derived(alias, "source"), Derived::NotDeclared);
    // An import: owner → imported namespace.
    let import = many(&mut r, p, "ownedImport")[0];
    let q = elem(&mut r, "Q");
    assert_eq!(r.relationship_ends(import).1, vec![Reference::Element(q)]);
    // A dependency: clients → suppliers.
    let dep = many(&mut r, p, "ownedElement")
        .into_iter()
        .find(|&e| r.element_type(e) == "Dependency")
        .expect("dependency");
    assert_eq!(
        r.relationship_ends(dep),
        (vec![Reference::Element(v)], vec![Reference::Element(v_def)])
    );
    assert_eq!(
        refs(&mut r, dep, "relatedElement"),
        vec![Reference::Element(v), Reference::Element(v_def)]
    );
    // An annotation: annotating → annotated.
    let comment = many(&mut r, p, "ownedElement")
        .into_iter()
        .find(|&e| r.element_type(e) == "Comment")
        .expect("comment");
    let annotation = many(&mut r, comment, "annotation")[0];
    assert_eq!(
        r.relationship_ends(annotation),
        (
            vec![Reference::Element(comment)],
            vec![Reference::Element(v)]
        )
    );
}

/// Connector and flow ends at the passthrough level: the owned end
/// features, the features they reference, and a flow's source output /
/// target input features.
#[test]
fn connector_and_flow_ends() {
    let mut r = build(
        "package P {
            part def T { port p; attribute a; }
            part x : T; part y : T;
            connection c connect x.p to y.p;
            flow f from x.a to y.a;
            attribute z = x.a;
        }",
    );
    let c = elem(&mut r, "P::c");
    let ends = many(&mut r, c, "connectorEnd");
    assert_eq!(ends.len(), 2);
    assert_eq!(ends, many(&mut r, c, "ownedEndFeature"));
    // The related features are the chain features the ends reference.
    let related = refs(&mut r, c, "relatedFeature");
    assert_eq!(related.len(), 2);
    assert_eq!(refs(&mut r, c, "sourceFeature"), vec![related[0].clone()]);
    assert_eq!(refs(&mut r, c, "targetFeature"), vec![related[1].clone()]);
    assert_eq!(
        derives("ConnectionUsage", "targetFeature"),
        Derives::Passthrough
    );
    // Another property of the same name on an expression is not this one
    // (the accessed feature, exact).
    assert_eq!(
        derives("FeatureChainExpression", "targetFeature"),
        Derives::Exact
    );
    let f = elem(&mut r, "P::f");
    let flow_ends = many(&mut r, f, "flowEnd");
    assert_eq!(flow_ends.len(), 2);
    assert!(flow_ends.iter().all(|&e| r.element_type(e) == "FlowEnd"));
    let out = one(&mut r, f, "sourceOutputFeature").expect("source output feature");
    let inp = one(&mut r, f, "targetInputFeature").expect("target input feature");
    assert_eq!(one(&mut r, out, "owningType"), Some(flow_ends[0]));
    assert_eq!(one(&mut r, inp, "owningType"), Some(flow_ends[1]));
}

/// `member` lists a non-owning membership's unresolved target by its
/// spelling; `qualifiedName` needs every owner named.
#[test]
fn members_and_qualified_names_through_unnamed_owners() {
    let mut r = build(
        "package P {
            alias thing for Nope::thing;
            part { part child; }
        }",
    );
    let p = elem(&mut r, "P");
    assert!(refs(&mut r, p, "member").contains(&Reference::Unresolved("Nope::thing".to_string())));
    let child = r
        .elements_of_metaclass("PartUsage")
        .into_iter()
        .find(|&e| r.element_name(e) == Some("child"))
        .expect("child");
    assert_eq!(string(&mut r, child, "name").as_deref(), Some("child"));
    assert_eq!(string(&mut r, child, "qualifiedName"), None);
}

// ---- M33f: behavior, expression, requirement and view structure ----

/// States and transitions: the sub-actions by membership kind; the
/// transition's trigger, guard, effect, succession, source and target.
#[test]
fn state_and_transition_structure() {
    let mut r = build(
        "package P {
            item def Signal;
            state def Machine {
                entry action e1;
                do action d1;
                exit action x1;
                state s1;
                state s2 { entry action inner; }
                transition t1 first s1 accept sig : Signal if true do action eff then s2;
                transition t2 first s2 then s1;
            }
        }",
    );
    let m = elem(&mut r, "P::Machine");
    let e1 = elem(&mut r, "P::Machine::e1");
    let d1 = elem(&mut r, "P::Machine::d1");
    let x1 = elem(&mut r, "P::Machine::x1");
    assert_eq!(one(&mut r, m, "entryAction"), Some(e1));
    assert_eq!(one(&mut r, m, "doAction"), Some(d1));
    assert_eq!(one(&mut r, m, "exitAction"), Some(x1));
    let s2 = elem(&mut r, "P::Machine::s2");
    assert_eq!(one(&mut r, s2, "doAction"), None);
    assert!(one(&mut r, s2, "entryAction").is_some());
    // The membership-side `action` is the owned member.
    let entry_membership = many(&mut r, m, "ownedFeatureMembership")
        .into_iter()
        .find(|&fm| r.element_type(fm) == "StateSubactionMembership")
        .expect("state subaction membership");
    assert_eq!(one(&mut r, entry_membership, "action"), Some(e1));
    assert_eq!(
        derives("StateSubactionMembership", "action"),
        Derives::Exact
    );
    let t1 = elem(&mut r, "P::Machine::t1");
    let s1 = elem(&mut r, "P::Machine::s1");
    let triggers = many(&mut r, t1, "triggerAction");
    assert_eq!(triggers.len(), 1);
    assert_eq!(r.element_type(triggers[0]), "AcceptActionUsage");
    let guards = many(&mut r, t1, "guardExpression");
    assert_eq!(guards.len(), 1);
    assert!(
        r.element_type(guards[0]).ends_with("Boolean")
            || r.element_type(guards[0]).contains("Expression")
    );
    let effects = many(&mut r, t1, "effectAction");
    assert_eq!(names(&mut r, &effects), vec!["eff"]);
    let succession = one(&mut r, t1, "succession").expect("succession");
    assert_eq!(r.element_type(succession), "SuccessionAsUsage");
    assert_eq!(one(&mut r, t1, "source"), Some(s1));
    assert_eq!(one(&mut r, t1, "target"), Some(s2));
    // The transition-feature membership's own reference.
    let tfm = many(&mut r, t1, "ownedFeatureMembership")
        .into_iter()
        .find(|&fm| r.element_type(fm) == "TransitionFeatureMembership")
        .expect("transition feature membership");
    assert_eq!(one(&mut r, tfm, "transitionFeature"), Some(triggers[0]));
    let t2 = elem(&mut r, "P::Machine::t2");
    assert_eq!(many(&mut r, t2, "triggerAction"), Vec::new());
    assert_eq!(one(&mut r, t2, "source"), Some(s2));
    assert_eq!(one(&mut r, t2, "target"), Some(s1));
}

/// Control and communication actions: arguments and bodies by input
/// parameter position, per the specification's `inputParameter(i)` /
/// `argument(i)` with the parameter-membership default direction.
#[test]
fn control_and_communication_actions() {
    let mut r = build(
        "package P {
            item def Msg;
            attribute x : Boolean;
            part def Peer { port p; }
            part peer : Peer;
            action def A {
                action i1 if x { action thenA; } else { action elseA; }
                action w1 while x { action bodyW; } until x;
                action f1 for i in 1..3 { action bodyF; }
                action s1 send 1 via peer.p to peer;
                action a1 accept m : Msg via peer.p;
                action g1 assign x := true;
                action k1 terminate peer;
            }
        }",
    );
    let i1 = elem(&mut r, "P::A::i1");
    let cond = one(&mut r, i1, "ifArgument").expect("if argument");
    assert!(r.element_type(cond).contains("Expression"));
    let then_a = one(&mut r, i1, "thenAction").expect("then");
    assert_eq!(r.element_type(then_a), "ActionUsage");
    let else_a = one(&mut r, i1, "elseAction").expect("else");
    assert_ne!(then_a, else_a);
    let w1 = elem(&mut r, "P::A::w1");
    assert!(one(&mut r, w1, "whileArgument").is_some());
    assert!(one(&mut r, w1, "bodyAction").is_some());
    assert!(one(&mut r, w1, "untilArgument").is_some());
    let f1 = elem(&mut r, "P::A::f1");
    let var = one(&mut r, f1, "loopVariable").expect("loop variable");
    assert_eq!(r.element_name(var), Some("i"));
    let seq = one(&mut r, f1, "seqArgument").expect("sequence");
    assert!(r.element_type(seq).contains("Expression"));
    assert!(one(&mut r, f1, "bodyAction").is_some());
    let s1 = elem(&mut r, "P::A::s1");
    assert!(one(&mut r, s1, "payloadArgument").is_some());
    assert!(one(&mut r, s1, "senderArgument").is_some());
    assert!(one(&mut r, s1, "receiverArgument").is_some());
    let a1 = elem(&mut r, "P::A::a1");
    let payload = one(&mut r, a1, "payloadParameter").expect("payload parameter");
    assert_eq!(r.element_name(payload), Some("m"));
    assert_eq!(one(&mut r, a1, "payloadArgument"), None);
    assert!(one(&mut r, a1, "receiverArgument").is_some());
    let g1 = elem(&mut r, "P::A::g1");
    assert!(one(&mut r, g1, "targetArgument").is_some());
    assert!(one(&mut r, g1, "valueExpression").is_some());
    let k1 = elem(&mut r, "P::A::k1");
    assert!(one(&mut r, k1, "terminatedOccurrenceArgument").is_some());
    // Positions are exact: an unspelled direction counts as `in`.
    assert_eq!(derives("IfActionUsage", "thenAction"), Derives::Exact);
    assert_eq!(
        derives("SendActionUsage", "receiverArgument"),
        Derives::Exact
    );
}

/// References through subsetting: perform/exhibit/include/event
/// dereference to the chain target, else the usage itself; expressions
/// know their result, function, instantiated type, arguments and
/// referents; multiplicity ranges their bounds.
#[test]
fn perform_and_expression_structure() {
    let mut r = build(
        "package P {
            action def A { in p; in q; return : Real; }
            action a : A;
            part def Car { action drive; }
            part car : Car;
            action def Use {
                perform action pa ::> car.drive;
                perform action lone;
                action computed = A(1, 2);
                action named = A(q = 2, p = 1);
            }
            calc def F { in n; return : Real; }
            attribute v = F(3);
            attribute w = v.x;
            part items[2..5];
            part one[1];
            use case def U { include use case inc; }
        }",
    );
    let pa = elem(&mut r, "P::Use::pa");
    let drive = elem(&mut r, "P::Car::drive");
    assert_eq!(one(&mut r, pa, "performedAction"), Some(drive));
    assert_eq!(one(&mut r, pa, "eventOccurrence"), Some(drive));
    let lone = elem(&mut r, "P::Use::lone");
    assert_eq!(one(&mut r, lone, "performedAction"), Some(lone));
    let u = elem(&mut r, "P::U");
    let inc = elem(&mut r, "P::U::inc");
    assert_eq!(many(&mut r, u, "includedUseCase"), vec![inc]);
    // Functions and expressions.
    let f = elem(&mut r, "P::F");
    let ret = one(&mut r, f, "result").expect("return parameter");
    assert_eq!(string(&mut r, ret, "name").as_deref(), Some("result"));
    assert_eq!(derives("Function", "result"), Derives::Passthrough);
    let v = elem(&mut r, "P::v");
    let invocation = many(&mut r, v, "ownedElement")
        .into_iter()
        .find(|&e| r.element_type(e) == "InvocationExpression")
        .expect("invocation");
    assert_eq!(one(&mut r, invocation, "instantiatedType"), Some(f));
    assert_eq!(one(&mut r, invocation, "result"), None);
    let args = many(&mut r, invocation, "argument");
    assert_eq!(args.len(), 1);
    assert_eq!(r.element_type(args[0]), "LiteralInteger");
    // Named arguments are matched by the callee's parameter, not position.
    let named = elem(&mut r, "P::Use::named");
    let call = many(&mut r, named, "ownedElement")
        .into_iter()
        .find(|&e| r.element_type(e) == "InvocationExpression")
        .expect("invocation");
    let args = many(&mut r, call, "argument");
    let literals: Vec<String> = args
        .iter()
        .map(|&a| {
            r.element_properties(a)
                .get("value")
                .map(|v| v.to_string())
                .unwrap_or_default()
        })
        .collect();
    assert_eq!(literals, vec!["1", "2"]);
    // A feature reference expression's referent, a chain expression's
    // target feature.
    let w = elem(&mut r, "P::w");
    let chain = many(&mut r, w, "ownedElement")
        .into_iter()
        .find(|&e| r.element_type(e) == "FeatureChainExpression")
        .expect("chain expression");
    assert!(refs(&mut r, chain, "targetFeature").len() == 1);
    assert_eq!(
        derives("FeatureChainExpression", "targetFeature"),
        Derives::Exact
    );
    // Multiplicity bounds.
    let items = elem(&mut r, "P::items");
    let range = one(&mut r, items, "multiplicity").expect("range");
    let bounds = many(&mut r, range, "bound");
    assert_eq!(bounds.len(), 2);
    assert_eq!(one(&mut r, range, "lowerBound"), Some(bounds[0]));
    assert_eq!(one(&mut r, range, "upperBound"), Some(bounds[1]));
    let one_ = elem(&mut r, "P::one");
    let range = one(&mut r, one_, "multiplicity").expect("range");
    assert_eq!(one(&mut r, range, "lowerBound"), None);
    assert!(one(&mut r, range, "upperBound").is_some());
    // Feature values.
    let fv = r
        .owned_relationships(v)
        .into_iter()
        .find(|&e| r.element_type(e) == "FeatureValue")
        .expect("feature value");
    assert_eq!(one(&mut r, fv, "featureWithValue"), Some(v));
    assert_eq!(one(&mut r, fv, "value"), Some(invocation));
}

/// Requirements, cases and views: subjects, actors, stakeholders,
/// objectives, required and assumed constraints, framed concerns,
/// verified and satisfied requirements, renderings and conditions.
#[test]
fn requirement_case_and_view_structure() {
    let mut r = build(
        "package P {
            part def Vehicle;
            part def Person;
            concern def Safety { stakeholder driver : Person; }
            requirement def R {
                subject v : Vehicle;
                actor user : Person;
                stakeholder owner : Person;
                require constraint c1 { true }
                assume constraint c2 { true }
                frame concern sf : Safety;
            }
            requirement r1 : R;
            part car : Vehicle { satisfy r1 by car; }
            verification def V {
                objective { verify r1; }
            }
            rendering def Tree;
            rendering asTree : Tree;
            view def VD { render asTree; filter @Safety; }
            view v1 : VD { expose P::*; }
            package Q { filter @Safety; }
            viewpoint def VP { frame concern sfv : Safety; }
        }",
    );
    let rd = elem(&mut r, "P::R");
    let v = elem(&mut r, "P::R::v");
    let user = elem(&mut r, "P::R::user");
    let owner = elem(&mut r, "P::R::owner");
    let c1 = elem(&mut r, "P::R::c1");
    let c2 = elem(&mut r, "P::R::c2");
    let sf = elem(&mut r, "P::R::sf");
    assert_eq!(one(&mut r, rd, "subjectParameter"), Some(v));
    assert_eq!(many(&mut r, rd, "actorParameter"), vec![user]);
    assert_eq!(many(&mut r, rd, "stakeholderParameter"), vec![owner]);
    // Framed concerns are required constraints (FramedConcernMembership
    // is a RequirementConstraintMembership of kind requirement).
    assert_eq!(many(&mut r, rd, "requiredConstraint"), vec![c1, sf]);
    assert_eq!(many(&mut r, rd, "assumedConstraint"), vec![c2]);
    assert_eq!(many(&mut r, rd, "framedConcern"), vec![sf]);
    assert_eq!(
        derives("RequirementDefinition", "requiredConstraint"),
        Derives::Exact
    );
    assert_eq!(
        derives("RequirementDefinition", "framedConcern"),
        Derives::Passthrough
    );
    // The membership-side references.
    let memberships = many(&mut r, rd, "ownedFeatureMembership");
    let subject_m = memberships
        .iter()
        .copied()
        .find(|&m| r.element_type(m) == "SubjectMembership")
        .unwrap();
    assert_eq!(one(&mut r, subject_m, "ownedSubjectParameter"), Some(v));
    let constraint_m = memberships
        .iter()
        .copied()
        .find(|&m| r.element_type(m) == "RequirementConstraintMembership")
        .unwrap();
    assert_eq!(one(&mut r, constraint_m, "ownedConstraint"), Some(c1));
    assert_eq!(one(&mut r, constraint_m, "referencedConstraint"), Some(c1));
    let concern_m = memberships
        .iter()
        .copied()
        .find(|&m| r.element_type(m) == "FramedConcernMembership")
        .unwrap();
    assert_eq!(one(&mut r, concern_m, "referencedConcern"), Some(sf));
    // Satisfaction and verification.
    let r1 = elem(&mut r, "P::r1");
    let car = elem(&mut r, "P::car");
    let satisfy = many(&mut r, car, "ownedFeature")
        .into_iter()
        .find(|&f| r.element_type(f) == "SatisfyRequirementUsage")
        .expect("satisfy");
    assert_eq!(one(&mut r, satisfy, "satisfiedRequirement"), Some(r1));
    assert_eq!(one(&mut r, satisfy, "assertedConstraint"), Some(r1));
    assert_eq!(one(&mut r, satisfy, "satisfyingFeature"), Some(car));
    let vd = elem(&mut r, "P::V");
    let objective = one(&mut r, vd, "objectiveRequirement").expect("objective");
    assert_eq!(r.element_type(objective), "RequirementUsage");
    assert_eq!(many(&mut r, vd, "verifiedRequirement"), vec![r1]);
    let verification_m = many(&mut r, objective, "ownedFeatureMembership")
        .into_iter()
        .find(|&m| r.element_type(m) == "RequirementVerificationMembership")
        .expect("verification membership");
    assert_eq!(one(&mut r, verification_m, "verifiedRequirement"), Some(r1));
    assert_eq!(
        derives("RequirementVerificationMembership", "verifiedRequirement"),
        Derives::Exact
    );
    // Views.
    let view_def = elem(&mut r, "P::VD");
    let as_tree = elem(&mut r, "P::asTree");
    assert_eq!(one(&mut r, view_def, "viewRendering"), Some(as_tree));
    let rendering_m = many(&mut r, view_def, "ownedFeatureMembership")
        .into_iter()
        .find(|&m| r.element_type(m) == "ViewRenderingMembership")
        .expect("rendering membership");
    assert_eq!(
        one(&mut r, rendering_m, "referencedRendering"),
        Some(as_tree)
    );
    assert_eq!(many(&mut r, view_def, "viewCondition").len(), 1);
    let q = elem(&mut r, "P::Q");
    let conditions = many(&mut r, q, "filterCondition");
    assert_eq!(conditions.len(), 1);
    let filter_m = many(&mut r, q, "ownedMembership")
        .into_iter()
        .find(|&m| r.element_type(m) == "ElementFilterMembership")
        .expect("filter membership");
    assert_eq!(one(&mut r, filter_m, "condition"), Some(conditions[0]));
    let v1 = elem(&mut r, "P::v1");
    let exposed = many(&mut r, v1, "exposedElement");
    assert!(exposed.contains(&car));
    let vp = elem(&mut r, "P::VP");
    let sfv = elem(&mut r, "P::VP::sfv");
    assert_eq!(many(&mut r, vp, "framedConcern"), vec![sfv]);
}

/// Membership identity strings and the typing residue: member ids and
/// names, enumerated values, conjugation, association ends, payload
/// types, individual definitions.
#[test]
fn membership_strings_and_typing_residue() {
    let mut r = build(
        "package P {
            enum def Color { red; <g> green; }
            port def Pt;
            part def Node { port in_ : Pt; port out_ : ~Pt; }
            connection def Link { end part a : Node; end part b : Node; }
            individual part def Earth :> Node;
            part earth : Earth;
            alias colour for Color;
        }",
    );
    let p = elem(&mut r, "P");
    let color = elem(&mut r, "P::Color");
    let red = elem(&mut r, "P::Color::red");
    let green = elem(&mut r, "P::Color::green");
    assert_eq!(many(&mut r, color, "enumeratedValue"), vec![red, green]);
    let memberships = many(&mut r, p, "ownedMembership");
    let color_m = memberships
        .iter()
        .copied()
        .find(|&m| one(&mut r, m, "ownedMemberElement") == Some(color))
        .unwrap();
    assert_eq!(
        string(&mut r, color_m, "ownedMemberElementId"),
        Some(r.element_id(color).to_string())
    );
    assert_eq!(
        string(&mut r, color_m, "memberElementId"),
        Some(r.element_id(color).to_string())
    );
    assert_eq!(
        string(&mut r, color_m, "ownedMemberName").as_deref(),
        Some("Color")
    );
    assert_eq!(string(&mut r, color_m, "ownedMemberShortName"), None);
    let alias = memberships
        .iter()
        .copied()
        .find(|&m| r.membership_is_alias(m))
        .unwrap();
    assert_eq!(
        string(&mut r, alias, "memberElementId"),
        Some(r.element_id(color).to_string())
    );
    let green_m = many(&mut r, color, "ownedMembership")
        .into_iter()
        .find(|&m| one(&mut r, m, "ownedVariantUsage") == Some(green))
        .expect("variant membership");
    assert_eq!(
        string(&mut r, green_m, "ownedMemberShortName").as_deref(),
        Some("g")
    );
    // Conjugation.
    let pt = elem(&mut r, "P::Pt");
    let conj = one(&mut r, pt, "conjugatedPortDefinition").expect("conjugated definition");
    assert_eq!(r.element_type(conj), "ConjugatedPortDefinition");
    assert!(matches!(
        r.derived(conj, "isConjugated"),
        Derived::Value(DerivedValue::Bool(true))
    ));
    assert!(matches!(
        r.derived(pt, "isConjugated"),
        Derived::Value(DerivedValue::Bool(false))
    ));
    let conjugator = one(&mut r, conj, "ownedPortConjugator").expect("port conjugation");
    assert_eq!(
        one(&mut r, conjugator, "conjugatedPortDefinition"),
        Some(conj)
    );
    // Association ends.
    let link = elem(&mut r, "P::Link");
    let ends = many(&mut r, link, "connectionEnd");
    assert_eq!(ends.len(), 2);
    assert_eq!(many(&mut r, link, "associationEnd"), ends);
    // Individual definitions.
    let earth = elem(&mut r, "P::earth");
    let earth_def = elem(&mut r, "P::Earth");
    assert_eq!(one(&mut r, earth, "individualDefinition"), Some(earth_def));
}

/// A kind test on a target outside the model passes: the reference is
/// reported as it is rather than dropped (the typing constraints of a
/// well-formed model make the test hold wherever it resolved).
#[test]
fn kind_tests_pass_unknowable_targets() {
    let mut r = build(
        "package P {
            attribute m : Real;
            part p : Lib::Part;
            action perform_it { perform Lib::doIt; }
        }",
    );
    let m = elem(&mut r, "P::m");
    assert_eq!(
        refs(&mut r, m, "definition"),
        vec![Reference::Unresolved("Real".to_string())]
    );
    assert_eq!(
        refs(&mut r, m, "attributeDefinition"),
        vec![Reference::Unresolved("Real".to_string())]
    );
    let p = elem(&mut r, "P::p");
    assert_eq!(
        refs(&mut r, p, "partDefinition"),
        vec![Reference::Unresolved("Lib::Part".to_string())]
    );
    let act = elem(&mut r, "P::perform_it");
    let perform = many(&mut r, act, "ownedFeature")
        .into_iter()
        .find(|&f| r.element_type(f) == "PerformActionUsage")
        .expect("perform");
    assert_eq!(
        refs(&mut r, perform, "performedAction"),
        vec![Reference::Unresolved("Lib::doIt".to_string())]
    );
}

/// Review follow-ups: an accept's trigger is not an input parameter and
/// stands in for the payload argument; a trigger invocation's
/// instantiated type and argument; constructor arguments by the type's
/// features; the positional fallback for a callee whose parameters are
/// inherited; the operator function by name table; `input` agrees with
/// `inputParameter(i)`.
#[test]
fn parameters_after_review() {
    let mut r = build(
        "package P {
            item def Msg;
            part def Peer { port p; }
            part peer : Peer;
            part def Car { attribute mass; }
            calc def F { in n; return : Real; }
            calc def G :> F;
            action def A {
                action a2 accept m : Msg at 1 via peer.p;
                action i1 if true { action thenA; }
            }
            attribute c = new Car(mass = 1);
            attribute g = G(3);
            attribute s = 1 + 2;
            alias thing for Nope::thing;
            part e : Lib::Earth;
        }",
    );
    // The accept: the trigger is not counted, so `via` is the receiver.
    let a2 = elem(&mut r, "P::A::a2");
    let receiver = one(&mut r, a2, "receiverArgument").expect("receiver");
    assert!(r.element_type(receiver).contains("Expression"));
    let trigger = one(&mut r, a2, "payloadArgument").expect("trigger as payload argument");
    assert_eq!(r.element_type(trigger), "TriggerInvocationExpression");
    let inputs = many(&mut r, a2, "input");
    assert!(
        inputs
            .iter()
            .all(|&f| r.element_type(f) != "TriggerInvocationExpression")
    );
    assert_eq!(inputs.len(), 2);
    // The trigger's own argument and instantiated type.
    let args = many(&mut r, trigger, "argument");
    assert_eq!(args.len(), 1);
    assert_eq!(r.element_type(args[0]), "LiteralInteger");
    assert_eq!(refs(&mut r, trigger, "instantiatedType"), Vec::new());
    // `input` on an if node agrees with `ifArgument`/`thenAction`.
    let i1 = elem(&mut r, "P::A::i1");
    let inputs = many(&mut r, i1, "input");
    assert_eq!(inputs.len(), 2);
    assert_eq!(one(&mut r, i1, "thenAction"), Some(inputs[1]));
    assert_eq!(many(&mut r, i1, "parameter"), inputs);
    // A constructor's arguments follow the type's features.
    let c = elem(&mut r, "P::c");
    let ctor = many(&mut r, c, "ownedElement")
        .into_iter()
        .find(|&x| r.element_type(x) == "ConstructorExpression")
        .expect("constructor");
    let args = many(&mut r, ctor, "argument");
    assert_eq!(args.len(), 1);
    assert_eq!(r.element_type(args[0]), "LiteralInteger");
    // A callee whose parameters are inherited: the positional fallback.
    let g = elem(&mut r, "P::g");
    let call = many(&mut r, g, "ownedElement")
        .into_iter()
        .find(|&x| r.element_type(x) == "InvocationExpression")
        .expect("invocation");
    assert_eq!(many(&mut r, call, "argument").len(), 1);
    assert_eq!(
        derives("InvocationExpression", "argument"),
        Derives::Passthrough
    );
    // An operator's function: null without a library, external through a
    // name table.
    let s = elem(&mut r, "P::s");
    let plus = many(&mut r, s, "ownedElement")
        .into_iter()
        .find(|&x| r.element_type(x) == "OperatorExpression")
        .expect("operator expression");
    assert_eq!(refs(&mut r, plus, "instantiatedType"), Vec::new());
    let plus_id = uuid::Uuid::new_v4();
    let at_id = uuid::Uuid::new_v4();
    let mut names = std::collections::HashMap::new();
    names.insert(
        plus_id.to_string(),
        vec!["DataFunctions".to_string(), "+".to_string()],
    );
    names.insert(
        at_id.to_string(),
        vec!["Triggers".to_string(), "TriggerAt".to_string()],
    );
    r.set_library_names(&names);
    assert_eq!(
        refs(&mut r, plus, "instantiatedType"),
        vec![Reference::External(plus_id)]
    );
    assert_eq!(
        refs(&mut r, trigger, "instantiatedType"),
        vec![Reference::External(at_id)]
    );
    // An unresolved member's id is the dangling id the wire spells; an
    // individual definition outside the model cannot pass its property
    // test.
    let p = elem(&mut r, "P");
    let alias = many(&mut r, p, "ownedMembership")
        .into_iter()
        .find(|&m| r.membership_is_alias(m))
        .expect("alias");
    let expected = uuid::Uuid::new_v5(
        &uuid::Uuid::NAMESPACE_OID,
        "unresolved:Nope::thing".as_bytes(),
    )
    .to_string();
    assert_eq!(string(&mut r, alias, "memberElementId"), Some(expected));
    let e = elem(&mut r, "P::e");
    assert_eq!(refs(&mut r, e, "individualDefinition"), Vec::new());
    // The owned/derived split.
    assert_eq!(derives("Specialization", "source"), Derives::NotDeclared);
    assert!(sysmlv2_parser::json::is_owned_property(
        "Specialization",
        "source"
    ));
    assert!(!sysmlv2_parser::json::is_owned_property(
        "TransitionUsage",
        "source"
    ));
}

/// Chains through the transition, verification and rendering references.
#[test]
fn chained_references_in_behavior_and_cases() {
    let mut r = build(
        "package P {
            requirement def R;
            part sys { requirement r2 : R; }
            state def M {
                state s1;
                state s2 { state inner; }
                transition t3 first s1 then s2.inner;
                transition t4 first s2.inner then s1;
            }
            verification def V { objective { verify sys.r2; verify sys.r2; } }
            rendering def Tree;
            part views { rendering asTree : Tree; }
            view def VD { render views.asTree; }
        }",
    );
    let inner = elem(&mut r, "P::M::s2::inner");
    let s1 = elem(&mut r, "P::M::s1");
    let t3 = elem(&mut r, "P::M::t3");
    assert_eq!(one(&mut r, t3, "source"), Some(s1));
    assert_eq!(one(&mut r, t3, "target"), Some(inner));
    let t4 = elem(&mut r, "P::M::t4");
    assert_eq!(one(&mut r, t4, "source"), Some(inner));
    assert_eq!(one(&mut r, t4, "target"), Some(s1));
    let r2 = elem(&mut r, "P::sys::r2");
    let v = elem(&mut r, "P::V");
    assert_eq!(many(&mut r, v, "verifiedRequirement"), vec![r2]);
    let vd = elem(&mut r, "P::VD");
    let as_tree = elem(&mut r, "P::views::asTree");
    assert_eq!(one(&mut r, vd, "viewRendering"), Some(as_tree));
}

// ---- M33g: type operations, association types, featuring, evaluability ----

/// Unioning, intersecting and differencing types and their relationship
/// ends; an association's related, source and target types.
#[test]
fn type_operations_and_association_types() {
    let mut model = Model::new();
    model.add_source(
        "m.kerml",
        "package P {
            classifier A; classifier B; classifier C;
            classifier U unions A, B;
            classifier I intersects A, B;
            classifier D differences A, B;
            assoc L { end feature a : A; end feature b : B; end feature c : C; }
        }",
    );
    assert!(
        !model.has_errors(),
        "{:?}",
        model
            .units()
            .iter()
            .flat_map(|u| u.diagnostics.iter())
            .collect::<Vec<_>>()
    );
    let mut r = ResolvedModel::build(&model);
    let a = elem(&mut r, "P::A");
    let b = elem(&mut r, "P::B");
    let c = elem(&mut r, "P::C");
    let u = elem(&mut r, "P::U");
    assert_eq!(many(&mut r, u, "unioningType"), vec![a, b]);
    assert_eq!(many(&mut r, u, "intersectingType"), Vec::new());
    let unionings = many(&mut r, u, "ownedUnioning");
    assert_eq!(unionings.len(), 2);
    assert_eq!(one(&mut r, unionings[0], "typeUnioned"), Some(u));
    let i = elem(&mut r, "P::I");
    assert_eq!(many(&mut r, i, "intersectingType"), vec![a, b]);
    let d = elem(&mut r, "P::D");
    assert_eq!(many(&mut r, d, "differencingType"), vec![a, b]);
    let l = elem(&mut r, "P::L");
    assert_eq!(many(&mut r, l, "relatedType"), vec![a, b, c]);
    assert_eq!(one(&mut r, l, "sourceType"), Some(a));
    assert_eq!(many(&mut r, l, "targetType"), vec![b, c]);
    assert_eq!(derives("Association", "relatedType"), Derives::Passthrough);
    assert_eq!(derives("Classifier", "unioningType"), Derives::Exact);
}

/// A connector's default featuring type: the innermost type featuring
/// every related feature, through the owning types of the chains' first
/// links.
#[test]
fn default_featuring_type() {
    let mut r = build(
        "package P {
            part def Wheel { port hub; }
            part def Axle { port end_; }
            part def Car {
                part w : Wheel;
                part ax : Axle;
                connection c1 connect w to ax;
                connection c2 connect w.hub to ax.end_;
                part inner { part x; part y; connection c3 connect x to y; }
            }
            part car : Car;
            connection top connect car.w to car.ax;
        }",
    );
    let car_def = elem(&mut r, "P::Car");
    let c1 = elem(&mut r, "P::Car::c1");
    assert_eq!(one(&mut r, c1, "defaultFeaturingType"), Some(car_def));
    let c2 = elem(&mut r, "P::Car::c2");
    assert_eq!(one(&mut r, c2, "defaultFeaturingType"), Some(car_def));
    let inner = elem(&mut r, "P::Car::inner");
    let c3 = elem(&mut r, "P::Car::inner::c3");
    assert_eq!(one(&mut r, c3, "defaultFeaturingType"), Some(inner));
    // Related features at the top level are featured by nothing in the
    // model: no common featuring type.
    let top = elem(&mut r, "P::top");
    assert_eq!(one(&mut r, top, "defaultFeaturingType"), None);
    assert_eq!(
        derives("ConnectionUsage", "defaultFeaturingType"),
        Derives::Passthrough
    );
}

/// Model-level evaluability: literals and metadata access are evaluable;
/// a reference to an unfeatured feature is; one to a featured feature is
/// not; an invocation is only when its function is a library function.
#[test]
fn model_level_evaluability() {
    let mut r = build(
        "package P {
            attribute a;
            attribute b = a;
            attribute lit = 1;
            part def T { attribute q; attribute rq = q; }
            calc def F { in n; return : Real; }
            attribute call = F(1);
            attribute op = 1 + 2;
            attribute chain = a + b;
        }",
    );
    let evaluable = |r: &mut ResolvedModel, owner: &str| -> bool {
        let e = elem(r, owner);
        let value = r
            .owned_relationships(e)
            .into_iter()
            .find(|&x| r.element_type(x) == "FeatureValue")
            .and_then(|fv| one(r, fv, "value"))
            .expect("value");
        matches!(r.derived(value, "isModelLevelEvaluable"), Derived::Value(DerivedValue::Bool(b)) if b)
    };
    assert!(evaluable(&mut r, "P::lit"));
    assert!(evaluable(&mut r, "P::b"));
    assert!(!evaluable(&mut r, "P::T::rq"));
    assert!(!evaluable(&mut r, "P::call"));
    // Without a library the operator's function is unknown: not evaluable.
    assert!(!evaluable(&mut r, "P::op"));
    // With a name table naming the library function, it is.
    let plus_id = uuid::Uuid::new_v4();
    let mut names = std::collections::HashMap::new();
    names.insert(
        plus_id.to_string(),
        vec!["DataFunctions".to_string(), "+".to_string()],
    );
    r.set_library_names(&names);
    assert!(evaluable(&mut r, "P::op"));
    assert!(evaluable(&mut r, "P::chain"));
    assert_eq!(
        derives("OperatorExpression", "isModelLevelEvaluable"),
        Derives::Passthrough
    );
}

// ---- M33h: the closures and the inheritance-aware switch ----

/// The four closure names answer through the resolver's walks whatever
/// the policy; under the closure policy the inheritance-aware families
/// switch to their specification definition.
#[test]
fn closures_and_the_inheritance_aware_switch() {
    use sysmlv2_parser::json::{ClosurePolicy, derives_under};
    let mut r = build(
        "package P {
            part def V { attribute mass; port p; }
            part def W :> V { attribute extra; }
            package Q { part q; }
            package R { import Q::*; }
            package S { private import Q::*; }
            part def T { import Q::*; attribute own; }
            part def U :> T;
        }",
    );
    let w = elem(&mut r, "P::W");
    let mass = elem(&mut r, "P::V::mass");
    let p = elem(&mut r, "P::V::p");
    let extra = elem(&mut r, "P::W::extra");
    // Passthrough: the families answer the owned side; the closures answer.
    assert_eq!(many(&mut r, w, "feature"), vec![extra]);
    assert_eq!(many(&mut r, w, "inheritedFeature"), vec![mass, p]);
    let inherited = many(&mut r, w, "inheritedMembership");
    assert_eq!(inherited.len(), 2);
    assert!(
        inherited
            .iter()
            .all(|&m| r.element_type(m) == "FeatureMembership")
    );
    assert_eq!(
        many(&mut r, mass, "featuringType"),
        vec![elem(&mut r, "P::V")]
    );
    let rpkg = elem(&mut r, "P::R");
    let q = elem(&mut r, "P::Q::q");
    let imported = many(&mut r, rpkg, "importedMembership");
    assert_eq!(imported.len(), 1);
    assert_eq!(one(&mut r, imported[0], "ownedMemberElement"), Some(q));
    assert_eq!(many(&mut r, rpkg, "membership"), Vec::new());
    assert_eq!(derives("PartDefinition", "feature"), Derives::Passthrough);
    // A private import imports for its owner (it is the re-export through
    // heritage that private excludes).
    let spkg = elem(&mut r, "P::S");
    assert_eq!(many(&mut r, spkg, "importedMembership"), imported);
    // A feature arriving through an import inside a type is a member,
    // not a feature: `feature` selects by membership kind.
    let t = elem(&mut r, "P::T");
    let u = elem(&mut r, "P::U");
    let own = elem(&mut r, "P::T::own");
    // The closure policy.
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: false,
    });
    assert_eq!(many(&mut r, w, "feature"), vec![extra, mass, p]);
    let memberships = many(&mut r, w, "featureMembership");
    assert_eq!(memberships.len(), 3);
    assert_eq!(many(&mut r, w, "ownedFeature"), vec![extra]);
    assert_eq!(many(&mut r, rpkg, "membership"), imported);
    assert_eq!(refs(&mut r, rpkg, "member"), vec![Reference::Element(q)]);
    assert_eq!(many(&mut r, t, "feature"), vec![own]);
    assert!(refs(&mut r, t, "member").contains(&Reference::Element(q)));
    assert_eq!(many(&mut r, u, "feature"), vec![own]);
    assert_eq!(many(&mut r, u, "inheritedFeature"), vec![own]);
    // A Type's membership unions its imported and inherited memberships.
    let u_memberships = many(&mut r, u, "membership");
    assert!(u_memberships.contains(&imported[0]));
    assert!(refs(&mut r, u, "member").contains(&Reference::Element(own)));
    // The written-heritage tier stays passthrough; the closure with the
    // implied heritage is the specification's value, except for the three
    // approximations.
    let written = ClosurePolicy::Closure {
        include_implied: false,
    };
    let full = ClosurePolicy::Closure {
        include_implied: true,
    };
    assert_eq!(
        derives_under("PartDefinition", "feature", written),
        Derives::Passthrough
    );
    assert_eq!(
        derives_under("PartDefinition", "feature", full),
        Derives::Exact
    );
    assert_eq!(
        derives_under("PartDefinition", "inheritedMembership", full),
        Derives::Exact
    );
    assert_eq!(
        derives_under("OperatorExpression", "isModelLevelEvaluable", full),
        Derives::Passthrough
    );
    // Without a library the implied heritage adds nothing.
    r.set_closure_policy(full);
    assert_eq!(many(&mut r, w, "feature"), vec![extra, mass, p]);
    r.set_closure_policy(written);
    assert!(!r.closure_truncated(w));
    r.set_closure_policy(ClosurePolicy::Passthrough);
    assert_eq!(many(&mut r, w, "feature"), vec![extra]);
}

/// A heritage deeper than the resolver's budget is reported, never
/// presented as a complete closure.
#[test]
fn a_deep_heritage_reports_truncation() {
    use sysmlv2_parser::json::ClosurePolicy;
    let mut src = String::from("package P { part def D0 { attribute a0; }");
    for i in 1..=26 {
        src.push_str(&format!(
            " part def D{i} :> D{} {{ attribute a{i}; }}",
            i - 1
        ));
    }
    src.push('}');
    let mut r = build(&src);
    let deep = elem(&mut r, "P::D26");
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: false,
    });
    assert!(r.closure_truncated(deep));
    let shallow = elem(&mut r, "P::D3");
    assert!(!r.closure_truncated(shallow));
    assert_eq!(many(&mut r, shallow, "feature").len(), 4);
    // The import walk has the same budget.
    let mut src = String::from("package P { package I0 { part x; }");
    for i in 1..=26 {
        src.push_str(&format!(" package I{i} {{ public import I{}::*; }}", i - 1));
    }
    src.push('}');
    let mut r = build(&src);
    let deep = elem(&mut r, "P::I26");
    r.set_closure_policy(ClosurePolicy::Closure {
        include_implied: false,
    });
    assert!(r.closure_truncated(deep));
    let shallow = elem(&mut r, "P::I3");
    assert!(!r.closure_truncated(shallow));
}

/// Review follow-ups for the evaluability walk and the association types.
#[test]
fn evaluability_after_review() {
    let mut r = build(
        "package P {
            part def Car { attribute mass; }
            attribute c = new Car(mass = 1);
            attribute c2 = new Car(mass = F(1));
            calc def F { in n; return : Real = n; }
            calc def G { in n; n + 1 }
            constraint def K { true }
            part p { calc cu : F; constraint k : K; attribute kv = 1; }
            attribute a;
            attribute b = a;
            attribute w = 1 + b;
            attribute call = F(1);
            attribute z = 1 + call;
            connection def L { end part x : Car; end part y : Car; }
        }",
    );
    let value_of = |r: &mut ResolvedModel, owner: &str| -> ElementRef {
        let e = elem(r, owner);
        r.owned_relationships(e)
            .into_iter()
            .find(|&x| r.element_type(x) == "FeatureValue")
            .and_then(|fv| one(r, fv, "value"))
            .expect("value")
    };
    let is_evaluable = |r: &mut ResolvedModel, e: ElementRef| -> bool {
        matches!(r.derived(e, "isModelLevelEvaluable"), Derived::Value(DerivedValue::Bool(b)) if b)
    };
    // A constructor with arguments is evaluable when they are.
    let ctor = value_of(&mut r, "P::c");
    assert_eq!(r.element_type(ctor), "ConstructorExpression");
    assert!(is_evaluable(&mut r, ctor));
    let ctor2 = value_of(&mut r, "P::c2");
    assert!(!is_evaluable(&mut r, ctor2));
    // Calculation and constraint usages never are.
    let cu = elem(&mut r, "P::p::cu");
    assert!(!is_evaluable(&mut r, cu));
    let k = elem(&mut r, "P::p::k");
    assert!(!is_evaluable(&mut r, k));
    // A user function is not a model-level evaluable function.
    let f = elem(&mut r, "P::F");
    assert!(!is_evaluable(&mut r, f));
    let g = elem(&mut r, "P::G");
    assert!(!is_evaluable(&mut r, g));
    // Through the valuation branch, with the library function named.
    let plus_id = uuid::Uuid::new_v4();
    let mut names = std::collections::HashMap::new();
    names.insert(
        plus_id.to_string(),
        vec!["DataFunctions".to_string(), "+".to_string()],
    );
    r.set_library_names(&names);
    let w = value_of(&mut r, "P::w");
    assert!(is_evaluable(&mut r, w));
    let z = value_of(&mut r, "P::z");
    assert!(!is_evaluable(&mut r, z));
    // A binary association over one type relates it twice.
    let l = elem(&mut r, "P::L");
    let car = elem(&mut r, "P::Car");
    assert_eq!(many(&mut r, l, "relatedType"), vec![car, car]);
    assert_eq!(one(&mut r, l, "sourceType"), Some(car));
    assert_eq!(many(&mut r, l, "targetType"), vec![car]);
}

/// `computable_names(metaclass)` is `computed_names()` filtered by the
/// static gate, in the same order, and every name it lists is answered
/// with a value on an element of that metaclass — the memoized plan the
/// full-form emitter iterates agrees with the static answer per name.
#[test]
fn computable_names_are_the_computed_names_the_gate_admits() {
    let mut r = build(
        "package P {
            part def Car { part engine; attribute mass; }
            part car : Car { part :>> engine; }
            calc def Area { in x; return : Real = x; }
            connection def Link { end a; end b; }
        }",
    );
    let mut targets: Vec<ElementRef> = [
        "P",
        "P::Car",
        "P::car",
        "P::car::engine",
        "P::Area",
        "P::Link",
    ]
    .into_iter()
    .map(|qn| elem(&mut r, qn))
    .collect();
    // A membership metaclass reaches the member-side arm through the plan.
    let engine = elem(&mut r, "P::car::engine");
    targets.push(one(&mut r, engine, "owningMembership").expect("owning membership"));
    for e in targets {
        let ty = r.element_type(e);
        let expected: Vec<&str> = computed_names()
            .filter(|n| matches!(derives(ty, n), Derives::Passthrough | Derives::Exact))
            .collect();
        // A runtime spelling of the metaclass reaches the same plan.
        let spelled: String = ty.to_owned();
        let plan = r.computable_names(spelled.as_str());
        assert_eq!(plan.as_ref(), expected.as_slice(), "{ty}");
        for name in plan.iter() {
            assert!(
                matches!(r.derived(e, name), Derived::Value(_)),
                "{ty}::{name} is planned but not answered"
            );
        }
        // Names outside the plan are refused with the static answer.
        for name in computed_names().filter(|n| !plan.contains(n)) {
            let refusal = match derives(ty, name) {
                Derives::NotDeclared => Derived::NotDeclared,
                Derives::NotComputed => Derived::NotComputed,
                admitted => panic!("{ty}::{name} is admitted ({admitted:?}) but not planned"),
            };
            assert_eq!(r.derived(e, name), refusal, "{ty}::{name}");
        }
        // A name outside the derived catalog is declared nowhere.
        assert_eq!(r.derived(e, "noSuchProperty"), Derived::NotDeclared, "{ty}");
        // The plan is the passthrough gate's: a closure policy changes
        // fidelity, never which names are answered.
        r.set_closure_policy(ClosurePolicy::Closure {
            include_implied: true,
        });
        assert_eq!(
            r.computable_names(ty).as_ref(),
            expected.as_slice(),
            "{ty} under closure"
        );
        r.set_closure_policy(ClosurePolicy::Passthrough);
    }
    // A metaclass outside the catalog has no computable names.
    assert!(r.computable_names("NoSuchMetaclass").is_empty());
}
