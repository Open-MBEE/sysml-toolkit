//! Checked Element, Membership, Type and Feature bodies that read names,
//! positions, redefinitions, filter conditions and directions: the naming
//! group of operations and the direction operations, beside the Namespace
//! bodies of `namespaces` and the conformance bodies of `operations`.
use super::{
    OperationError, OperationExecutionSignature,
    namespaces::{self, Membership, blocked, member_name_pair, with_stable_evidence},
};
use crate::{
    json::{
        DerivedValue, ElementRef, Reference, ResolvedModel, Tri,
        direction_proof::{Direction, DirectionFact, authored_direction},
        membership_evidence, semantic_ownership,
        structural_index::StoredStructure,
        type_relations::TypeRelations,
    },
    metaclass::{conforms, is_a},
};
use std::collections::HashSet;

#[derive(Clone, Copy)]
pub(super) enum Body {
    EscapedName,
    Path,
    NamingFeature,
    Distinguishable,
    AllRedefinedFeatures,
    AllRedefinedFeaturesOf,
    RemoveRedefinedFeatures,
    IncludeAsMember,
    IncludeAsExposed,
    DirectionOf,
    DirectionOfExcluding,
    DirectionFor,
}

fn charge(steps: &mut usize, n: usize, effective: &'static str) -> Result<(), OperationError> {
    *steps = steps.saturating_add(n);
    if *steps > crate::eval::MAX_STEPS {
        Err(OperationError::WorkLimit { effective })
    } else {
        Ok(())
    }
}
fn argument_element(argument: &DerivedValue) -> usize {
    match argument {
        DerivedValue::Element(e) | DerivedValue::Reference(Reference::Element(e)) => e.0,
        _ => unreachable!("validated scalar element argument"),
    }
}
fn references(elements: impl IntoIterator<Item = usize>) -> DerivedValue {
    DerivedValue::References(
        elements
            .into_iter()
            .map(|e| Reference::Element(ElementRef(e)))
            .collect(),
    )
}

/// `Element::escapedName()`: the name, else the short name, else null,
/// spelled as a basic name or a quoted restricted name.
fn escaped_name(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    charge(steps, 8, effective)?;
    let incomplete = || blocked(effective, receiver.0);
    let name = match r
        .checked_effective_name_of(receiver.0)
        .ok_or_else(incomplete)?
    {
        Some(name) => Some(name),
        None => r
            .checked_effective_short_name_of(receiver.0)
            .ok_or_else(incomplete)?,
    };
    Ok(match name {
        Some(name) => {
            charge(steps, name.len(), effective)?;
            DerivedValue::Str(sysmlv2_syntax::ast::escape_name(&name))
        }
        None => DerivedValue::Null,
    })
}

/// `Element::path()` and its Relationship and OwningMembership overrides:
/// the qualified name where there is one; else the owning relationship's
/// path and the element's position among its owned related elements;
/// for a relationship owned by its related element, that element's path
/// and the relationship's position among its owned relationships; for an
/// owning membership of a qualified element, that name and
/// `/owningMembership`. Positions count the authored relationships, from
/// one, as the compact form lists them; an element outside that list (a
/// generated or implied row) is refused.
fn path(
    r: &mut ResolvedModel,
    e: usize,
    effective: &'static str,
    depth: usize,
    steps: &mut usize,
) -> Result<String, OperationError> {
    charge(steps, 8, effective)?;
    let incomplete = || blocked(effective, e);
    if depth > crate::json::MAX_RESOLUTION_DEPTH {
        return Err(incomplete());
    }
    let element = &r.b.elements[e];
    if is_a!(element, "OwningMembership") {
        if let Some(&member) = element.children.first() {
            if let Some(segments) = r
                .checked_qualified_name_segments(ElementRef(member))
                .ok_or_else(incomplete)?
            {
                return Ok(format!("{}/owningMembership", spell_qualified(&segments)));
            }
        }
    }
    let element = &r.b.elements[e];
    if is_a!(element, "Relationship") && element.owning_relationship.is_none() {
        r.ensure_rel_owner();
        if let Some(owner) = r.rel_owner[e] {
            let position = r.b.elements[owner]
                .owned_relationships
                .iter()
                .position(|&rel| rel == e)
                .ok_or_else(incomplete)?;
            let prefix = path(r, owner, effective, depth + 1, steps)?;
            return Ok(format!("{prefix}/{}", position + 1));
        }
    }
    if let Some(segments) = r
        .checked_qualified_name_segments(ElementRef(e))
        .ok_or_else(incomplete)?
    {
        return Ok(spell_qualified(&segments));
    }
    let Some(relationship) = r.b.elements[e].owning_relationship else {
        return Ok(String::new());
    };
    let position = r.b.elements[relationship]
        .children
        .iter()
        .position(|&child| child == e)
        .ok_or_else(incomplete)?;
    let prefix = path(r, relationship, effective, depth + 1, steps)?;
    Ok(format!("{prefix}/{}", position + 1))
}
fn spell_qualified(segments: &[String]) -> String {
    segments
        .iter()
        .map(|s| sysmlv2_syntax::ast::escape_name(s))
        .collect::<Vec<_>>()
        .join("::")
}

/// `Feature::namingFeature()` and its SysML overrides, all of which the
/// naming rule of `naming.rs` folds into one derivation: the feature that
/// names an unnamed one, as a model element or an external reference, or
/// null; refused where it cannot be identified.
fn naming_feature(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    charge(steps, 8, effective)?;
    match r.checked_naming_feature(receiver.0) {
        Some(Some(reference)) => Ok(DerivedValue::Reference(reference)),
        Some(None) => Ok(DerivedValue::Null),
        None => Err(blocked(effective, receiver.0)),
    }
}

/// The checked Membership record of `relationship`: its carrier and member.
fn membership(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    relationship: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Membership, OperationError> {
    let incomplete = || blocked(effective, relationship);
    let owner = semantic_ownership::checked_relationship_carrier(&r.b, raw, relationship, steps)
        .flatten()
        .ok_or_else(incomplete)?;
    let member = membership_evidence::member(&r.b, raw, owner, relationship, steps)
        .ok_or_else(incomplete)?;
    Ok(Membership {
        relationship,
        member,
        visibility: namespaces::visibility(r, relationship).ok_or_else(incomplete)?,
    })
}

/// `Membership::isDistinguishableFrom(other)`: the member metaclasses
/// conform to each other in neither direction, or each of this
/// Membership's names, where it has one, differs from both of the other's.
fn distinguishable(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: ElementRef,
    other: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let this = membership(r, raw, receiver.0, effective, steps)?;
    let that = membership(r, raw, other, effective, steps)?;
    let (mine, theirs) = (r.b.elements[this.member].ty, r.b.elements[that.member].ty);
    if !conforms(mine, theirs) && !conforms(theirs, mine) {
        return Ok(DerivedValue::Bool(true));
    }
    let [short, name] = member_name_pair(r, &this, steps, effective)?;
    let others = member_name_pair(r, &that, steps, effective)?;
    let differs = |candidate: &Option<String>| {
        candidate
            .as_ref()
            .is_none_or(|value| others.iter().all(|o| o.as_ref() != Some(value)))
    };
    Ok(DerivedValue::Bool(differs(&short) && differs(&name)))
}

/// `Feature::allRedefinedFeatures()`: the feature and every feature it
/// redefines, directly or transitively.
fn all_redefined_features(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    feature: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let closure = relations.checked_redefinition_closure(&mut r.b, feature, steps);
    charge(steps, 0, effective)?;
    let mut result = vec![feature];
    result.extend(closure.ok_or_else(|| blocked(effective, feature))?);
    Ok(result)
}
/// `Type::allRedefinedFeaturesOf(membership)`: the member's
/// `allRedefinedFeatures()` when it is a Feature, else nothing.
fn all_redefined_features_of(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    relations: &mut TypeRelations,
    relationship: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Vec<usize>, OperationError> {
    let member = membership(r, raw, relationship, effective, steps)?.member;
    if !conforms(r.b.elements[member].ty, "Feature") {
        return Ok(Vec::new());
    }
    all_redefined_features(r, relations, member, effective, steps)
}
/// `Type::removeRedefinedFeatures(memberships)`: the memberships less
/// those whose member another of them redefines, and less those that
/// redefine a feature one of this type's owned features directly
/// redefines.
fn remove_redefined_features(
    r: &mut ResolvedModel,
    raw: &StoredStructure,
    receiver: ElementRef,
    memberships: &[usize],
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let mut relations = TypeRelations::default();
    charge(steps, memberships.len().saturating_mul(4), effective)?;
    let mut members = Vec::with_capacity(memberships.len());
    let mut redefined = Vec::with_capacity(memberships.len());
    for &relationship in memberships {
        let member = membership(r, raw, relationship, effective, steps)?.member;
        members.push(member);
        redefined.push(all_redefined_features_of(
            r,
            raw,
            &mut relations,
            relationship,
            effective,
            steps,
        )?);
    }
    // The features this type's owned features directly redefine.
    let owned =
        namespaces::owned_memberships_of_namespace(&r.b, raw, receiver.0, steps, effective)?;
    let mut owned_redefinitions = HashSet::new();
    for m in owned {
        if !is_a!(r.b.elements[m.relationship], "FeatureMembership")
            || !conforms(r.b.elements[m.member].ty, "Feature")
        {
            continue;
        }
        let direct = relations.direct_redefinitions(&mut r.b, m.member, steps);
        charge(steps, 0, effective)?;
        owned_redefinitions.extend(direct.ok_or_else(|| blocked(effective, m.member))?);
    }
    charge(
        steps,
        memberships.len().saturating_mul(memberships.len()),
        effective,
    )?;
    let mut result = Vec::new();
    for (i, &relationship) in memberships.iter().enumerate() {
        let redefined_by_another = redefined
            .iter()
            .enumerate()
            .any(|(j, features)| j != i && features.contains(&members[i]));
        if redefined_by_another {
            continue;
        }
        if redefined[i]
            .iter()
            .any(|feature| owned_redefinitions.contains(feature))
        {
            continue;
        }
        result.push(relationship);
    }
    Ok(references(result))
}

/// `Package::includeAsMember(element)` and
/// `ViewUsage::includeAsExposed(element)`: every filter condition admits
/// the element — for a package its own `filter` conditions; for a view
/// usage the conditions among its memberships, owned, imported and
/// inherited, as the compatibility exposure projection selects them.
/// A condition the filter evaluator cannot decide refuses.
fn included(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    element: usize,
    exposed: bool,
    effective: &'static str,
    steps: &mut usize,
) -> Result<DerivedValue, OperationError> {
    let incomplete = || blocked(effective, receiver.0);
    charge(steps, 8, effective)?;
    let scope = *r.b.elem_scope.get(&receiver.0).ok_or_else(incomplete)?;
    let filters = if exposed {
        if !r.b.semantic_ready {
            return Err(incomplete());
        }
        let mut context = crate::json::membership_context::MembershipContext::default();
        r.b.exposure_condition_ids(scope, &mut context)
    } else {
        r.b.scopes[scope].filters.clone()
    };
    charge(steps, filters.len().saturating_mul(8), effective)?;
    for filter in filters {
        match r.b.filter_verdict(filter, element, 0) {
            Tri::True => {}
            Tri::False => return Ok(DerivedValue::Bool(false)),
            Tri::Unknown => return Err(incomplete()),
        }
    }
    Ok(DerivedValue::Bool(true))
}

/// `Type::directionOfExcluding(feature, excluded)` (KerML 8.3.3.1.10):
/// the feature's own direction when this type owns it; else the first
/// non-null direction of it relative to a direct base (the complete
/// bases, in order, less the excluded types and this one), flipped
/// between `in` and `out` when this type is conjugated; null when no
/// base gives one.
#[allow(clippy::too_many_arguments)]
fn direction_of_excluding(
    r: &mut ResolvedModel,
    relations: &mut TypeRelations,
    current: usize,
    feature: usize,
    excluded: &HashSet<usize>,
    depth: usize,
    effective: &'static str,
    steps: &mut usize,
) -> Result<Option<Direction>, OperationError> {
    charge(steps, 4, effective)?;
    let incomplete = || blocked(effective, current);
    if depth > crate::json::MAX_RESOLUTION_DEPTH {
        return Err(incomplete());
    }
    let owning_type = relations.owning_type(&mut r.b, feature, steps);
    charge(steps, 0, effective)?;
    if owning_type.ok_or_else(|| blocked(effective, feature))? == Some(current) {
        return match authored_direction(&r.b, feature) {
            DirectionFact::Known(direction) => Ok(direction),
            DirectionFact::Unknown => Err(blocked(effective, feature)),
        };
    }
    let mut excluded_self = excluded.clone();
    excluded_self.insert(current);
    let bases = relations.complete_direct_bases(&mut r.b, current, steps);
    charge(steps, 0, effective)?;
    let bases = bases.ok_or_else(incomplete)?;
    let mut found = None;
    for base in bases {
        if excluded_self.contains(&base) {
            continue;
        }
        if let Some(direction) = direction_of_excluding(
            r,
            relations,
            base,
            feature,
            &excluded_self,
            depth + 1,
            effective,
            steps,
        )? {
            found = Some(direction);
            break;
        }
    }
    let conjugated = relations.owned_conjugation(&mut r.b, current, steps);
    charge(steps, 0, effective)?;
    let conjugated = conjugated.ok_or_else(incomplete)?.is_some();
    Ok(match (found, conjugated) {
        (Some(Direction::In), true) => Some(Direction::Out),
        (Some(Direction::Out), true) => Some(Direction::In),
        (direction, _) => direction,
    })
}
fn direction_value(direction: Option<Direction>) -> DerivedValue {
    match direction {
        Some(Direction::In) => DerivedValue::Str("in".into()),
        Some(Direction::Out) => DerivedValue::Str("out".into()),
        Some(Direction::InOut) => DerivedValue::Str("inout".into()),
        None => DerivedValue::Null,
    }
}

pub(super) fn invoke(
    r: &mut ResolvedModel,
    receiver: ElementRef,
    effective: &'static str,
    _signature: &OperationExecutionSignature,
    arguments: &[DerivedValue],
    body: Body,
    mut steps: usize,
) -> Result<DerivedValue, OperationError> {
    let steps = &mut steps;
    let result = match body {
        Body::EscapedName => escaped_name(r, receiver, effective, steps),
        Body::Path => path(r, receiver.0, effective, 0, steps).map(DerivedValue::Str),
        Body::NamingFeature => naming_feature(r, receiver, effective, steps),
        Body::IncludeAsMember | Body::IncludeAsExposed => included(
            r,
            receiver,
            argument_element(&arguments[0]),
            matches!(body, Body::IncludeAsExposed),
            effective,
            steps,
        ),
        Body::AllRedefinedFeatures => {
            let mut relations = TypeRelations::default();
            all_redefined_features(r, &mut relations, receiver.0, effective, steps).map(references)
        }
        Body::DirectionOf | Body::DirectionOfExcluding | Body::DirectionFor => {
            let mut relations = TypeRelations::default();
            let (owner, feature, excluded) = match body {
                Body::DirectionFor => (argument_element(&arguments[0]), receiver.0, Vec::new()),
                Body::DirectionOf => (receiver.0, argument_element(&arguments[0]), Vec::new()),
                _ => (
                    receiver.0,
                    argument_element(&arguments[0]),
                    namespaces::imports::exclusions(&arguments[1]),
                ),
            };
            direction_of_excluding(
                r,
                &mut relations,
                owner,
                feature,
                &excluded.into_iter().collect(),
                0,
                effective,
                steps,
            )
            .map(direction_value)
        }
        Body::Distinguishable | Body::AllRedefinedFeaturesOf | Body::RemoveRedefinedFeatures => {
            with_stable_evidence(r, receiver, steps, effective, |r, raw, steps| match body {
                Body::Distinguishable => distinguishable(
                    r,
                    raw,
                    receiver,
                    argument_element(&arguments[0]),
                    effective,
                    steps,
                ),
                Body::AllRedefinedFeaturesOf => all_redefined_features_of(
                    r,
                    raw,
                    &mut TypeRelations::default(),
                    argument_element(&arguments[0]),
                    effective,
                    steps,
                )
                .map(references),
                _ => {
                    let memberships = namespaces::imports::exclusions(&arguments[0]);
                    remove_redefined_features(r, raw, receiver, &memberships, effective, steps)
                }
            })
            .map(|(_, _, value)| value)
        }
    };
    if *steps > crate::eval::MAX_STEPS {
        Err(OperationError::WorkLimit { effective })
    } else {
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;
    const KERNEL: &str = "standard library package Base { classifier Anything; datatype DataValue specializes Anything; feature things : Anything; }
         standard library package Occurrences { class Occurrence specializes Base::Anything; feature occurrences : Occurrence subsets Base::things; }
         standard library package Objects { struct Object specializes Occurrences::Occurrence; feature objects : Object subsets Occurrences::occurrences; }
         standard library package Performances { behavior Performance specializes Occurrences::Occurrence; function Evaluation specializes Performance { return result; } step performances : Performance subsets Occurrences::occurrences; expr evaluations : Evaluation subsets performances; }";
    fn fixture(name: &str, source: &str) -> ResolvedModel {
        let mut model = Model::new();
        assert!(
            model
                .add_library_source("kernel.kerml", KERNEL)
                .diagnostics
                .is_empty()
        );
        let unit = model.add_source(name, source);
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        ResolvedModel::build(&model)
    }
    fn call(
        r: &mut ResolvedModel,
        receiver: ElementRef,
        operation: &str,
        arguments: &[DerivedValue],
    ) -> Result<DerivedValue, OperationError> {
        r.invoke_operation(receiver, operation, arguments)
            .map(|v| v.value)
    }
    fn at(r: &mut ResolvedModel, name: &str) -> ElementRef {
        r.resolve_qualified(name).unwrap()
    }
    fn membership_of(r: &mut ResolvedModel, name: &str) -> ElementRef {
        let e = at(r, name);
        ElementRef(r.b.elements[e.0].owning_relationship.unwrap())
    }
    fn str(value: &str) -> DerivedValue {
        DerivedValue::Str(value.into())
    }
    fn names(r: &mut ResolvedModel, value: DerivedValue) -> Vec<String> {
        let DerivedValue::References(refs) = value else {
            panic!("{value:?}")
        };
        refs.into_iter()
            .map(|reference| match reference {
                Reference::Element(e) => r
                    .element_qualified_name(e)
                    .unwrap_or_else(|| r.element_type(e).to_owned()),
                other => panic!("{other:?}"),
            })
            .collect()
    }
    /// The unnamed feature `owner` owns at `index` among its unnamed
    /// features (through a FeatureMembership in a type, an OwningMembership
    /// in a package).
    fn unnamed_feature(r: &mut ResolvedModel, owner: &str, index: usize) -> ElementRef {
        let owner = at(r, owner);
        let features: Vec<_> = r.b.elements[owner.0]
            .owned_relationships
            .iter()
            .filter(|&&m| is_a!(r.b.elements[m], "OwningMembership"))
            .map(|&m| ElementRef(r.b.elements[m].children[0]))
            .filter(|&f| {
                conforms(r.element_type(f), "Feature")
                    && ["declaredName", "declaredShortName"]
                        .iter()
                        .all(|key| r.b.elements[f.0].props.get(key).is_none_or(|v| v.is_null()))
            })
            .collect();
        features[index]
    }

    #[test]
    fn escaped_names_and_paths_follow_the_specification_text() {
        let mut r = fixture(
            "names.kerml",
            "package P { class A; class 'Odd Name'; feature <s>; feature : A; class B specializes A { feature :>> 'Odd Name'; } }",
        );
        const ESCAPED: &str = "Root-Elements-Element-escapedName_";
        const PATH: &str = "Root-Elements-Element-path_";
        let a = at(&mut r, "P::A");
        let odd = at(&mut r, "P::'Odd Name'");
        let s = at(&mut r, "P::s");
        assert_eq!(call(&mut r, a, ESCAPED, &[]).unwrap(), str("A"));
        assert_eq!(call(&mut r, odd, ESCAPED, &[]).unwrap(), str("'Odd Name'"));
        assert_eq!(call(&mut r, s, ESCAPED, &[]).unwrap(), str("s"));
        let anonymous = unnamed_feature(&mut r, "P", 0);
        assert_eq!(
            call(&mut r, anonymous, ESCAPED, &[]).unwrap(),
            DerivedValue::Null
        );
        // Paths: the qualified name where there is one.
        let p = at(&mut r, "P");
        assert_eq!(call(&mut r, p, PATH, &[]).unwrap(), str("P"));
        assert_eq!(call(&mut r, odd, PATH, &[]).unwrap(), str("P::'Odd Name'"));
        // An owning membership of a qualified element.
        let membership = membership_of(&mut r, "P::A");
        let answer = r.invoke_operation(membership, PATH, &[]).unwrap();
        assert_eq!(answer.effective, "Root-Namespaces-OwningMembership-path_");
        assert_eq!(answer.value, str("P::A/owningMembership"));
        // An unnamed element: positions, from one, through its membership —
        // the fourth owned relationship of P, whose first related element it
        // is. The membership's own override applies and, its member having
        // no qualified name, falls through to the Relationship body.
        let feature_membership = ElementRef(r.b.elements[anonymous.0].owning_relationship.unwrap());
        let answer = r.invoke_operation(feature_membership, PATH, &[]).unwrap();
        assert_eq!(answer.effective, "Root-Namespaces-OwningMembership-path_");
        assert_eq!(answer.value, str("P/4"));
        assert_eq!(call(&mut r, anonymous, PATH, &[]).unwrap(), str("P/4/1"));
        // A root-level element's owning membership: its qualified name.
        let root = ElementRef(r.b.elements[p.0].owning_relationship.unwrap());
        assert_eq!(
            call(&mut r, root, PATH, &[]).unwrap(),
            str("P/owningMembership")
        );
    }

    #[test]
    fn naming_feature_is_the_first_redefinition_target_or_null() {
        let mut r = fixture(
            "naming.kerml",
            "class A { feature x; feature y; } class B specializes A { feature :>> x; feature named :>> y; feature plain; feature :>> missing; }",
        );
        const NAMING: &str = "Core-Features-Feature-namingFeature_";
        let x = at(&mut r, "A::x");
        let y = at(&mut r, "A::y");
        let bx = at(&mut r, "B::x");
        assert_eq!(
            call(&mut r, bx, NAMING, &[]).unwrap(),
            DerivedValue::Reference(Reference::Element(x))
        );
        // Declaring a name does not change the naming feature.
        let named = at(&mut r, "B::named");
        assert_eq!(
            call(&mut r, named, NAMING, &[]).unwrap(),
            DerivedValue::Reference(Reference::Element(y))
        );
        let plain = at(&mut r, "B::plain");
        assert_eq!(
            call(&mut r, plain, NAMING, &[]).unwrap(),
            DerivedValue::Null
        );
        let unknown = unnamed_feature(&mut r, "B", 1);
        assert!(matches!(
            call(&mut r, unknown, NAMING, &[]),
            Err(OperationError::Incomplete { blocker: Some(blocker), .. }) if blocker == unknown
        ));
    }

    #[test]
    fn distinguishability_compares_names_and_member_metaclasses() {
        let mut r = fixture(
            "distinct.kerml",
            "package P { class A; feature a; } package Q { class A; class <a> Other; feature nameless; } package R { feature : P::A; }",
        );
        const DISTINCT: &str = "Root-Namespaces-Membership-isDistinguishableFrom_Membership";
        let pa = membership_of(&mut r, "P::A");
        let qa = membership_of(&mut r, "Q::A");
        let pf = membership_of(&mut r, "P::a");
        let other = membership_of(&mut r, "Q::Other");
        let nameless = membership_of(&mut r, "Q::nameless");
        let unnamed_feature = unnamed_feature(&mut r, "R", 0);
        let unnamed = ElementRef(r.b.elements[unnamed_feature.0].owning_relationship.unwrap());
        let ask = |r: &mut ResolvedModel, this: ElementRef, other: ElementRef| {
            call(r, this, DISTINCT, &[DerivedValue::Element(other)]).unwrap()
        };
        // Same name, conforming metaclasses: indistinguishable.
        assert_eq!(ask(&mut r, pa, qa), DerivedValue::Bool(false));
        // Same name, a class against a feature: distinguishable.
        assert_eq!(ask(&mut r, pf, other), DerivedValue::Bool(true));
        // Different names: distinguishable.
        assert_eq!(ask(&mut r, pa, nameless), DerivedValue::Bool(true));
        // A membership without names is distinguishable from anything.
        assert_eq!(ask(&mut r, unnamed, pf), DerivedValue::Bool(true));
        // Symmetric in these cases.
        assert_eq!(ask(&mut r, qa, pa), DerivedValue::Bool(false));
        assert_eq!(ask(&mut r, other, pf), DerivedValue::Bool(true));
    }

    #[test]
    fn redefinition_closures_and_their_removal_follow_the_memberships() {
        let mut r = fixture(
            "redef.kerml",
            "class A { feature x; feature y; class N; } class B specializes A { feature :>> x; feature z; } class C specializes B { feature :>> x; } class D specializes A;",
        );
        const ALL: &str = "Core-Features-Feature-allRedefinedFeatures_";
        const ALL_OF: &str = "Core-Types-Type-allRedefinedFeaturesOf_Membership";
        const REMOVE: &str = "Core-Types-Type-removeRedefinedFeatures_Membership";
        let cx = at(&mut r, "C::x");
        let value = call(&mut r, cx, ALL, &[]).unwrap();
        assert_eq!(names(&mut r, value), ["C::x", "B::x", "A::x"]);
        let b = at(&mut r, "B");
        let cx_membership = membership_of(&mut r, "C::x");
        let value = call(&mut r, b, ALL_OF, &[DerivedValue::Element(cx_membership)]).unwrap();
        assert_eq!(names(&mut r, value), ["C::x", "B::x", "A::x"]);
        let n = membership_of(&mut r, "A::N");
        let value = call(&mut r, b, ALL_OF, &[DerivedValue::Element(n)]).unwrap();
        assert_eq!(names(&mut r, value), Vec::<String>::new());
        // Among A's x and y and B's x, on a type owning no redefinition: A's
        // x goes, redefined by another membership of the list.
        let ax = membership_of(&mut r, "A::x");
        let ay = membership_of(&mut r, "A::y");
        let bx = membership_of(&mut r, "B::x");
        let d = at(&mut r, "D");
        let value = call(
            &mut r,
            d,
            REMOVE,
            &[DerivedValue::Elements(vec![ax, ay, bx])],
        )
        .unwrap();
        assert_eq!(
            value,
            DerivedValue::References(vec![Reference::Element(ay), Reference::Element(bx)])
        );
        // On B, whose own x directly redefines A's x: every membership whose
        // member redefines A's x goes, B's own included, as the body reads.
        let value = call(
            &mut r,
            b,
            REMOVE,
            &[DerivedValue::Elements(vec![ax, ay, bx])],
        )
        .unwrap();
        assert_eq!(
            value,
            DerivedValue::References(vec![Reference::Element(ay)])
        );
        let value = call(&mut r, b, REMOVE, &[DerivedValue::Elements(vec![ax, ay])]).unwrap();
        assert_eq!(
            value,
            DerivedValue::References(vec![Reference::Element(ay)])
        );
        let value = call(&mut r, b, REMOVE, &[DerivedValue::Elements(vec![])]).unwrap();
        assert_eq!(value, DerivedValue::References(vec![]));
    }

    #[test]
    fn filter_conditions_decide_membership_and_exposure() {
        let mut model = Model::new();
        let unit = model.add_source(
            "filters.sysml",
            // A package's filters also screen the imports it would resolve
            // names through, so the conditions name the metadata in full.
            "package Lib { metadata def Safe; metadata def Loud; }
             package P { filter @Lib::Safe; }
             package Both { filter @Lib::Safe; filter @Lib::Loud; }
             package Q { @Lib::Safe; }
             package R;
             package Open;
             package Views { view v { expose Q; filter @Lib::Safe; } view open { expose Q; } }",
        );
        assert!(unit.diagnostics.is_empty(), "{:?}", unit.diagnostics);
        let mut r = ResolvedModel::build(&model);
        const MEMBER: &str = "Kernel-Packages-Package-includeAsMember_Element";
        const EXPOSED: &str = "Systems-Views-ViewUsage-includeAsExposed_Element";
        let p = at(&mut r, "P");
        let both = at(&mut r, "Both");
        let q = at(&mut r, "Q");
        let open = at(&mut r, "Open");
        let r_package = at(&mut r, "R");
        let ask = |r: &mut ResolvedModel, receiver: ElementRef, operation: &str, e: ElementRef| {
            call(r, receiver, operation, &[DerivedValue::Element(e)]).unwrap()
        };
        assert_eq!(ask(&mut r, p, MEMBER, q), DerivedValue::Bool(true));
        assert_eq!(ask(&mut r, p, MEMBER, r_package), DerivedValue::Bool(false));
        assert_eq!(ask(&mut r, both, MEMBER, q), DerivedValue::Bool(false));
        // No conditions: everything is a member.
        assert_eq!(
            ask(&mut r, open, MEMBER, r_package),
            DerivedValue::Bool(true)
        );
        let v = at(&mut r, "Views::v");
        let open_view = at(&mut r, "Views::open");
        assert_eq!(ask(&mut r, v, EXPOSED, q), DerivedValue::Bool(true));
        assert_eq!(
            ask(&mut r, v, EXPOSED, r_package),
            DerivedValue::Bool(false)
        );
        assert_eq!(
            ask(&mut r, open_view, EXPOSED, r_package),
            DerivedValue::Bool(true)
        );
    }

    #[test]
    fn directions_follow_the_supertypes_and_flip_under_conjugation() {
        let mut r = fixture(
            "directions.kerml",
            "class A { in feature p; out feature q; inout feature b; feature r; } class B specializes A; class C conjugates A; class D; class E specializes B, D;",
        );
        const OF: &str = "Core-Types-Type-directionOf_Feature";
        const EXCLUDING: &str = "Core-Types-Type-directionOfExcluding_Feature_Type";
        const FOR: &str = "Core-Features-Feature-directionFor_Type";
        let p = at(&mut r, "A::p");
        let q = at(&mut r, "A::q");
        let b_feature = at(&mut r, "A::b");
        let r_feature = at(&mut r, "A::r");
        let of = |r: &mut ResolvedModel, owner: &str, feature: ElementRef| {
            let owner = at(r, owner);
            call(r, owner, OF, &[DerivedValue::Element(feature)]).unwrap()
        };
        assert_eq!(of(&mut r, "A", p), str("in"));
        assert_eq!(of(&mut r, "A", q), str("out"));
        assert_eq!(of(&mut r, "A", b_feature), str("inout"));
        assert_eq!(of(&mut r, "A", r_feature), DerivedValue::Null);
        assert_eq!(of(&mut r, "B", p), str("in"));
        assert_eq!(of(&mut r, "E", q), str("out"));
        assert_eq!(of(&mut r, "C", p), str("out"));
        assert_eq!(of(&mut r, "C", q), str("in"));
        assert_eq!(of(&mut r, "C", b_feature), str("inout"));
        // Not reachable: null.
        assert_eq!(of(&mut r, "D", p), DerivedValue::Null);
        // Excluding the type that owns it cuts the only path.
        let b = at(&mut r, "B");
        let a = at(&mut r, "A");
        assert_eq!(
            call(
                &mut r,
                b,
                EXCLUDING,
                &[DerivedValue::Element(p), DerivedValue::Elements(vec![a])]
            )
            .unwrap(),
            DerivedValue::Null
        );
        assert_eq!(
            call(
                &mut r,
                b,
                EXCLUDING,
                &[DerivedValue::Element(p), DerivedValue::Elements(vec![])]
            )
            .unwrap(),
            str("in")
        );
        // directionFor asks the type.
        let c = at(&mut r, "C");
        assert_eq!(
            call(&mut r, p, FOR, &[DerivedValue::Element(c)]).unwrap(),
            str("out")
        );
        assert_eq!(
            call(&mut r, p, FOR, &[DerivedValue::Element(b)]).unwrap(),
            str("in")
        );
    }
}
