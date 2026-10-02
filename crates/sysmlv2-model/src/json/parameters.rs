//! Declaration identities used to admit runtime parameter bindings.
use super::{Builder, ElementRef, ResolvedModel, ScopeRef};
use crate::metaclass::conforms;
use std::collections::{HashMap, HashSet};
use sysmlv2_syntax::ast::{Expr, ExprKind, FeatureDirection, MemberKind, QualifiedName};

/// A parameter's declaration identity and the name an argument binds it by.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParameterBinding {
    /// The name a named argument binds the parameter by: its declared name,
    /// else that of the parameter it redefines (`in :>> b` is `b`), whether
    /// explicitly or by position. Empty when neither supplies one.
    pub name: String,
    /// The parameter declaration in the resolved model.
    pub element: ElementRef,
}

/// The declaration selected by a reference in its source and lexical context.
/// An exact identity may have no in-model target; that case must not fall back
/// to an unrelated runtime binding with the same textual spelling.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ReferenceIdentity {
    /// The selected declaration, if it is present in this model.
    pub target: Option<ElementRef>,
    /// Whether this source site carries an exact identity binding.
    pub identity_bound: bool,
}

type SiteKey = (usize, u32, u32);
type ParameterSite = (usize, usize);

/// Derived from declaration spans, never serialized. The size stamp rejects a
/// library-prefix index after user declarations have been appended to its clone.
#[derive(Clone)]
pub(super) struct ParameterSites {
    elements_len: usize,
    sites: HashMap<SiteKey, Option<ParameterSite>>,
}

/// Signatures of a completed, unchanged graph. Cached failures retain their
/// distinction from a valid empty signature.
#[derive(Clone)]
pub(super) struct ParameterSignatures {
    elements_len: usize,
    signatures: HashMap<usize, Option<Vec<ParameterBinding>>>,
}

impl ParameterSites {
    fn build(b: &Builder) -> Self {
        let mut sites = HashMap::new();
        for (&element, span) in b.member_spans.iter() {
            if !input_parameter(b, element) {
                continue;
            }
            let key = (b.unit_of_elem(element), span.start, span.end);
            let site = b.owner_scope_of(element).map(|scope| (element, scope));
            sites
                .entry(key)
                .and_modify(|previous| {
                    if *previous != site {
                        *previous = None;
                    }
                })
                .or_insert(site);
        }
        Self {
            elements_len: b.elements.len(),
            sites,
        }
    }

    fn current(&self, b: &Builder) -> bool {
        self.elements_len == b.elements.len()
    }
}

fn input_parameter(b: &Builder, element: usize) -> bool {
    b.is_parameter(element)
        && matches!(
            b.elements[element]
                .props
                .get("direction")
                .and_then(|value| value.as_str()),
            Some("in" | "inout")
        )
}

/// Deeper heritage than any callable needs: a walk past it answers
/// no signature instead of exhausting the stack.
const MAX_SIGNATURE_DEPTH: usize = 64;

/// One callable's signature walk: each type's parameter list once, its owned
/// parameters once with the type that owns each, the types whose lists are
/// still being worked out, and the positional slots read on the way.
#[derive(Default)]
struct SignatureWalk {
    lists: HashMap<usize, Option<Vec<usize>>>,
    owned: HashMap<usize, Vec<usize>>,
    owners: HashMap<usize, usize>,
    active: HashSet<usize>,
    slots: SlotMemo,
}

/// A role whose redefinition the specification implies by position.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
enum Role {
    Parameter,
    End,
    Result,
    Subject,
}

/// The slots of each type and role read so far by one positional walk —
/// a function of the heritage and the structure, which do not change
/// while a walk runs — and the ones being worked out up the recursion.
/// Exact for an acyclic heritage: on a cycle the re-entered type answers
/// its own slots, which the types consuming that answer keep.
#[derive(Default)]
pub(crate) struct SlotMemo {
    slots: HashMap<(usize, Role), Vec<usize>>,
    active: HashSet<(usize, Role)>,
    /// Header names resolved once in the feature's own context.
    spelled_redefinitions: HashMap<usize, Vec<usize>>,
}

fn behavior_or_step(ty: &str) -> bool {
    conforms(ty, "Behavior") || conforms(ty, "Step")
}

fn function_or_expression(ty: &str) -> bool {
    conforms(ty, "Function") || conforms(ty, "Expression")
}

/// The SysML families whose subject redefines its general's subject, even an
/// inherited one: requirements and cases.
fn subject_family(ty: &str) -> Option<u8> {
    if conforms(ty, "RequirementDefinition") || conforms(ty, "RequirementUsage") {
        Some(0)
    } else if conforms(ty, "CaseDefinition") || conforms(ty, "CaseUsage") {
        Some(1)
    } else {
        None
    }
}

impl Builder {
    fn is_subject(&self, feature: usize) -> bool {
        self.elements[feature]
            .owning_relationship
            .is_some_and(|r| conforms(self.elements[r].ty, "SubjectMembership"))
    }

    fn is_private_member(&self, feature: usize) -> bool {
        self.elements[feature].owning_relationship.is_some_and(|r| {
            self.elements[r]
                .props
                .get("visibility")
                .and_then(|value| value.as_str())
                == Some("private")
        })
    }

    /// A type's owned parameters other than the result, in declaration order:
    /// the ones a position pairs.
    fn owned_parameters(&self, owner: usize) -> Vec<usize> {
        self.owned_member_elems(owner, true)
            .into_iter()
            .filter(|&f| self.is_parameter(f) && !self.positional_is_result(f))
            .collect()
    }

    /// A type's owned end features, in declaration order.
    fn owned_ends(&self, owner: usize) -> Vec<usize> {
        self.owned_member_elems(owner, true)
            .into_iter()
            .filter(|&f| self.positional_is_end(f))
            .collect()
    }

    /// [`Self::owned_parameters`], recorded in the walk with the owner of
    /// each parameter.
    fn ordered_parameters(&self, walk: &mut SignatureWalk, owner: usize) -> Vec<usize> {
        if let Some(parameters) = walk.owned.get(&owner) {
            return parameters.clone();
        }
        let parameters = self.owned_parameters(owner);
        for &parameter in &parameters {
            walk.owners.insert(parameter, owner);
        }
        walk.owned.insert(owner, parameters.clone());
        parameters
    }

    /// The types `ty` directly specializes, as its inherited members read
    /// them: its written generals (typings, specializations, subsettings,
    /// redefinitions, reference subsettings, chains), in the order written,
    /// then the implied library bases of its kind.
    fn direct_generals(&mut self, ty: usize) -> Vec<usize> {
        // A type without a scope of its own (the argument of an assignment,
        // terminate or satisfy usage) has no body to inherit into and no
        // generals here — whenever asked: a base scope's answer must not
        // depend on whether the specialization index exists yet, and a
        // parameter's positional generals come from `direct_redefinitions`.
        let Some(&scope) = self.elem_scope.get(&ty) else {
            return Vec::new();
        };
        let (bases, _) = self.base_scopes_split(scope);
        let mut generals = Vec::new();
        for base in bases {
            if let Some(owner) = self.scopes[base].owner {
                if owner != ty && !generals.contains(&owner) {
                    generals.push(owner);
                }
            }
        }
        generals
    }

    /// The parameters a callable has, its result aside: those it owns, then
    /// each direct general's (see [`Self::direct_generals`]), in that order,
    /// but for those its own features redefine. `None` for cyclic or overly
    /// deep heritage.
    fn signature(
        &mut self,
        walk: &mut SignatureWalk,
        ty: usize,
        depth: usize,
        cacheable: &mut bool,
    ) -> Option<Vec<usize>> {
        if let Some(list) = walk.lists.get(&ty) {
            return list.clone();
        }
        if depth > MAX_SIGNATURE_DEPTH || !walk.active.insert(ty) {
            return None;
        }
        let list = self.signature_uncached(walk, ty, depth, cacheable);
        walk.active.remove(&ty);
        walk.lists.insert(ty, list.clone());
        list
    }

    fn signature_uncached(
        &mut self,
        walk: &mut SignatureWalk,
        ty: usize,
        depth: usize,
        cacheable: &mut bool,
    ) -> Option<Vec<usize>> {
        // The supertype helper can re-resolve missing outcomes. Do not
        // retain a result that could depend on ambient source or lookup
        // state rather than the graph's recorded endpoints.
        self.ensure_spec_index();
        if self
            .spec_index
            .as_ref()
            .and_then(|index| index.get(&ty))
            .is_some_and(|indices| {
                indices
                    .iter()
                    .any(|&index| self.spec_resolved.get(index).is_none_or(Option::is_none))
            })
        {
            *cacheable = false;
        }
        let own = self.ordered_parameters(walk, ty);
        let mut generals = self.direct_generals(ty);
        // A parameter also specializes the ones it redefines by position: an
        // argument written `in f = g;` is called with `f`'s parameters.
        if self.is_parameter(ty) {
            for target in self.direct_redefinitions(walk, ty) {
                if !generals.contains(&target) {
                    generals.push(target);
                }
            }
        }
        let mut inherited = Vec::new();
        for general in generals {
            for parameter in self.signature(walk, general, depth + 1, cacheable)? {
                if !own.contains(&parameter)
                    && !inherited.contains(&parameter)
                    && !self.is_private_member(parameter)
                {
                    inherited.push(parameter);
                }
            }
        }
        if inherited.is_empty() {
            return Some(own);
        }
        // KerML removes an inherited feature that an owned feature redefines
        // directly, or redefines through something it redefines, and one that
        // another inherited feature redefines.
        let owned = self.owned_member_elems(ty, true);
        let mut owned_targets = HashSet::new();
        for &feature in &owned {
            owned_targets.extend(self.direct_redefinitions(walk, feature));
        }
        let mut hidden = HashSet::new();
        for &parameter in &inherited {
            let closure = self.redefinition_closure(walk, parameter);
            if closure.iter().any(|t| owned_targets.contains(t)) {
                hidden.insert(parameter);
            }
            hidden.extend(closure.into_iter().filter(|&t| t != parameter));
        }
        inherited.retain(|parameter| !hidden.contains(parameter));
        Some(own.into_iter().chain(inherited).collect())
    }

    /// The features `feature` redefines in one step: those it names, and
    /// those its position pairs it with
    /// ([`Self::positional_redefinition_targets`]), through the type the
    /// walk recorded as its owner — the arguments of assignment, terminate
    /// and satisfy usages have no scope of their own, so `owner_elem`
    /// cannot find them.
    fn direct_redefinitions(&mut self, walk: &mut SignatureWalk, feature: usize) -> Vec<usize> {
        let mut targets = self.redefinition_target_elems(feature);
        let Some(owner) = walk
            .owners
            .get(&feature)
            .copied()
            .or_else(|| self.owner_elem(feature))
        else {
            return targets;
        };
        for target in self.positional_targets(feature, owner, &mut walk.slots) {
            if !targets.contains(&target) {
                targets.push(target);
            }
        }
        targets
    }

    /// `feature` and everything it redefines, transitively.
    fn redefinition_closure(&mut self, walk: &mut SignatureWalk, feature: usize) -> Vec<usize> {
        let mut closure = vec![feature];
        let mut next = 0;
        while let Some(&current) = closure.get(next) {
            next += 1;
            for target in self.direct_redefinitions(walk, current) {
                if !closure.contains(&target) {
                    closure.push(target);
                }
            }
        }
        closure
    }

    /// Whether `e` plays a role whose redefinition the specification implies
    /// by position — a parameter of a behavior or step, a result, an end —
    /// so that reusing an inherited name says nothing about what it
    /// redefines (see [`Self::positional_redefinition_targets`]).
    pub(crate) fn redefines_by_position(&self, e: usize) -> bool {
        if self.positional_is_end(e) || self.positional_is_result(e) {
            return true;
        }
        self.is_parameter(e)
            && self
                .owner_elem(e)
                .is_some_and(|owner| behavior_or_step(self.elements[owner].ty))
    }

    /// KerML's `checkFeatureParameterRedefinition` exempts an invocation's
    /// argument that names the parameter it redefines (`f(b = 1)`): such an
    /// argument takes over no parameter by position.
    fn names_its_redefined_parameter(&self, feature: usize, owner_ty: &str) -> bool {
        conforms(owner_ty, "InvocationExpression")
            && self.elements[feature].owned_relationships.iter().any(|&r| {
                conforms(self.elements[r].ty, "Redefinition")
                    && self.elements[r]
                        .props
                        .get("isImplied")
                        .and_then(|v| v.as_bool())
                        != Some(true)
            })
    }

    /// The features `feature` redefines by position, read off the direct
    /// generals of `owner`, the type that owns it (see
    /// [`Self::direct_generals`]):
    ///
    /// - an end feature redefines each general's end at the same position
    ///   (KerML `checkFeatureEndRedefinition`);
    /// - a parameter of a behavior or step, its result aside, redefines each
    ///   behavior or step general's parameter at the same position
    ///   (`checkFeatureParameterRedefinition`, which exempts only an
    ///   invocation's argument naming what it redefines);
    /// - the result of a function or expression redefines each function or
    ///   expression general's result, wherever that is
    ///   (`checkFeatureResultRedefinition`);
    /// - a requirement's or case's subject redefines each same-family
    ///   general's subject, wherever that is (SysML).
    ///
    /// A general's parameters and ends are its effective ones — its own,
    /// then those it inherits after them, less those its features redefine
    /// ([`Self::effective_slots`]); its result and subject are its own,
    /// else the nearest its heritage declares ([`Self::nearest_members`]).
    /// The parameter walk pairs through this too; the positional planner
    /// materializes the same edges for the whole model
    /// (`PositionalRedefinitions`), and also counts a membership a general
    /// imports as one of its slots, which this structural reading — made
    /// for a body scope's bases, before the specialization index may
    /// exist — does not. Nothing for an ambiguous subject or result.
    pub(crate) fn positional_redefinition_targets(
        &mut self,
        feature: usize,
        owner: usize,
    ) -> Vec<usize> {
        self.positional_targets(feature, owner, &mut SlotMemo::default())
    }

    /// [`Self::positional_redefinition_targets`] within one walk.
    pub(crate) fn positional_targets(
        &mut self,
        feature: usize,
        owner: usize,
        memo: &mut SlotMemo,
    ) -> Vec<usize> {
        let mut targets = Vec::new();
        // A cyclic heritage could pair a feature with itself.
        let push = |targets: &mut Vec<usize>, target: usize| {
            if target != feature && !targets.contains(&target) {
                targets.push(target);
            }
        };
        let owner_ty = self.elements[owner].ty;
        if self.positional_is_end(feature) {
            let Some(index) = self.owned_ends(owner).iter().position(|&f| f == feature) else {
                return targets;
            };
            for general in self.direct_generals(owner) {
                if let Some(&target) = self.effective_slots(general, Role::End, memo).get(index) {
                    push(&mut targets, target);
                }
            }
            return targets;
        }
        if self.positional_is_result(feature) {
            if !function_or_expression(owner_ty) {
                return targets;
            }
            for general in self.direct_generals(owner) {
                if !function_or_expression(self.elements[general].ty) {
                    continue;
                }
                if let [target] = self.nearest_members(general, Role::Result, memo)[..] {
                    push(&mut targets, target);
                }
            }
            return targets;
        }
        // Every subject family is a behavior or step, so the parameter
        // rule's owner test comes first and spares a classifier's directed
        // feature its owner's base fill.
        if !self.is_parameter(feature) || !behavior_or_step(owner_ty) {
            return targets;
        }
        let own = self.owned_parameters(owner);
        let Some(index) = own.iter().position(|&p| p == feature) else {
            return targets;
        };
        let subject = self.is_subject(feature);
        let generals = self.direct_generals(owner);
        let mut subject_generals = Vec::new();
        if let Some(family) = subject_family(owner_ty) {
            if own.iter().filter(|&&p| self.is_subject(p)).count() > 1 {
                return targets;
            }
            for &general in &generals {
                if subject_family(self.elements[general].ty) != Some(family) {
                    continue;
                }
                match self.nearest_members(general, Role::Subject, memo)[..] {
                    [] => {}
                    [target] => {
                        subject_generals.push(general);
                        if subject {
                            push(&mut targets, target);
                        }
                    }
                    _ => return targets,
                }
            }
        }
        if self.names_its_redefined_parameter(feature, owner_ty) {
            return targets;
        }
        for &general in &generals {
            if !behavior_or_step(self.elements[general].ty)
                || (subject && subject_generals.contains(&general))
            {
                continue;
            }
            if let Some(&target) = self
                .effective_slots(general, Role::Parameter, memo)
                .get(index)
            {
                push(&mut targets, target);
            }
        }
        targets
    }

    /// Whether a written redefinition selects this supplied slot. Header names
    /// select declaration identities, never every inherited slot of that name.
    fn spelled_redefinition(&mut self, feature: usize, slot: usize, memo: &mut SlotMemo) -> bool {
        let Some(&scope) = self.elem_scope.get(&feature) else {
            return false;
        };
        let spellings = &self.scopes[scope].redefinition_spellings;
        if spellings.is_empty() {
            return false;
        }
        if let std::collections::hash_map::Entry::Vacant(entry) =
            memo.spelled_redefinitions.entry(feature)
        {
            let spellings = spellings.clone();
            let mut targets = Vec::new();
            if !spellings.is_empty() {
                // This helper also runs during base-cache construction. Resolve
                // in the header's own lexical/source context, never the ambient
                // query's access, exclusion or source-identity mode. Do not read
                // the specialization index while lowering is still appending it.
                let query = self.enter_fill_mode();
                let mark = self.query_imports.len();
                let origin = self.set_identity_origin(feature);
                self.exclude = Some(feature);
                self.redefinition_lookup_owner = self.owner_elem(feature);
                let from = self.scopes[scope].parent.unwrap_or(scope);
                for qn in spellings {
                    if let Some(target) = self.resolve(from, &qn, 0) {
                        targets.push(target);
                    }
                }
                self.identity_origin_unit = origin;
                self.query_imports.truncate(mark);
                self.leave_fill_mode(query);
            }
            entry.insert(targets);
        }
        memo.spelled_redefinitions[&feature].contains(&slot)
    }

    /// A type's features of one positional role (its parameters, its ends),
    /// as a specialization pairs them: its own, then those it inherits
    /// after them — each general's, nearest first, past the positions its
    /// own take over (KerML 7.4.7.2: a general's parameters are its owned
    /// ones, then the inherited ones ordered after them) — less those an
    /// own slot or another inherited slot redefines, by position or by a
    /// spelled `:>>`, directly or through what that one redefines (the
    /// KerML removal of redefined features). A type whose slots are being
    /// worked out up the recursion contributes its own.
    fn effective_slots(&mut self, ty: usize, role: Role, memo: &mut SlotMemo) -> Vec<usize> {
        if let Some(slots) = memo.slots.get(&(ty, role)) {
            return slots.clone();
        }
        let own = match role {
            Role::Parameter => self.owned_parameters(ty),
            Role::End => self.owned_ends(ty),
            Role::Result | Role::Subject => unreachable!("singular roles are read nearest"),
        };
        if memo.active.len() > MAX_SIGNATURE_DEPTH || !memo.active.insert((ty, role)) {
            return own;
        }
        let mut inherited = Vec::new();
        for general in self.direct_generals(ty) {
            // Positions take over a behavior's or step's parameters and
            // any general's ends, as the pairing does; a classifier's
            // directed features are inherited whole.
            let taken = match role {
                Role::Parameter if !behavior_or_step(self.elements[general].ty) => 0,
                _ => own.len(),
            };
            for (position, slot) in self
                .effective_slots(general, role, memo)
                .into_iter()
                .enumerate()
            {
                if position >= taken && !own.contains(&slot) && !inherited.contains(&slot) {
                    inherited.push(slot);
                }
            }
        }
        let mut hidden = HashSet::new();
        if !inherited.is_empty() {
            let mut pending: Vec<(usize, usize)> = own
                .iter()
                .map(|&slot| (slot, ty))
                .chain(
                    inherited
                        .iter()
                        .filter_map(|&slot| Some((slot, self.owner_elem(slot)?))),
                )
                .collect();
            let mut seen: HashSet<usize> = pending.iter().map(|&(slot, _)| slot).collect();
            let mut supplied_by: HashMap<usize, HashSet<usize>> = HashMap::new();
            while let Some((slot, slot_owner)) = pending.pop() {
                let mut redefined = self.positional_targets(slot, slot_owner, memo);
                // A `:>>` spelled on `slot` names a feature its owner
                // inherits — one of its owner's generals' slots — never a
                // nearer namesake (`IfThenPerformance::ifTest`, itself a
                // `:>> ifTest`, cannot hide `IfThenAction`'s).
                if let std::collections::hash_map::Entry::Vacant(entry) =
                    supplied_by.entry(slot_owner)
                {
                    let mut supplied = HashSet::new();
                    for general in self.direct_generals(slot_owner) {
                        supplied.extend(self.effective_slots(general, role, memo));
                    }
                    entry.insert(supplied);
                }
                let supplied = &supplied_by[&slot_owner];
                redefined.extend(inherited.iter().copied().filter(|&candidate| {
                    supplied.contains(&candidate)
                        && self.spelled_redefinition(slot, candidate, memo)
                }));
                for target in redefined {
                    if target != slot {
                        hidden.insert(target);
                        if seen.insert(target) {
                            if let Some(target_owner) = self.owner_elem(target) {
                                pending.push((target, target_owner));
                            }
                        }
                    }
                }
            }
        }
        memo.active.remove(&(ty, role));
        let slots: Vec<usize> = own
            .into_iter()
            .chain(inherited.into_iter().filter(|slot| !hidden.contains(slot)))
            .collect();
        memo.slots.insert((ty, role), slots.clone());
        slots
    }

    /// The members of one singular role (result, subject) a specialization
    /// of `ty` pairs with: `ty`'s own, else those its generals pair with,
    /// where a nearer one wins — a candidate reached through another
    /// candidate's heritage is what that one redefines (`FEA1 :> FEA` with
    /// `FEA { subject vehicle; }` inherits `vehicle` beside the library
    /// case's `subj`, which `vehicle` redefines). More than one left means
    /// the heritage does not say which; a cyclic heritage says nothing.
    fn nearest_members(&mut self, ty: usize, role: Role, memo: &mut SlotMemo) -> Vec<usize> {
        if let Some(found) = memo.slots.get(&(ty, role)) {
            return found.clone();
        }
        let select: fn(&Self, usize) -> bool = match role {
            Role::Result => Self::positional_is_result,
            Role::Subject => Self::is_subject,
            Role::Parameter | Role::End => unreachable!("positional roles are read as slots"),
        };
        let own: Vec<usize> = self
            .owned_member_elems(ty, true)
            .into_iter()
            .filter(|&m| select(self, m))
            .collect();
        if !own.is_empty() {
            memo.slots.insert((ty, role), own.clone());
            return own;
        }
        if memo.active.len() > MAX_SIGNATURE_DEPTH || !memo.active.insert((ty, role)) {
            return Vec::new();
        }
        let mut candidates = Vec::new();
        for general in self.direct_generals(ty) {
            for member in self.nearest_members(general, role, memo) {
                if !candidates.contains(&member) {
                    candidates.push(member);
                }
            }
        }
        memo.active.remove(&(ty, role));
        if candidates.len() > 1 {
            let mut reachable = HashSet::new();
            for &candidate in &candidates {
                if let Some(owner) = self.owner_elem(candidate) {
                    self.role_heritage(owner, select, &mut HashSet::new(), 0, &mut reachable);
                }
            }
            candidates.retain(|candidate| !reachable.contains(candidate));
        }
        memo.slots.insert((ty, role), candidates.clone());
        candidates
    }

    /// Every member of the role `select` reachable through the generals of
    /// `ty`, at any depth, into `out`.
    fn role_heritage(
        &mut self,
        ty: usize,
        select: fn(&Self, usize) -> bool,
        seen: &mut HashSet<usize>,
        depth: usize,
        out: &mut HashSet<usize>,
    ) {
        if depth > MAX_SIGNATURE_DEPTH || !seen.insert(ty) {
            return;
        }
        for general in self.direct_generals(ty) {
            for member in self.owned_member_elems(general, true) {
                if select(self, member) {
                    out.insert(member);
                }
            }
            self.role_heritage(general, select, seen, depth + 1, out);
        }
    }

    /// The name a named argument binds `parameter` by (see
    /// [`ParameterBinding::name`]), nearest redefinition first.
    fn binding_name(&mut self, walk: &mut SignatureWalk, parameter: usize) -> Option<String> {
        let mut pending = vec![parameter];
        let mut next = 0;
        while let Some(&current) = pending.get(next) {
            next += 1;
            if let Some(name) = self.id_name(current) {
                return Some(name);
            }
            for target in self.direct_redefinitions(walk, current) {
                if !pending.contains(&target) {
                    pending.push(target);
                }
            }
        }
        Some(String::new())
    }
}

impl Builder {
    /// Context-free scope selection without traversing receiver dependencies.
    pub(crate) fn value_evaluation_scope(
        &self,
        element: usize,
        receiver: Option<usize>,
    ) -> Option<usize> {
        let own_scope = self.values.get(&element)?.0;
        let featured = self
            .owner_elem(element)
            .is_some_and(|owner| crate::metaclass::conforms(self.elements[owner].ty, "Type"));
        (!featured || receiver.is_none_or(|scope| scope == own_scope)).then_some(own_scope)
    }

    pub(crate) fn reference_identity(
        &mut self,
        scope: usize,
        name: &QualifiedName,
    ) -> ReferenceIdentity {
        let identity_bound = self.id_spelled_target(scope, name).is_some();
        ReferenceIdentity {
            target: self.resolve(scope, name, 0).map(ElementRef),
            identity_bound,
        }
    }

    /// The inputs of the callable's signature (see [`Self::signature`]) with
    /// the names a named argument binds them by.
    pub(crate) fn calc_parameter_bindings(
        &mut self,
        element: usize,
    ) -> Option<Vec<ParameterBinding>> {
        if !self.semantic_ready {
            return self.calc_parameter_bindings_uncached(element, &mut false);
        }
        if self
            .parameter_signatures
            .as_ref()
            .is_none_or(|cache| cache.elements_len != self.elements.len())
        {
            self.parameter_signatures = Some(ParameterSignatures {
                elements_len: self.elements.len(),
                signatures: HashMap::new(),
            });
        }
        if let Some(signature) = self
            .parameter_signatures
            .as_ref()
            .and_then(|cache| cache.signatures.get(&element))
        {
            return signature.clone();
        }
        let mut cacheable = true;
        let signature = self.calc_parameter_bindings_uncached(element, &mut cacheable);
        if cacheable {
            self.parameter_signatures
                .as_mut()
                .expect("a ready graph initialized its signature cache")
                .signatures
                .insert(element, signature.clone());
        }
        signature
    }

    fn calc_parameter_bindings_uncached(
        &mut self,
        element: usize,
        cacheable: &mut bool,
    ) -> Option<Vec<ParameterBinding>> {
        let mut names = HashSet::new();
        let mut bindings = Vec::new();
        for parameter in self.named_signature(element, cacheable)? {
            if !input_parameter(self, parameter.element.0) {
                continue;
            }
            if !parameter.name.is_empty() && !names.insert(parameter.name.clone()) {
                return None;
            }
            bindings.push(parameter);
        }
        Some(bindings)
    }

    /// The callable's signature (see [`Self::signature`]), each parameter
    /// with the name an argument binds it by.
    pub(crate) fn named_signature(
        &mut self,
        callee: usize,
        cacheable: &mut bool,
    ) -> Option<Vec<ParameterBinding>> {
        let mut walk = SignatureWalk::default();
        self.signature(&mut walk, callee, 0, cacheable)?
            .into_iter()
            .map(|parameter| {
                Some(ParameterBinding {
                    name: self.binding_name(&mut walk, parameter)?,
                    element: ElementRef(parameter),
                })
            })
            .collect()
    }

    pub(crate) fn lambda_parameter_bindings(
        &mut self,
        unit: usize,
        body: &Expr,
    ) -> Option<(ScopeRef, Vec<ParameterBinding>)> {
        let ExprKind::Body { members } = &body.kind else {
            return None;
        };
        if self
            .parameter_sites
            .as_ref()
            .is_none_or(|sites| !sites.current(self))
        {
            self.parameter_sites = Some(ParameterSites::build(self));
        }
        let sites = &self.parameter_sites.as_ref()?.sites;
        let mut scope = None;
        let mut names = HashSet::new();
        let mut bindings = Vec::new();
        for member in members {
            let MemberKind::Usage(usage) = &member.kind else {
                continue;
            };
            if !matches!(
                usage.prefix.direction,
                Some(FeatureDirection::In | FeatureDirection::InOut)
            ) {
                continue;
            }
            let name = &usage.declaration.id.name.as_ref()?.value;
            if !names.insert(name.as_str()) {
                return None;
            }
            let (element, declaration_scope) = sites
                .get(&(unit, member.span.start, member.span.end))?
                .as_ref()?;
            if self.elements[*element]
                .props
                .get("declaredName")
                .and_then(|value| value.as_str())
                != Some(name.as_str())
                || scope.is_some_and(|scope| scope != *declaration_scope)
            {
                return None;
            }
            scope = Some(*declaration_scope);
            bindings.push(ParameterBinding {
                name: name.clone(),
                element: ElementRef(*element),
            });
        }
        Some((ScopeRef(scope?), bindings))
    }
}

impl ResolvedModel {
    /// A context-free evaluation scope for an authored value. Root and other
    /// non-Type-owned values use their declaration's lexical scope. Type-owned
    /// values require no proof only when the receiver is absent or identical
    /// to that scope. Other receivers return `None`; use
    /// [`Self::value_scope_decision_with_steps`] for a checked contextual read.
    /// `None` also denotes an absent authored expression and must not be treated
    /// as permission to substitute a caller scope.
    pub fn value_evaluation_scope(
        &self,
        element: ElementRef,
        receiver: Option<ScopeRef>,
    ) -> Option<ScopeRef> {
        self.b
            .value_evaluation_scope(element.0, receiver.map(|scope| scope.0))
            .map(ScopeRef)
    }

    /// Resolve a reference for runtime parameter admission using its declaration
    /// lexical scope and current source context (see [`Self::with_source`]).
    /// The lexical scope is independent of any receiver used to evaluate a value.
    pub fn reference_identity(
        &mut self,
        lexical_scope: ScopeRef,
        name: &QualifiedName,
    ) -> ReferenceIdentity {
        self.b.reference_identity(lexical_scope.0, name)
    }

    /// The input parameters an invocation of `calculation` binds its
    /// arguments to, in order: the `in` and `inout` parameters of
    /// [`Self::callable_parameters`], each with the name a named argument
    /// binds it by. With `calc def Diff { in a; in b; }` and
    /// `calc def D :> Diff { in x; }`, `D` binds `(x, b)`: `x` takes over `a`
    /// by position. Returns `None` when [`Self::callable_parameters`] does,
    /// or when two inputs answer to the same name.
    pub fn calc_parameter_bindings(
        &mut self,
        calculation: ElementRef,
    ) -> Option<Vec<ParameterBinding>> {
        self.b.calc_parameter_bindings(calculation.0)
    }

    /// A callable's parameters, its result aside, as an invocation sees them:
    /// those it owns, in declaration order, then those of each general it is
    /// written to specialize, type, subset or redefine, in the order the
    /// generals are written, then those of the implied library bases of its
    /// kind, but for any its own features redefine — explicitly, by
    /// position, or as a requirement's or case's subject — each with the
    /// name an argument binds it by (see
    /// [`ParameterBinding::name`]). KerML pairs every owned parameter of a
    /// behavior or step with each general's parameter at the same position
    /// — the general's own, then those it inherits after them — even one
    /// that also redefines a parameter explicitly:
    /// `in :>> b;` in a specialization of `Diff { in a; in b; }` redefines
    /// both `a` and `b`.
    ///
    /// Read off the callable's heritage alone, without the model-wide
    /// positional plan, so the first call stays cheap. They agree with the
    /// parameters among [`Self::effective_features`] with implied heritage
    /// (a requirement without a subject of its own inherits its library
    /// base's), except that this pairs a general reached through a feature
    /// chain by position, as that view does not. `None` for cyclic or
    /// overly deep heritage.
    pub fn callable_parameters(&mut self, callee: ElementRef) -> Option<Vec<ParameterBinding>> {
        self.b.named_signature(callee.0, &mut true)
    }

    /// The features `feature` redefines by position: for an end, each direct
    /// general's end at the same position; for a parameter of a behavior or
    /// step, each behavior or step general's parameter at the same position,
    /// the general's own then those it inherits after them (an invocation's
    /// argument naming what it redefines excepted);
    /// for a result, each function or expression general's result; for a
    /// requirement's or case's subject, each same-family general's subject.
    /// Read off the owner's heritage alone (written generals, then the
    /// implied library bases), without the model-wide positional plan: it is
    /// what the redefining feature's body inherits members through, and what
    /// the implied `Redefinition` relationships of [`Self::implied_relationships`]
    /// materialize. Empty for a feature of no such role, or whose owner is
    /// unknown.
    pub fn positional_redefinition_targets(&mut self, feature: ElementRef) -> Vec<ElementRef> {
        // The element's owner, not its scope's: the ends a `connect` clause
        // declares resolve their targets from the enclosing scope.
        let Some(owner) = self.owner(feature) else {
            return Vec::new();
        };
        self.b
            .positional_redefinition_targets(feature.0, owner.0)
            .into_iter()
            .map(ElementRef)
            .collect()
    }

    /// Recover a lambda's input declaration identities and lexical scope from
    /// the source owner's unit and the input members' exact declaration spans.
    /// Returns `None` for absent or ambiguous declarations, or when no input
    /// declaration establishes a body scope. This does not validate the body.
    pub fn lambda_parameter_bindings(
        &mut self,
        source_owner: ElementRef,
        body: &Expr,
    ) -> Option<(ScopeRef, Vec<ParameterBinding>)> {
        let unit = self.b.unit_of_elem(source_owner.0);
        self.b.lambda_parameter_bindings(unit, body)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Model;
    use sysmlv2_syntax::ast::ArrowArgs;

    fn lambda_body(expression: &Expr) -> &Expr {
        match &expression.kind {
            ExprKind::Arrow {
                args: ArrowArgs::Body(body),
                ..
            }
            | ExprKind::Collect { body, .. } => body,
            _ => panic!("expected a collection lambda"),
        }
    }

    fn names(bindings: &[ParameterBinding]) -> Vec<&str> {
        bindings.iter().map(|p| p.name.as_str()).collect()
    }

    #[test]
    fn calculation_bindings_take_own_inputs_then_inherited_ones() {
        let mut model = Model::new();
        model.add_source(
            "parameters.sysml",
            "calc def Base { in x; inout y; return z; }
             calc def Child :> Base;
             calc def Other { in q; }
             calc def Multiple :> Base, Other;
             calc def Own :> Base { in local; }
             calc def Duplicate { in x; in x; }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let base = r.resolve_qualified("Base").unwrap();
        let child = r.resolve_qualified("Child").unwrap();
        let multiple = r.resolve_qualified("Multiple").unwrap();
        let own = r.resolve_qualified("Own").unwrap();
        let duplicate = r.resolve_qualified("Duplicate").unwrap();
        let parameters = r.calc_parameter_bindings(base).unwrap();
        assert_eq!(names(&parameters), ["x", "y"]);
        assert_eq!(r.calc_parameter_bindings(child), Some(parameters.clone()));
        // Each general's inputs, in the order the generals are written.
        let both = r.calc_parameter_bindings(multiple).unwrap();
        assert_eq!(names(&both), ["x", "y", "q"]);
        assert_eq!(both[..2], parameters[..]);
        assert_eq!(both[2].element, r.resolve_qualified("Other::q").unwrap());
        // `local` takes over `x` by position; `y` is still inherited.
        let own = r.calc_parameter_bindings(own).unwrap();
        assert_eq!(names(&own), ["local", "y"]);
        assert_eq!(own[1], parameters[1]);
        assert_eq!(r.calc_parameter_bindings(duplicate), None);
    }

    /// The inputs a calculation binds are the input parameters among the
    /// model's own view of its features, implied heritage included.
    #[test]
    fn calculation_bindings_agree_with_the_inherited_view() {
        let mut model = Model::new();
        model.add_source(
            "signatures.sysml",
            "package P {
                calc def Diff { in a; in b; return r = a - b; }
                calc def D3 :> Diff { in x; }
                calc def D2 :> Diff { in :>> b; }
                calc def A { in p; in q; }
                calc def B :> A { in r; }
                calc def C :> B { in s; in t; }
                calc def Mixed { in a; out o; in b; }
                calc def SubMixed :> Mixed { in x; in y; }
                calc def Two :> A, Diff { in z; }
                calc def SameName :> Diff { in b; }
                attribute def Number;
                calc def Unnamed :> Diff { in : Number; }
                calc typed : Diff;
                calc typedOwn : Diff { in x; }
                part def Q { calc m : Diff; }
                part def Q2 :> Q { calc :>> m { in y; } }
            }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        for (name, expected) in [
            ("Diff", &["a", "b"][..]),
            ("D3", &["x", "b"]),
            ("D2", &["b"]),
            ("B", &["r", "q"]),
            // A general's parameters are its own, then the inherited ones
            // after them: `t` pairs with `B`'s second parameter, `q`.
            ("C", &["s", "t"]),
            // An output holds its position too.
            ("SubMixed", &["x", "y", "b"]),
            ("Two", &["z", "q", "b"]),
            // A reused name hides nothing: `SameName::b` redefines `a` by
            // position and `Diff::b` is still inherited — two inputs of one
            // name, which no invocation can bind by name.
            ("SameName", &["b", "b"]),
            ("Unnamed", &["a", "b"]),
            ("typed", &["a", "b"]),
            ("typedOwn", &["x", "b"]),
            ("Q::m", &["a", "b"]),
            ("Q2::m", &["y", "b"]),
        ] {
            let callee = r.resolve_qualified(&format!("P::{name}")).unwrap();
            let inherited: Vec<ElementRef> = r
                .effective_features(callee, true)
                .into_iter()
                .filter(|&f| {
                    r.is_parameter(f)
                        && r.owning_membership_type(f) != Some("ReturnParameterMembership")
                })
                .collect();
            let parameters = r.callable_parameters(callee).unwrap();
            assert_eq!(
                parameters.iter().map(|p| p.element).collect::<Vec<_>>(),
                inherited,
                "{name}"
            );
            let Some(bindings) = r.calc_parameter_bindings(callee) else {
                assert_eq!(name, "SameName");
                assert_eq!(names(&parameters), expected, "{name}");
                continue;
            };
            assert!(bindings.iter().all(|b| parameters.contains(b)), "{name}");
            assert_eq!(names(&bindings), expected, "{name}");
            let inputs: Vec<ElementRef> = inherited
                .into_iter()
                .filter(|&f| matches!(r.declared_direction(f), Some("in" | "inout")))
                .collect();
            assert_eq!(
                bindings.iter().map(|p| p.element).collect::<Vec<_>>(),
                inputs,
                "{name}"
            );
        }
    }

    /// A requirement without a subject of its own takes its library base's,
    /// and a performed action the parameters of what it performs: the
    /// implied bases and reference subsettings its inherited members read.
    #[test]
    fn implied_bases_and_reference_subsettings_supply_parameters() {
        let mut model = Model::new();
        model.add_library_source(
            "Requirements.sysml",
            "standard library package Requirements {
                 abstract requirement def RequirementCheck { subject subj; }
             }",
        );
        model.add_source(
            "parameters.sysml",
            "package P {
                 requirement def Bare;
                 requirement def Own { subject vehicle; }
                 action def Run { in speed; }
                 action run : Run;
                 action trip { perform run; }
             }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        for (name, expected) in [
            ("P::Bare", &["subj"][..]),
            ("P::Own", &["vehicle"]),
            ("P::trip::run", &["speed"]),
        ] {
            let callee = r.resolve_qualified(name).unwrap();
            let parameters = r.callable_parameters(callee).unwrap();
            assert_eq!(names(&parameters), expected, "{name}");
            let inherited: Vec<ElementRef> = r
                .effective_features(callee, true)
                .into_iter()
                .filter(|&f| r.is_parameter(f))
                .collect();
            assert_eq!(
                parameters.iter().map(|p| p.element).collect::<Vec<_>>(),
                inherited,
                "{name}"
            );
        }
    }

    /// KerML's `checkFeatureParameterRedefinition` exempts only an
    /// invocation's argument that names what it redefines. A calculation's
    /// parameter that redefines one explicitly still takes over the general's
    /// parameter at its own position, so it stands for both.
    #[test]
    fn an_explicit_redefinition_does_not_release_the_position() {
        let mut model = Model::new();
        model.add_source(
            "positions.sysml",
            "calc def KineticEnergy { in m; in v; return ke = m * v * v / 2; }
             calc def ByVelocity :> KineticEnergy { in :>> v; }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let callee = r.resolve_qualified("ByVelocity").unwrap();
        let parameter = r.callable_parameters(callee).unwrap();
        assert_eq!(names(&parameter), ["v"]);
        let parameter = parameter[0].element;
        assert_eq!(r.owner(parameter), Some(callee));
        let m = r.resolve_qualified("KineticEnergy::m").unwrap();
        let v = r.resolve_qualified("KineticEnergy::v").unwrap();
        let mut targets = r.b.semantic_redefinition_targets(parameter.0, true);
        targets.sort_unstable();
        assert_eq!(targets, [m.0, v.0]);
        assert!(!r.effective_features(callee, true).contains(&m));
        assert_eq!(names(&r.calc_parameter_bindings(callee).unwrap()), ["v"]);
    }

    /// Positions pair parameters whatever their names: a reused name hides
    /// no inherited parameter at another position, and leaves the two
    /// inputs without a name to tell them apart.
    #[test]
    fn a_reused_name_hides_no_inherited_parameter() {
        let mut model = Model::new();
        model.add_source(
            "names.sysml",
            "calc def Diff { in a; in b; return r = a - b; }
             calc def Partial :> Diff { in b; }
             calc def Swapped :> Diff { in b; in a; }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let diff_a = r.resolve_qualified("Diff::a").unwrap();
        let diff_b = r.resolve_qualified("Diff::b").unwrap();
        let partial = r.resolve_qualified("Partial").unwrap();
        let partial_b = r.resolve_qualified("Partial::b").unwrap();
        assert_eq!(r.positional_redefinition_targets(partial_b), [diff_a]);
        let parameters = r.callable_parameters(partial).unwrap();
        assert_eq!(names(&parameters), ["b", "b"]);
        assert_eq!(parameters[0].element, partial_b);
        assert_eq!(parameters[1].element, diff_b);
        assert_eq!(r.calc_parameter_bindings(partial), None);
        let swapped = r.resolve_qualified("Swapped").unwrap();
        let swapped_b = r.resolve_qualified("Swapped::b").unwrap();
        let swapped_a = r.resolve_qualified("Swapped::a").unwrap();
        assert_eq!(r.positional_redefinition_targets(swapped_b), [diff_a]);
        assert_eq!(r.positional_redefinition_targets(swapped_a), [diff_b]);
        let parameters = r.calc_parameter_bindings(swapped).unwrap();
        assert_eq!(names(&parameters), ["b", "a"]);
        assert_eq!(parameters[0].element, swapped_b);
    }

    /// Ends, results and subjects pair with what the general owns, else with
    /// what it inherits.
    #[test]
    fn ends_results_and_subjects_pair_through_the_heritage() {
        let mut model = Model::new();
        model.add_source(
            "roles.sysml",
            "part def P1; part def P2;
             connection def Conn { end e1 : P1; end e2 : P2; }
             connection def Conn2 :> Conn { end f1; end f2; }
             connection def Conn3 :> Conn2;
             connection def Conn4 :> Conn3 { end g1; end g2; }
             calc def C1 { in i; return r : P1; }
             calc def C2 :> C1;
             calc def C3 :> C2 { return s; }
             requirement def R { subject sub : P1; }
             requirement def R2 :> R;
             requirement def R3 :> R2 { subject t; in x; }
             port def Q;
             interface def I { end port a : Q; end port b : ~Q; }
             part def W { port p : Q; }
             part def H { port q : ~Q; }
             part def Sys { part w : W; part h : H; interface i : I connect w.p to h.q; }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let q = |r: &mut ResolvedModel, name: &str| r.resolve_qualified(name).unwrap();
        let (e1, e2) = (q(&mut r, "Conn::e1"), q(&mut r, "Conn::e2"));
        let (f1, f2) = (q(&mut r, "Conn2::f1"), q(&mut r, "Conn2::f2"));
        assert_eq!(r.positional_redefinition_targets(f1), [e1]);
        assert_eq!(r.positional_redefinition_targets(f2), [e2]);
        let g1 = q(&mut r, "Conn4::g1");
        assert_eq!(r.positional_redefinition_targets(g1), [f1]);
        let (c1_r, c3_s) = (q(&mut r, "C1::r"), q(&mut r, "C3::s"));
        assert_eq!(r.positional_redefinition_targets(c3_s), [c1_r]);
        let (sub, t) = (q(&mut r, "R::sub"), q(&mut r, "R3::t"));
        assert_eq!(r.positional_redefinition_targets(t), [sub]);
        let x = q(&mut r, "R3::x");
        assert_eq!(r.positional_redefinition_targets(x), []);
        // The ends a `connect` clause declares pair with the definition's.
        let (a, b) = (q(&mut r, "I::a"), q(&mut r, "I::b"));
        let i = q(&mut r, "Sys::i");
        let ends: Vec<_> = r
            .owned_members(i)
            .into_iter()
            .filter(|&e| {
                r.element_properties(e)
                    .get("isEnd")
                    .and_then(|v| v.as_bool())
                    == Some(true)
            })
            .collect();
        assert_eq!(ends.len(), 2);
        assert_eq!(r.positional_redefinition_targets(ends[0]), [a]);
        assert_eq!(r.positional_redefinition_targets(ends[1]), [b]);
    }

    /// An inherited parameter that another inherited one redefines is no
    /// slot of the type inheriting both (`r` under `B1` redefines `A::p`,
    /// which `B2` inherits), whichever general is written first; and a
    /// parameter redefined by a qualified `:>>` is no slot either.
    #[test]
    fn redefined_inherited_parameters_are_no_slots() {
        let mut model = Model::new();
        model.add_source(
            "slots.sysml",
            "calc def A { in p; in q; }
             calc def B1 :> A { in r; }
             calc def B2 :> A;
             calc def G :> B1, B2;
             calc def G2 :> B2, B1;
             calc def H :> G { in x; in y; in z; }
             calc def H2 :> G2 { in x; in y; in z; }
             calc def B :> A { in z :>> A::q; }
             calc def C :> B { in m; in n; }",
        );
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let q = |r: &mut ResolvedModel, name: &str| r.resolve_qualified(name).unwrap();
        let (p, qq, rr) = (q(&mut r, "A::p"), q(&mut r, "A::q"), q(&mut r, "B1::r"));
        for (general, first, second) in [("G", rr, qq), ("G2", qq, rr)] {
            let general = q(&mut r, general);
            let parameters: Vec<_> = r
                .callable_parameters(general)
                .unwrap()
                .into_iter()
                .map(|parameter| parameter.element)
                .collect();
            assert_eq!(parameters, [first, second]);
            assert!(!r.effective_features(general, true).contains(&p));
        }
        for (specialization, first, second) in [("H", rr, qq), ("H2", qq, rr)] {
            let x = q(&mut r, &format!("{specialization}::x"));
            let y = q(&mut r, &format!("{specialization}::y"));
            let z = q(&mut r, &format!("{specialization}::z"));
            assert_eq!(r.positional_redefinition_targets(x), [first]);
            assert_eq!(r.positional_redefinition_targets(y), [second]);
            assert_eq!(r.positional_redefinition_targets(z), []);
        }
        let z = q(&mut r, "B::z");
        let m = q(&mut r, "C::m");
        let n = q(&mut r, "C::n");
        assert_eq!(r.positional_redefinition_targets(m), [z]);
        assert_eq!(r.positional_redefinition_targets(n), []);
        let c = q(&mut r, "C");
        assert_eq!(names(&r.callable_parameters(c).unwrap()), ["m", "n"]);
    }

    #[test]
    fn lambda_sites_are_unit_scoped_and_ambiguous_sites_are_rejected() {
        let mut model = Model::new();
        for package in ["A", "B"] {
            model.add_source(
                format!("{package}.sysml"),
                &format!("package {package} {{ attribute value = (1,2)->collect {{ in p; p }}; calc def Shadow {{ in p; }} }}"),
            );
        }
        assert!(!model.has_errors());
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A::value").unwrap();
        let b = r.resolve_qualified("B::value").unwrap();
        let (_, expression) = r.value_expr(a).unwrap();
        let body = lambda_body(&expression);
        let (scope_a, bindings_a) = r.lambda_parameter_bindings(a, body).unwrap();
        let (scope_b, bindings_b) = r.lambda_parameter_bindings(b, body).unwrap();
        assert_eq!(bindings_a[0].name, "p");
        assert_ne!(bindings_a[0].element, bindings_b[0].element);
        assert_ne!(scope_a, scope_b);
        assert_eq!(r.b.scopes[scope_a.0].owner, None);
        // A retained prefix index with an old length stamp must rebuild.
        let index = r.b.parameter_sites.as_mut().unwrap();
        index.elements_len = 0;
        index.sites.clear();
        assert_eq!(
            r.lambda_parameter_bindings(a, body),
            Some((scope_a, bindings_a.clone()))
        );
        // Two declarations claimed at one source site cannot select arbitrarily.
        let span = *r.b.member_spans.get(&bindings_a[0].element.0).unwrap();
        let duplicate = r.resolve_qualified("A::Shadow::p").unwrap();
        r.b.member_spans.insert(duplicate.0, span);
        r.b.parameter_sites = None;
        assert!(r.lambda_parameter_bindings(a, body).is_none());
        assert_eq!(r.b.owner_scope_of(bindings_b[0].element.0), Some(scope_b.0));
    }

    #[test]
    fn populated_prepared_parameter_index_rebuilds_after_user_append() {
        use crate::prepared::PreparedLibrary;
        use std::sync::Arc;

        let mut library_model = Model::new();
        library_model.add_library_source(
            "library.sysml",
            "package L { attribute value = (1,2)->collect { in p; p }; }",
        );
        let prepared = PreparedLibrary::build(&library_model).unwrap();
        let decoded = PreparedLibrary::from_bytes(&prepared.to_bytes(19).unwrap(), 19).unwrap();
        // In-memory preparation retains already-parsed syntax; decoding starts
        // cold. Neither path should hydrate another unit for parameter lookup.
        for (mode, mut prepared) in [prepared, decoded].into_iter().enumerate() {
            let library_owner = prepared
                .builder
                .resolve(0, &super::super::lib_qn("L::value"), 0)
                .unwrap();
            let expression = prepared
                .builder
                .values
                .get(&library_owner)
                .unwrap()
                .1
                .clone();
            let (_, original) = prepared
                .builder
                .lambda_parameter_bindings(0, lambda_body(&expression))
                .unwrap();
            let library_elements = prepared.builder.elements.len();
            assert_eq!(
                prepared
                    .builder
                    .parameter_sites
                    .as_ref()
                    .unwrap()
                    .elements_len,
                library_elements
            );
            let prepared = Arc::new(prepared);
            let mut model = Model::new();
            Arc::clone(&prepared).install(&mut model).unwrap();
            let initially_loaded = model.loaded_library_unit_count();
            assert_eq!(initially_loaded, usize::from(mode == 0));
            model.add_source(
                "user.sysml",
                "package U { attribute value = (3,4)->collect { in p; p }; }",
            );
            let mut r = ResolvedModel::build(&model);
            assert!(r.b.elements.shares_prefix(&prepared.builder.elements));
            assert!(r.b.elements.len() > library_elements);
            let user_owner = r.resolve_qualified("U::value").unwrap();
            let (_, expression) = r.value_expr(user_owner).unwrap();
            let (_, user) = r
                .lambda_parameter_bindings(user_owner, lambda_body(&expression))
                .unwrap();
            assert_eq!(user.len(), 1);
            assert_ne!(user[0].element, original[0].element);
            assert_eq!(r.b.unit_of_elem(user[0].element.0), 1);
            assert_eq!(
                r.b.parameter_sites.as_ref().unwrap().elements_len,
                r.b.elements.len()
            );
            assert_eq!(
                prepared
                    .builder
                    .parameter_sites
                    .as_ref()
                    .unwrap()
                    .elements_len,
                library_elements
            );
            assert_eq!(model.loaded_library_unit_count(), initially_loaded);
        }
    }

    #[test]
    fn exact_missing_reference_is_distinct_from_lexical_resolution() {
        const ID: &str = "77777777-7777-4777-8777-777777777777";
        let mut model = Model::new();
        model.add_source(
            "a.sysml",
            &format!("attribute '{ID}' = 1; attribute value = '{ID}';"),
        );
        let mut r = ResolvedModel::build(&model);
        let owner = r.resolve_qualified("value").unwrap();
        let ordinary = r.resolve_qualified(&format!("'{ID}'")).unwrap();
        let (scope, expression) = r.value_expr(owner).unwrap();
        let ExprKind::Ref(name) = expression.kind else {
            panic!("expected reference");
        };
        assert_eq!(
            r.reference_identity(scope, &name),
            ReferenceIdentity {
                target: Some(ordinary),
                identity_bound: false
            }
        );
        let id = ID.parse().unwrap();
        let span = name.segments[0].span;
        r.b.id_spelled_targets
            .insert((0, span.start, span.end), (id, id));
        assert_eq!(
            r.with_source(owner, |r| r.reference_identity(scope, &name)),
            ReferenceIdentity {
                target: None,
                identity_bound: true
            }
        );
    }

    #[test]
    fn signature_cache_requires_ready_recorded_heritage() {
        let mut model = Model::new();
        model.add_source(
            "signatures.sysml",
            "calc def Base { in p; } calc def Child :> Base;
             calc def Missing :> absent;
             calc def Duplicate { in p; in p; } calc def Empty;",
        );
        let mut r = ResolvedModel::build(&model);
        let base = r.resolve_qualified("Base").unwrap();
        let child = r.resolve_qualified("Child").unwrap();
        let missing = r.resolve_qualified("Missing").unwrap();
        let duplicate = r.resolve_qualified("Duplicate").unwrap();
        let empty = r.resolve_qualified("Empty").unwrap();
        r.b.parameter_signatures = None;
        r.b.semantic_ready = false;
        let expected = r.calc_parameter_bindings(base).unwrap();
        assert!(r.b.parameter_signatures.is_none());
        r.b.semantic_ready = true;
        assert_eq!(r.calc_parameter_bindings(child), Some(expected.clone()));
        assert_eq!(r.calc_parameter_bindings(child), Some(expected));
        assert_eq!(r.calc_parameter_bindings(missing), Some(Vec::new()));
        assert_eq!(r.calc_parameter_bindings(duplicate), None);
        assert_eq!(r.calc_parameter_bindings(empty), Some(Vec::new()));
        let cache = r.b.parameter_signatures.as_ref().unwrap();
        assert!(cache.signatures.contains_key(&child.0));
        assert!(!cache.signatures.contains_key(&missing.0));
        assert_eq!(cache.signatures.get(&duplicate.0), Some(&None));
        assert_eq!(cache.signatures.get(&empty.0), Some(&Some(Vec::new())));
        r.b.reset_lookup_caches();
        assert!(r.b.parameter_signatures.is_none());
    }

    #[test]
    fn signature_cache_does_not_survive_identity_rebinding() {
        const ID: &str = "88888888-8888-4888-8888-888888888888";
        let mut model = Model::new();
        model.add_source(
            "identity.sysml",
            &format!(
                "calc def Actual {{ in actual; }} calc def '{ID}' {{ in ordinary; }}
                 calc def Child :> '{ID}';"
            ),
        );
        let mut r = ResolvedModel::build(&model);
        let actual = r.resolve_qualified("Actual").unwrap();
        let ordinary = r.resolve_qualified(&format!("'{ID}'")).unwrap();
        let child = r.resolve_qualified("Child").unwrap();
        let sites = r.references_to(ordinary);
        assert_eq!(sites.len(), 1);
        let mut hints = HashMap::from([(
            (r.element_id(sites[0].owner), sites[0].kind.clone()),
            ID.parse().unwrap(),
        )]);
        assert_eq!(
            r.calc_parameter_bindings(child).unwrap()[0].name,
            "ordinary"
        );
        assert!(
            r.b.parameter_signatures
                .as_ref()
                .unwrap()
                .signatures
                .contains_key(&child.0)
        );
        r.override_ids(&HashMap::from([(
            r.element_id(actual),
            ID.parse().unwrap(),
        )]));
        // Rewarm after remapping so the binding replay itself must invalidate.
        assert_eq!(
            r.calc_parameter_bindings(child).unwrap()[0].name,
            "ordinary"
        );
        assert!(
            r.bind_id_spelled_references_with(&mut hints)
                .contains(&ID.parse().unwrap())
        );
        let rebound = r.calc_parameter_bindings(child).unwrap();
        assert_eq!(rebound[0].name, "actual");
        assert_eq!(
            rebound[0].element,
            r.resolve_qualified("Actual::actual").unwrap()
        );
        assert_eq!(r.calc_parameter_bindings(child), Some(rebound));
    }
}
