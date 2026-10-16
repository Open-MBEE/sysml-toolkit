//! The features a constructor's positional arguments bind, in order.
//!
//! `new T(a, b)` makes a result whose owned features redefine, one each,
//! the public features of `T` — the `i`-th argument the `i`-th feature of
//! `T` in `Type::feature` order: `T`'s own features in declaration order,
//! then those of each written general in the order the generals are
//! written, each general's own before the ones it inherits, leaving out
//! every feature a nearer one redefines or hides by name. Whether a
//! feature already carries a value plays no part in the position: an
//! argument landing on a bound feature is an overriding, which the
//! semantic checks report. Features inherited through the implied
//! library bases of a definition's kind follow these and are not listed,
//! so an argument past the features of the type and its written generals
//! is unplaced here, not unbound.
use super::{Builder, ElementRef, ResolvedModel};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// The sequences memoized for one state of a semantically ready graph.
#[derive(Clone, Default)]
pub(crate) struct ConstructorSequences {
    elements_len: usize,
    sequences: HashMap<usize, Arc<Vec<(String, usize)>>>,
}

impl Builder {
    /// The public features of `ty` a constructor binds by position, in
    /// binding order (see the module notes), each with the name a named
    /// argument binds it by — empty for a feature nothing names (an
    /// invariant, a result expression). Memoized per type once the graph
    /// is semantically ready, for the state of the rows it was made on.
    pub(crate) fn constructor_feature_sequence(&mut self, ty: usize) -> Arc<Vec<(String, usize)>> {
        if self.semantic_ready {
            let stale = self
                .constructor_sequences
                .as_ref()
                .is_none_or(|c| c.elements_len != self.elements.len());
            if stale {
                self.constructor_sequences = Some(ConstructorSequences {
                    elements_len: self.elements.len(),
                    sequences: HashMap::new(),
                });
            }
            if let Some(hit) = self
                .constructor_sequences
                .as_ref()
                .and_then(|c| c.sequences.get(&ty))
            {
                return Arc::clone(hit);
            }
        }
        let sequence = Arc::new(self.compute_constructor_sequence(ty));
        if self.semantic_ready {
            if let Some(cache) = self.constructor_sequences.as_mut() {
                cache.sequences.insert(ty, Arc::clone(&sequence));
            }
        }
        sequence
    }

    fn compute_constructor_sequence(&mut self, ty: usize) -> Vec<(String, usize)> {
        // The closure in binding order: the type, then its written
        // generals depth-first in declaration order.
        let mut order = Vec::new();
        let mut seen: HashSet<usize> = HashSet::new();
        let mut stack = vec![ty];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            order.push(t);
            let generals = self.explicit_supertype_elems(t);
            stack.extend(generals.into_iter().rev());
        }
        // A feature any member of the closure redefines is replaced by its
        // redefiner and leaves the sequence wherever it was declared.
        let mut shadowed: HashSet<usize> = HashSet::new();
        for &t in &order {
            for f in self.owned_member_elems(t, true) {
                shadowed.extend(self.redefinition_target_elems(f));
            }
        }
        let mut out: Vec<(String, usize)> = Vec::new();
        let mut names: HashSet<String> = HashSet::new();
        for &t in &order {
            for f in self.owned_member_elems(t, true) {
                if shadowed.contains(&f) {
                    continue;
                }
                // A nearer feature of the same name, of any visibility,
                // hides an inherited one: the hidden feature is not a
                // member of the subtype.
                let name = self.id_name(f).unwrap_or_default();
                let fresh = name.is_empty() || names.insert(name.clone());
                if !fresh || !self.member_is_public(f) {
                    continue;
                }
                out.push((name, f));
            }
        }
        out
    }

    /// The nearest feature along `feature`'s redefinition chain — itself
    /// first — that carries a value which is not a default: what an
    /// argument bound to `feature` would override, which
    /// `validateFeatureValueOverriding` forbids.
    pub(crate) fn non_default_binding(&mut self, feature: usize) -> Option<usize> {
        let mut seen = HashSet::new();
        let mut stack = vec![feature];
        while let Some(f) = stack.pop() {
            if !seen.insert(f) {
                continue;
            }
            if self.values.contains_key(&f) && !self.default_values.contains(&f) {
                return Some(f);
            }
            stack.extend(self.redefinition_target_elems(f));
        }
        None
    }

    /// The declared types a value bound to `feature` must inhabit: its own
    /// typings, else those of the nearest features along its redefinition
    /// chain that declare any (an untyped redefinition of an untyped
    /// redefinition borrows from further up).
    pub(crate) fn declared_or_borrowed_typings(&mut self, feature: usize) -> Vec<usize> {
        let mut frontier = vec![feature];
        let mut seen: HashSet<usize> = HashSet::new();
        while !frontier.is_empty() {
            let mut tys: Vec<usize> = Vec::new();
            let mut next = Vec::new();
            for f in frontier {
                if !seen.insert(f) {
                    continue;
                }
                for ty in self.direct_typing_elems(f) {
                    if !tys.contains(&ty) {
                        tys.push(ty);
                    }
                }
                next.extend(self.redefinition_target_elems(f));
            }
            if !tys.is_empty() {
                return tys;
            }
            frontier = next;
        }
        Vec::new()
    }

    /// Whether the membership `f` is owned through is public — the only
    /// visibility a constructor argument may bind (an unspelled
    /// visibility is public).
    fn member_is_public(&self, f: usize) -> bool {
        let Some(rel) = self.elements[f].owning_relationship else {
            return true;
        };
        match self.elements[rel].props.get("visibility") {
            None => true,
            Some(v) => v.as_str() == Some("public"),
        }
    }
}

impl ResolvedModel {
    /// The public features a constructor of `ty` binds, in the order its
    /// positional arguments take them (the first argument binds the first
    /// feature), each with the name a named argument binds it by — an
    /// empty name is a feature nothing can name, such as an invariant.
    /// The type's own features in declaration order, then those of each
    /// written general — depth-first, in the order the generals are
    /// written — minus the ones a nearer feature redefines or hides by
    /// name. Features inherited through the implied library bases of the
    /// type's kind follow these and are not listed. An unresolved or
    /// typeless `ty` answers an empty sequence.
    pub fn constructor_features(&mut self, ty: ElementRef) -> Vec<(String, ElementRef)> {
        self.b
            .constructor_feature_sequence(ty.0)
            .iter()
            .map(|(name, e)| (name.clone(), ElementRef(*e)))
            .collect()
    }
}
