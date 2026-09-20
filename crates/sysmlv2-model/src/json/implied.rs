//! Implied relationships, materialized lazily in the resolved model.
//!
//! SysML 8.4.2 Tables 31/32 give every definition and usage kind a library
//! base it implicitly specializes (`part def` → `Parts::Part`, `part` →
//! `Parts::parts`, …) unless an explicit specialization of the covering
//! kind is written, and a variant usage implicitly specializes the
//! variation it is a variant of (SysML `checkUsageVariationDefinition-
//! Specialization` / `-UsageSpecialization`: a FeatureTyping to the
//! owning variation definition — an enumeration literal's typing — or a
//! Subsetting to the owning variation usage). These relationships are
//! part of the abstract syntax (`isImplied = true`, listed under the
//! specific element's `ownedRelationship` when `isImpliedIncluded`), but
//! the builder never creates them: the lowering keeps the element graph
//! at what the text says, and name resolution reads the same tables as
//! implied heritage instead ([`super::implicit_def_bases`]).
//!
//! The derivation layer materializes them on first demand for the whole
//! model — when the library bases are known, from a loaded library or a
//! name table ([`ResolvedModel::set_library_names`]); a model with
//! neither gets none at all, the variant specializations included, so
//! that `isImpliedIncluded` (false without a library) never contradicts
//! a listed implied relationship (KerML: `ownedRelationship->exists(isImplied)
//! implies isImpliedIncluded`). One relationship element per implied
//! specialization, appended
//! to the element list past every explicit element (`Builder::implied_from`
//! marks the boundary, so the checks, lints and iteration over the model
//! keep to the explicit elements), owned by its specific side through a
//! side table rather than the owner's `ownedRelationship` row — the
//! resolver, the expression evaluator and the language server keep the
//! explicit graph they were built on. The relationship families read the
//! side table ([`ResolvedModel::implied_relationships`]); the full-form
//! emitter takes its implied relationships from here.
//!
//! Ids are the emitter's: `uuid5(OID, "{owner id}/implied{n}")` with `n`
//! the relationship's position among its owner's implied ones — the
//! library bases in table order, then the variant specialization.

use super::{Elem, ElementRef, ResolvedModel, implicit_def_bases, implicit_usage_bases};
use crate::lift::{def_kind_of, usage_kind_of};
use crate::metaclass::conforms;
use serde_json::json;
use std::collections::HashMap;
use sysmlv2_syntax::ast::Dialect;
use uuid::Uuid;

/// One kind's implied specializations: the library bases (qualified
/// names), the relationship metaclass, its source and target keys, and
/// the explicit metaclasses that cover them.
type ImpliedBases = (
    &'static [&'static str],
    &'static str,
    &'static str,
    &'static str,
    &'static [&'static str],
);

/// The materialized implied relationships: their owners, and each
/// owner's list in order.
pub(super) struct ImpliedTable {
    /// Index of the first implied relationship in the element list.
    pub from: usize,
    /// Owner of the implied relationship at `from + k`.
    pub owner_of: Vec<usize>,
    /// Owner → its implied relationships, in order.
    pub by_owner: HashMap<usize, Vec<usize>>,
}

impl ResolvedModel {
    /// Materialize the implied relationships on first demand.
    pub(super) fn ensure_implied(&mut self) {
        if self.implied.is_some() {
            return;
        }
        self.ensure_by_id();
        self.ensure_rel_owner();
        let from = self.b.elements.len();
        let lib_by_name: HashMap<String, Uuid> = self
            .b
            .lib_qnames
            .iter()
            .map(|(id, segments)| (segments.join("::"), *id))
            .chain(
                self.external_by_name
                    .iter()
                    .map(|(name, id)| (name.clone(), *id)),
            )
            .collect();
        let mut owner_of: Vec<usize> = Vec::new();
        let mut by_owner: HashMap<usize, Vec<usize>> = HashMap::new();
        // User elements only, as the emitter did: the library's own
        // elements specialize explicitly. No bases known, nothing at all.
        let range = if lib_by_name.is_empty() {
            0..0
        } else {
            self.b.lib_boundary..from
        };
        for i in range {
            let plan = self.implied_plan(i, &lib_by_name);
            if plan.is_empty() {
                continue;
            }
            let owner_id = self.b.elements[i].id;
            for (n, (rel_ty, src_key, tgt_key, target)) in plan.into_iter().enumerate() {
                let id = Uuid::new_v5(
                    &Uuid::NAMESPACE_OID,
                    format!("{owner_id}/implied{n}").as_bytes(),
                );
                let mut props = crate::properties::Properties::new();
                props.insert("isImplied", json!(true));
                props.insert(src_key, json!({ "@id": owner_id.to_string() }));
                props.insert(tgt_key, json!({ "@id": target.to_string() }));
                self.b.elements.push(Elem {
                    ty: rel_ty,
                    id,
                    path: String::new(),
                    props,
                    owned_relationships: Default::default(),
                    children: Default::default(),
                    owning_relationship: None,
                });
                let idx = self.b.elements.len() - 1;
                owner_of.push(i);
                by_owner.entry(i).or_default().push(idx);
            }
        }
        self.b.implied_from = Some(from);
        self.implied = Some(ImpliedTable {
            from,
            owner_of,
            by_owner,
        });
        // The lazy maps are keyed on the element count: rebuild them so
        // the new relationships have ids and owners.
        self.ensure_by_id();
        self.rel_owner.clear();
        self.ensure_rel_owner();
    }

    /// The implied relationships element `i` gets: `(metaclass, source
    /// key, target key, target id)`, in emission order.
    fn implied_plan(
        &self,
        i: usize,
        lib_by_name: &HashMap<String, Uuid>,
    ) -> Vec<(&'static str, &'static str, &'static str, Uuid)> {
        let t = self.b.elements[i].ty;
        let mut plan = Vec::new();
        let explicit: Vec<usize> = self.b.elements[i].owned_relationships.to_vec();
        // Tables 31/32: the library bases of the element's kind, unless an
        // explicit specialization of the covering kind is present
        // (anti-redundancy, approximated as any explicit same-kind
        // specialization — the emitter's rule).
        let bases: Option<ImpliedBases> = if let Some(kind) = def_kind_of(t) {
            Some((
                implicit_def_bases(kind),
                "Subclassification",
                "subclassifier",
                "superclassifier",
                &["Subclassification", "Specialization"],
            ))
        } else {
            usage_kind_of(t, Dialect::Sysml).map(|kind| {
                (
                    implicit_usage_bases(kind),
                    "Subsetting",
                    "subsettingFeature",
                    "subsettedFeature",
                    &["Subsetting", "Redefinition", "ReferenceSubsetting"] as &[&str],
                )
            })
        };
        if let Some((bases, rel_ty, src, tgt, covering)) = bases {
            let covered = explicit
                .iter()
                .any(|&r| covering.contains(&self.b.elements[r].ty));
            if !covered {
                for base in bases {
                    if let Some(&id) = lib_by_name.get(*base) {
                        plan.push((rel_ty, src, tgt, id));
                    }
                }
            }
        }
        // A variant specializes the variation it belongs to: a typing by
        // the owning variation definition, a subsetting of the owning
        // variation usage — unless written explicitly. The specification
        // asks for a direct *or indirect* specialization; only a direct
        // one is recognized here (`variant part small : Sub` with `Sub :>
        // Box` still gets the implied typing by `Box`), the same
        // approximation as the covering rule above.
        if let Some(rel) = self.b.elements[i].owning_relationship {
            if self.b.elements[rel].ty == "VariantMembership" {
                if let Some(variation) = self.rel_owner[rel] {
                    let variation_id = self.b.elements[variation].id;
                    let targets = |kinds: &[&str], key: &str| -> bool {
                        explicit.iter().any(|&r| {
                            kinds.contains(&self.b.elements[r].ty)
                                && self.b.elements[r]
                                    .props
                                    .get(key)
                                    .and_then(|v| v.as_reference())
                                    == Some(variation_id)
                        })
                    };
                    let vty = self.b.elements[variation].ty;
                    if conforms(vty, "Definition") {
                        if !targets(&["FeatureTyping", "ConjugatedPortTyping"], "type") {
                            plan.push(("FeatureTyping", "typedFeature", "type", variation_id));
                        }
                    } else if conforms(vty, "Usage")
                        && !targets(
                            &["Subsetting", "Redefinition", "ReferenceSubsetting"],
                            "subsettedFeature",
                        )
                    {
                        plan.push((
                            "Subsetting",
                            "subsettingFeature",
                            "subsettedFeature",
                            variation_id,
                        ));
                    }
                }
            }
        }
        plan
    }

    /// The implied relationships `e` owns — the library specializations
    /// of its kind (SysML Tables 31/32) and a variant's specialization of
    /// its variation — as relationship elements of the model, in
    /// emission order. Materialized for the whole model on first call
    /// (see the module documentation); empty for a library element, and
    /// for every element of a model built without its library and
    /// without a library name table ([`Self::set_library_names`]).
    pub fn implied_relationships(&mut self, e: ElementRef) -> Vec<ElementRef> {
        self.ensure_implied();
        self.implied
            .as_ref()
            .and_then(|t| t.by_owner.get(&e.0))
            .map(|v| v.iter().copied().map(ElementRef).collect())
            .unwrap_or_default()
    }

    /// `Element::ownedRelationship` with the implied relationships
    /// included, as the specification lists them: the explicit ones in
    /// declaration order, then the implied ones.
    pub(super) fn d_owned_relationships(&mut self, e: ElementRef) -> Vec<ElementRef> {
        let mut out = self.owned_relationships(e);
        out.extend(self.implied_relationships(e));
        out
    }

    /// Whether `e` is a materialized implied relationship.
    pub fn is_implied(&self, e: ElementRef) -> bool {
        self.implied.as_ref().is_some_and(|t| e.0 >= t.from)
    }
}
