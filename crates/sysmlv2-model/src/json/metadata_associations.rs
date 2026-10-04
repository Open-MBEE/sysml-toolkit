//! Shared positive Annotation association snapshots.
use super::Builder;
use crate::layered::LayeredMap;
use std::collections::BTreeMap;

/// Reference-resolution checkpoints restore this together with endpoint rows.
#[derive(Clone)]
pub(super) struct Snapshot {
    merged: LayeredMap<usize, Vec<usize>>,
    explicit: BTreeMap<usize, Vec<usize>>,
    incomplete: bool,
}
impl Builder {
    /// Intrinsic metadata survives removal/retargeting of explicit Annotations,
    /// even if a source identity eventually contributes through both routes.
    pub(super) fn record_intrinsic_metadata(&mut self, owner: usize, metadata: usize) {
        self.metadata_of.entry(owner).or_default().push(metadata);
        if self.metadata_association_generation.is_some() {
            self.metadata_association_generation = Some(std::sync::Arc::new(()));
        }
        if let Some(intrinsic) = &mut self.metadata_intrinsic {
            intrinsic.entry(owner).or_default().push(metadata);
        }
    }
    pub(super) fn metadata_snapshot(&self) -> Snapshot {
        Snapshot {
            merged: self.metadata_of.clone(),
            explicit: self.metadata_about.clone(),
            incomplete: self.metadata_associations_incomplete,
        }
    }
    pub(super) fn restore_metadata_snapshot(&mut self, snapshot: &Snapshot) {
        self.retain_library_prefix_for(&snapshot.merged);
        self.metadata_of = snapshot.merged.clone();
        self.metadata_about = snapshot.explicit.clone();
        self.metadata_associations_incomplete = snapshot.incomplete;
        self.metadata_association_generation = Some(std::sync::Arc::new(()));
        self.reset_lookup_caches();
    }
    /// The frozen library prefix of the recorded lookup graph and the frozen
    /// library results of the semantic memo read the metadata of library
    /// owners only, so they outlive a change confined to user rows — every
    /// reference-resolution pass restores metadata. Results over user rows
    /// are dropped either way. (A user relationship that reaches a library
    /// row drops the library results once the build completes.)
    fn retain_library_prefix_for(&mut self, next: &LayeredMap<usize, Vec<usize>>) {
        let boundary = self.lib_boundary;
        if self.metadata_of.agrees_on(next, |&owner| owner < boundary) {
            self.semantic_memo.clear_local();
        } else {
            self.recorded_lookup_prefix = None;
            self.semantic_memo = Default::default();
        }
    }
    /// Called only between complete reference-resolution passes or at an
    /// explicit public mutation boundary. No partially updated association is
    /// visible to another pending reference in the same pass.
    pub(super) fn refresh_metadata_associations(&mut self) -> bool {
        if self.explicit_metadata_annotations.is_empty() {
            return false;
        }
        if self.metadata_intrinsic.is_none() {
            self.metadata_intrinsic = Some(self.metadata_of.clone());
        }
        // A failed fixed-point pass cannot be repaired merely by observing its
        // restored bootstrap endpoints after ID assignment or binding replay.
        if self.recorded_lookup_incomplete {
            return self.replace_metadata_associations(BTreeMap::new(), true);
        }
        let mut steps = 0;
        let raw = super::structural_index::StoredStructure::for_annotations(self, &mut steps);
        let mut next: BTreeMap<usize, Vec<usize>> = BTreeMap::new();
        let mut incomplete = true;
        if let Some(raw) = raw.filter(|raw| raw.ids_unique) {
            incomplete = raw.annotations_incomplete;
            for (&target, sources) in &raw.metadata_annotation_sources {
                steps = steps.saturating_add(sources.len());
                if steps > crate::eval::MAX_STEPS {
                    next.clear();
                    incomplete = true;
                    break;
                }
                // Sources are recorded in relationship order; sort by the
                // immutable declaration index to combine all annotation forms.
                let mut sources = sources.clone();
                sources.sort_unstable();
                sources.dedup();
                next.insert(target, sources);
            }
        }
        self.replace_metadata_associations(next, incomplete)
    }
    pub(super) fn discard_unstable_metadata_associations(&mut self) {
        self.replace_metadata_associations(BTreeMap::new(), true);
    }
    fn replace_metadata_associations(
        &mut self,
        mut next: BTreeMap<usize, Vec<usize>>,
        incomplete: bool,
    ) -> bool {
        // Empty entries retain touched-target history for prepared Facts.
        // They contribute no metadata, but ensure removal recomputes the old
        // library target's context even when intrinsic metadata remains there.
        for &target in self.metadata_about.keys() {
            next.entry(target).or_default();
        }
        if self.metadata_about == next && self.metadata_associations_incomplete == incomplete {
            return false;
        }
        let mut merged = self
            .metadata_intrinsic
            .as_ref()
            .expect("intrinsic snapshot")
            .clone();
        for (&target, sources) in &next {
            let list = merged.entry(target).or_default();
            list.extend(sources.iter().copied());
            list.sort_unstable();
            list.dedup();
        }
        self.retain_library_prefix_for(&merged);
        self.metadata_of = merged;
        self.metadata_about = next;
        self.metadata_associations_incomplete = incomplete;
        self.metadata_association_generation = Some(std::sync::Arc::new(()));
        // Element rows need not change when this semantic input changes.
        self.reset_lookup_caches();
        true
    }
}

#[cfg(test)]
mod tests {
    //! Include in json/metadata_associations.rs as child tests module.
    use crate::{json::ResolvedModel, model::Model};
    /// Every replay pass restores the metadata snapshot. The frozen library
    /// prefix of the recorded lookup graph survives those restores while
    /// library owners' metadata is unchanged; an annotation about a library
    /// element drops it.
    #[test]
    fn replay_keeps_library_lookup_prefix_unless_library_metadata_changes() {
        let mut base = Model::new();
        base.add_library_source(
            "lib.kerml",
            "standard library package L { metaclass Mark; \
             class A { feature x; } class B :> A { feature redefines x; } }",
        );
        let prepared = base.prepare_library().unwrap();
        for (source, kept) in [
            ("class C :> L::B { feature redefines x; }", true),
            (
                "class C :> L::B { feature redefines x; } @L::Mark about L::A;",
                false,
            ),
        ] {
            let mut model = Model::new();
            std::sync::Arc::clone(&prepared)
                .install(&mut model)
                .unwrap();
            assert!(
                model
                    .add_source("user.kerml", source)
                    .diagnostics
                    .is_empty()
            );
            let r = ResolvedModel::build(&model);
            assert!(r.b.lib_boundary > 0, "built on the prepared library");
            assert_eq!(r.b.recorded_lookup_prefix.is_some(), kept, "{source}");
        }
    }
    /// The frozen library results of the semantic memo survive those
    /// restores the same way; results over user rows do not.
    #[test]
    fn replay_keeps_library_semantic_results_unless_library_metadata_changes() {
        let mut base = Model::new();
        base.add_library_source(
            "lib.kerml",
            "standard library package MeasurementReferences { datatype MeasurementUnit; } \
             standard library package L { metaclass Mark; datatype D; \
             class A { feature x; } class B :> A { feature redefines x; } \
             feature m : MeasurementReferences::MeasurementUnit; }",
        );
        let prepared = base.prepare_library().unwrap();
        assert!(prepared.builder.semantic_memo.units.iter().next().is_some());
        for (source, kept) in [
            ("class C :> L::B { feature redefines x; }", true),
            (
                "class C :> L::B { feature redefines x; } @L::Mark about L::A;",
                false,
            ),
        ] {
            let mut model = Model::new();
            std::sync::Arc::clone(&prepared)
                .install(&mut model)
                .unwrap();
            assert!(
                model
                    .add_source("user.kerml", source)
                    .diagnostics
                    .is_empty()
            );
            let r = ResolvedModel::build(&model);
            assert!(r.b.lib_boundary > 0, "built on the prepared library");
            let memo = &r.b.semantic_memo;
            assert_eq!(memo.units.iter().next().is_some(), kept, "{source}");
            assert_eq!(memo.types.iter().next().is_some(), kept, "{source}");
        }
        // A restore drops the results over user rows and keeps the library's.
        let mut model = Model::new();
        prepared.install(&mut model).unwrap();
        model.add_source("user.kerml", "datatype E;");
        let mut r = ResolvedModel::build(&model);
        let user = r.resolve_qualified("E").unwrap();
        r.quantity_dims_of_type(user);
        let key = (user.0, crate::eval::unit_spelling_expansion());
        assert!(r.b.semantic_memo.types.get(&key).is_some());
        let library = r.b.semantic_memo.types.iter().count() - 1;
        let snapshot = r.b.metadata_snapshot();
        r.b.restore_metadata_snapshot(&snapshot);
        assert!(r.b.semantic_memo.types.get(&key).is_none());
        assert_eq!(r.b.semantic_memo.types.iter().count(), library);
    }
    fn fixture() -> (ResolvedModel, usize, usize, usize) {
        let mut model = Model::new();
        assert!(
            model
                .add_source(
                    "associations.kerml",
                    "metaclass Mark; #Mark class A; class B; @Mark about A;"
                )
                .diagnostics
                .is_empty()
        );
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let b = r.resolve_qualified("B").unwrap().0;
        let ann =
            r.b.elements
                .iter()
                .position(|e| e.ty == "Annotation")
                .unwrap();
        (r, a, b, ann)
    }
    #[test]
    fn retarget_missing_and_malformed_remove_only_explicit_contributions() {
        let (mut r, a, b, ann) = fixture();
        let original = r.b.metadata_of.get(&a).unwrap().clone();
        assert_eq!(original.len(), 2);
        let target = r.b.elements[b].id;
        r.b.elements[ann].props.insert(
            "annotatedElement",
            serde_json::json!({"@id":target.to_string()}),
        );
        assert!(r.b.refresh_metadata_associations());
        assert_eq!(r.b.metadata_of.get(&a).unwrap(), &original[..1]);
        assert_eq!(r.b.metadata_of.get(&b).unwrap(), &original[1..]);
        assert!(!r.b.metadata_associations_incomplete);
        let good = r.b.elements[ann].props.clone();
        for malformed in [false, true] {
            r.b.elements[ann].props = good.clone();
            if malformed {
                r.b.elements[ann]
                    .props
                    .insert("source", serde_json::json!([{"@id":target.to_string()}]));
            } else {
                r.b.elements[ann]
                    .props
                    .insert("annotatedElement", serde_json::json!({"@ref":"Missing"}));
            }
            assert!(r.b.refresh_metadata_associations());
            assert!(r.b.metadata_of.get(&b).is_none_or(|items| items.is_empty()));
            assert_eq!(r.b.metadata_of.get(&a).unwrap(), &original[..1]);
            assert!(r.b.metadata_associations_incomplete);
            r.b.elements[ann].props = good.clone();
            assert!(r.b.refresh_metadata_associations());
            assert!(!r.b.metadata_associations_incomplete);
        }
    }
    #[test]
    fn restored_snapshot_and_nonconvergence_preserve_intrinsic_metadata() {
        let (mut r, a, b, ann) = fixture();
        let original = r.b.metadata_of.get(&a).unwrap().clone();
        let snapshot = r.b.metadata_snapshot();
        let props = r.b.elements[ann].props.clone();
        let target = r.b.elements[b].id;
        r.b.elements[ann].props.insert(
            "annotatedElement",
            serde_json::json!({"@id":target.to_string()}),
        );
        r.b.refresh_metadata_associations();
        r.b.elements[ann].props = props;
        r.b.restore_metadata_snapshot(&snapshot);
        assert_eq!(r.b.metadata_of.get(&a).unwrap(), &original);
        assert!(r.b.metadata_of.get(&b).is_none_or(|items| items.is_empty()));
        r.b.discard_unstable_metadata_associations();
        assert_eq!(r.b.metadata_of.get(&a).unwrap(), &original[..1]);
        assert!(r.b.metadata_associations_incomplete);
        assert!(r.b.refresh_metadata_associations());
        assert_eq!(r.b.metadata_of.get(&a).unwrap(), &original);
    }
    #[test]
    fn duplicate_identity_cannot_keep_a_warmed_explicit_association() {
        let (mut r, a, b, _) = fixture();
        let original = r.b.metadata_of.get(&a).unwrap().clone();
        let prior = r.b.elements[b].id;
        r.b.elements[b].id = r.b.elements[a].id;
        assert!(r.b.refresh_metadata_associations());
        assert!(r.b.metadata_associations_incomplete);
        assert_eq!(r.b.metadata_of.get(&a).unwrap(), &original[..1]);
        r.b.elements[b].id = prior;
        assert!(r.b.refresh_metadata_associations());
        assert!(!r.b.metadata_associations_incomplete);
        assert_eq!(r.b.metadata_of.get(&a).unwrap(), &original);
    }

    #[test]
    fn failed_resolution_cannot_be_readmitted_by_final_identity_refresh() {
        let (mut r, a, _, _) = fixture();
        let original = r.b.metadata_of.get(&a).unwrap().clone();
        r.b.discard_unstable_metadata_associations();
        r.b.recorded_lookup_incomplete = true;
        assert!(!r.b.refresh_metadata_associations());
        assert!(r.b.metadata_associations_incomplete);
        assert_eq!(r.b.metadata_of.get(&a).unwrap(), &original[..1]);
        // This is the same final-ID boundary used by normal model construction.
        let roots =
            r.b.unit_starts
                .iter()
                .map(|&(root, _)| root)
                .collect::<Vec<_>>();
        r.b.assign_user_ids(0, &roots);
        assert!(r.b.metadata_associations_incomplete);
        assert_eq!(r.b.metadata_of.get(&a).unwrap(), &original[..1]);
        assert!(r.b.metadata_about.get(&a).unwrap().is_empty());
    }
    #[test]
    fn same_row_snapshot_uncertainty_cannot_reuse_provider_positive() {
        let mut model = Model::new();
        model.add_source(
            "unaffected.kerml",
            "class A; class B; metaclass M; @M about B;",
        );
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let scope = *r.b.elem_scope.get(&a).unwrap();
        let snapshot = r.b.metadata_snapshot();
        let mut proof = super::super::provider_completeness::ProviderCompleteness::default();
        assert!(proof.scope(&mut r.b, scope, &mut 0));
        r.b.discard_unstable_metadata_associations();
        assert!(!proof.scope(&mut r.b, scope, &mut 0));
        r.b.restore_metadata_snapshot(&snapshot);
        assert!(proof.scope(&mut r.b, scope, &mut 0));
    }
    #[test]
    fn prepared_facts_refresh_old_and_new_library_targets_on_retarget() {
        let mut base = Model::new();
        let library = "standard library package Base {classifier Anything;} standard library package Occurrences {class Occurrence specializes Base::Anything;} standard library package Metaobjects {metaclass SemanticMetadata {feature baseType;}} metaclass U; class A; metaclass Tagged :> Metaobjects::SemanticMetadata {:>> baseType=A meta U;} class C; class D; @Tagged about C;";
        assert!(
            base.add_library_source("about-library.kerml", library)
                .diagnostics
                .is_empty()
        );
        let prepared = base.prepare_library().unwrap();
        let mut model = Model::new();
        prepared.install(&mut model).unwrap();
        model.add_source("user.kerml", "class User;");
        let mut r = ResolvedModel::build(&model);
        let a = r.resolve_qualified("A").unwrap().0;
        let c = r.resolve_qualified("C").unwrap().0;
        let d = r.resolve_qualified("D").unwrap().0;
        assert!(r.b.library_facts.is_some());
        assert!(
            crate::check::facts::Facts::new(&mut r.b)
                .context(c)
                .contains(&a)
        );
        let ann =
            r.b.elements
                .iter()
                .position(|e| e.ty == "Annotation")
                .unwrap();
        let target = r.b.elements[d].id;
        r.b.elements[ann].props.insert(
            "annotatedElement",
            serde_json::json!({"@id":target.to_string()}),
        );
        assert!(r.b.refresh_metadata_associations());
        assert!(r.b.metadata_about.get(&c).unwrap().is_empty());
        let facts = crate::check::facts::Facts::new(&mut r.b);
        assert!(!facts.context(c).contains(&a));
        assert!(facts.context(d).contains(&a));
    }
    #[test]
    fn incomplete_or_multiple_metadata_casts_cannot_choose_first_boolean_binding() {
        for prefix in [false, true] {
            for first in [false, true] {
                let initial = if prefix {
                    format!("class C {{@M {{flag={first};}}}}")
                } else {
                    format!("class C; @M about C {{flag={first};}}")
                };
                for other in ["C", "Missing"] {
                    let mut model = Model::new();
                    let source = format!(
                        "metaclass M {{feature flag;}} {initial} @M about {other} {{flag={};}}",
                        !first
                    );
                    let parsed = model.add_source("attributes.kerml", &source);
                    assert!(parsed.diagnostics.is_empty(), "{:?}", parsed.diagnostics);
                    let mut r = ResolvedModel::build(&model);
                    let c = r.resolve_qualified("C").unwrap().0;
                    let qn = super::super::lib_qn("M");
                    let mut attr = super::super::lib_qn("flag");
                    attr.is_global = false;
                    assert_eq!(
                        r.b.metadata_attr_verdict(0, &qn, &attr, c, 0),
                        super::super::Tri::Unknown,
                        "{source}"
                    );
                }
            }
        }
    }
}
