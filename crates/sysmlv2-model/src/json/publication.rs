//! Publication permission and reentrancy, separate from logical semantic readiness.
//! This substrate adds no new materialization demand sites.
use std::sync::{
    Arc,
    atomic::{AtomicBool, Ordering},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Status {
    Ready,
    Construction,
    Reentrant,
}

#[derive(Default)]
pub(super) struct Control {
    enabled: bool,
    active: Option<Arc<AtomicBool>>,
    revision: Option<Arc<()>>,
}
impl Clone for Control {
    fn clone(&self) -> Self {
        Self {
            enabled: self.enabled,
            active: None,
            revision: self.revision.clone(),
        }
    }
}
#[derive(Clone, Default)]
pub(super) struct Revision(Option<Arc<()>>);
impl Revision {
    pub(super) fn next() -> Self {
        Self(Some(Arc::new(())))
    }
    pub(super) fn same_as(&self, other: &Self) -> bool {
        match (&self.0, &other.0) {
            (None, None) => true,
            (Some(a), Some(b)) => Arc::ptr_eq(a, b),
            _ => false,
        }
    }
}
pub(super) struct Guard(Arc<AtomicBool>);
impl Drop for Guard {
    fn drop(&mut self) {
        self.0.store(false, Ordering::Release);
    }
}
impl Control {
    pub(super) fn enable(&mut self) {
        self.enabled = true;
    }
    pub(super) fn suppress(&mut self) {
        self.enabled = false;
    }
    pub(super) fn begin(&mut self, semantic_ready: bool) -> Result<Guard, Status> {
        if !semantic_ready || !self.enabled {
            return Err(Status::Construction);
        }
        let active = self
            .active
            .get_or_insert_with(|| Arc::new(AtomicBool::new(false)));
        if active.swap(true, Ordering::AcqRel) {
            return Err(Status::Reentrant);
        }
        Ok(Guard(Arc::clone(active)))
    }
    pub(super) fn revision(&self) -> Revision {
        Revision(self.revision.clone())
    }
    pub(super) fn install(&mut self, revision: Revision) {
        self.revision = revision.0;
    }
    pub(super) fn published(&mut self) {
        self.install(Revision::next());
    }
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn readiness_permission_and_reentrancy_are_distinct() {
        let mut c = Control::default();
        assert!(matches!(c.begin(true), Err(Status::Construction)));
        c.enable();
        assert!(matches!(c.begin(false), Err(Status::Construction)));
        let g = c.begin(true).unwrap();
        assert!(matches!(c.begin(true), Err(Status::Reentrant)));
        drop(g);
        assert!(c.begin(true).is_ok());
        c.suppress();
        assert!(matches!(c.begin(true), Err(Status::Construction)));
    }
    #[test]
    fn unwind_releases_phase_without_publishing_or_reusing_revision() {
        let mut c = Control::default();
        c.enable();
        let before = c.revision();
        let _ = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let _g = c.begin(true).unwrap();
            panic!("preparation failed");
        }));
        assert!(before.same_as(&c.revision()));
        let _g = c.begin(true).unwrap();
        c.published();
        assert!(!before.same_as(&c.revision()));
        let first = c.revision();
        c.published();
        assert!(!first.same_as(&c.revision()));
    }
    #[test]
    fn clone_holds_snapshot_but_does_not_share_an_active_transaction() {
        let mut c = Control::default();
        c.enable();
        c.published();
        let _g = c.begin(true).unwrap();
        let mut copy = c.clone();
        assert!(c.revision().same_as(&copy.revision()));
        let _copy_guard = copy.begin(true).unwrap();
        copy.published();
        assert!(!c.revision().same_as(&copy.revision()));
    }
}
