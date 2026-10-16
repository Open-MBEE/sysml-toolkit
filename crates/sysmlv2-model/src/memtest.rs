//! The bytes live on the heap, counted at the allocator, for the tests
//! that measure what a structure holds: a step's kept bytes are the live
//! bytes after it less those before, and a drop's held bytes the reverse.
use std::alloc::{GlobalAlloc, Layout, System};
use std::sync::atomic::{AtomicUsize, Ordering::Relaxed};

/// The system allocator, counting live bytes.
struct Counting;
static LIVE: AtomicUsize = AtomicUsize::new(0);

// SAFETY: every call forwards to `System` with the caller's arguments; the
// counter is only bookkeeping.
unsafe impl GlobalAlloc for Counting {
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc(layout) };
        if !p.is_null() {
            LIVE.fetch_add(layout.size(), Relaxed);
        }
        p
    }
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        let p = unsafe { System.alloc_zeroed(layout) };
        if !p.is_null() {
            LIVE.fetch_add(layout.size(), Relaxed);
        }
        p
    }
    unsafe fn dealloc(&self, p: *mut u8, layout: Layout) {
        unsafe { System.dealloc(p, layout) };
        LIVE.fetch_sub(layout.size(), Relaxed);
    }
    unsafe fn realloc(&self, p: *mut u8, layout: Layout, size: usize) -> *mut u8 {
        let q = unsafe { System.realloc(p, layout, size) };
        if !q.is_null() {
            if size >= layout.size() {
                LIVE.fetch_add(size - layout.size(), Relaxed);
            } else {
                LIVE.fetch_sub(layout.size() - size, Relaxed);
            }
        }
        q
    }
}

#[global_allocator]
static ALLOCATOR: Counting = Counting;

/// The bytes live now.
pub(crate) fn live() -> usize {
    LIVE.load(Relaxed)
}

/// Run `step`, printing the bytes it kept under `label`.
pub(crate) fn kept<T>(label: &str, step: impl FnOnce() -> T) -> T {
    let start = live();
    let value = step();
    println!(
        "{label:<44} {:>+9.3} MB",
        (live() as f64 - start as f64) / 1e6
    );
    value
}

/// Run `drop_it`, printing the bytes it freed under `label`: what the
/// dropped member held.
pub(crate) fn held(label: &str, drop_it: impl FnOnce()) {
    let start = live();
    drop_it();
    println!(
        "{label:<44} {:>9.3} MB",
        (start as f64 - live() as f64) / 1e6
    );
}
