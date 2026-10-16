//! Threads for the independent parts of a library load.
//!
//! Every path here has a sequential twin that runs the same work in the
//! same order to the same result: a target without threads (wasm), a
//! machine with one core, a host that refuses a thread, or a run asked for
//! one thread (`SYSMLV2_THREADS=1`) take it. Nothing a caller hands over
//! may depend on which thread runs it or on how the pieces interleave;
//! the callers here decode independent records and make tables that are
//! functions of frozen rows.

/// Stack reserved for a thread that decodes a library's tables or plans
/// on them: the rows nest as the parser bounds them, and planning builds
/// on the rows the way a parse stack does, so a thread given less could
/// run out where the calling thread would not.
#[cfg(not(target_family = "wasm"))]
pub(crate) const STACK_BYTES: usize = sysmlv2_syntax::parser::MAX_NESTING_STACK_BYTES;

/// Whether work may run on more than one thread: never on a machine with
/// one core, and not when the run asked for one thread. A wasm target has
/// no threads and no such question; every path there runs in line.
#[cfg(not(target_family = "wasm"))]
pub(crate) fn enabled() -> bool {
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| {
        let one_thread =
            std::env::var_os("SYSMLV2_THREADS").is_some_and(|v| v == "1" || v == "0" || v == "off");
        !one_thread && std::thread::available_parallelism().is_ok_and(|threads| threads.get() > 1)
    })
}

/// Run `a` and `b` and return both results, in that order: `a` on a thread
/// of its own and `b` here where a thread can be had, else one after the
/// other here. A thread the host refuses is not an error: nothing took
/// `a`, so it runs here after `b`. A panic on either side is the caller's.
pub(crate) fn join<A, B, FA, FB>(a: FA, b: FB) -> (A, B)
where
    FA: FnOnce() -> A + Send,
    FB: FnOnce() -> B + Send,
    A: Send,
    B: Send,
{
    #[cfg(not(target_family = "wasm"))]
    if enabled() {
        // The work is handed to the thread, so it cannot simply be called
        // again where the thread never starts: the thread takes it from
        // here, and it is still here when nothing took it.
        let mut work = Some(a);
        let (spawned, b_value) = std::thread::scope(|scope| {
            let slot = &mut work;
            let spawned = std::thread::Builder::new()
                .name("sysmlv2-load".into())
                .stack_size(STACK_BYTES)
                .spawn_scoped(scope, move || {
                    (slot.take().expect("the work is taken once"))()
                });
            // `b` runs here while the thread runs `a`; the thread is joined
            // only afterwards.
            let b_value = b();
            (spawned.map(std::thread::ScopedJoinHandle::join), b_value)
        });
        match spawned {
            Ok(Ok(a_value)) => return (a_value, b_value),
            Ok(Err(panic)) => std::panic::resume_unwind(panic),
            Err(_refused) => {}
        }
        let a_value = (work.take().expect("no thread took the work"))();
        return (a_value, b_value);
    }
    (a(), b())
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Both results come back in order, whichever thread computed them.
    #[test]
    fn join_returns_both_results_in_order() {
        let (a, b) = join(|| 1 + 1, || "two".len());
        assert_eq!((a, b), (2, 3));
    }

    /// The pieces may borrow the caller's stack: the scope ends before
    /// `join` returns.
    #[test]
    fn join_may_borrow_from_the_caller() {
        let words = ["one", "two", "three"];
        let (letters, count) = join(
            || words.iter().map(|w| w.len()).sum::<usize>(),
            || words.len(),
        );
        assert_eq!((letters, count), (11, 3));
    }

    /// A panic on the spawned side is the caller's panic.
    #[test]
    #[should_panic(expected = "from the spawned side")]
    fn join_resumes_a_panic_from_the_spawned_side() {
        let _ = join(|| panic!("from the spawned side"), || ());
    }

    /// Both sides run at once where threads are had: each hears from the
    /// other while it runs. Run one after the other, the first side would
    /// wait for a message the second has not sent yet and time out.
    #[test]
    fn join_runs_both_sides_at_once() {
        if !enabled() {
            return;
        }
        let (to_b, from_a) = std::sync::mpsc::channel();
        let (to_a, from_b) = std::sync::mpsc::channel();
        let patience = std::time::Duration::from_secs(5);
        let (a_heard_b, b_heard_a) = join(
            move || {
                to_b.send(()).expect("b is listening");
                from_b.recv_timeout(patience).is_ok()
            },
            move || {
                let heard = from_a.recv_timeout(patience).is_ok();
                to_a.send(()).expect("a is listening");
                heard
            },
        );
        assert!(
            a_heard_b && b_heard_a,
            "each side heard the other while both ran"
        );
    }
}

/// How many threads the semantic checks of a model with `user_rows` rows
/// of its own may run on: one where threads are not enabled
/// ([`enabled`]); else what `SYSMLV2_THREADS` names, when it names two or
/// more; else the machine's parallelism, eight at most, and four at most
/// from a hundred thousand rows. Each thread forks the resolved model's
/// memos, which on the largest models weigh as much again as the model:
/// there four threads take most of the gain (the 18.8 MB model 1.17×,
/// eight 1.22×) for half the memory.
#[cfg(not(target_family = "wasm"))]
pub(crate) fn workers(user_rows: usize) -> usize {
    if !enabled() {
        return 1;
    }
    static NAMED: std::sync::OnceLock<Option<usize>> = std::sync::OnceLock::new();
    let named = *NAMED.get_or_init(|| {
        std::env::var("SYSMLV2_THREADS")
            .ok()
            .and_then(|v| v.parse::<usize>().ok())
            .filter(|&n| n >= 2)
    });
    named.unwrap_or_else(|| {
        let most = if user_rows >= 100_000 { 4 } else { 8 };
        std::thread::available_parallelism()
            .map_or(1, std::num::NonZero::get)
            .min(most)
    })
}

#[cfg(test)]
thread_local! {
    /// A test's worker count for the semantic checks, in place of the
    /// policy's and whatever the model's size.
    static TEST_WORKERS: std::cell::Cell<Option<usize>> = const { std::cell::Cell::new(None) };
}
#[cfg(test)]
pub(crate) fn test_workers() -> Option<usize> {
    TEST_WORKERS.with(std::cell::Cell::get)
}
#[cfg(test)]
pub(crate) fn set_test_workers(workers: Option<usize>) {
    TEST_WORKERS.with(|c| c.set(workers));
}
