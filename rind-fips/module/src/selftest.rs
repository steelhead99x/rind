// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The self-tests: each algorithm's CAST runs once, before its first use,
//! as IG 10.3.A allows, so a process pays only for what it uses. A failure
//! enters the error state, aborting, so no output follows a failed test.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Mutex, MutexGuard, PoisonError};

use rind::Error;
pub(crate) use rind::fips::SelfTest;
use rind::fips::{broken, fail};

static PASSED: [AtomicBool; SelfTest::ALL.len()] =
    [const { AtomicBool::new(false) }; SelfTest::ALL.len()];

/// Held while any self-test runs, and across `fork`, so a child never
/// inherits one half run by a thread it lacks, which would block it forever.
static RUNNING: Mutex<()> = Mutex::new(());

/// The self-tests held still, as [`hold`] returns them.
pub(crate) type Hold = MutexGuard<'static, ()>;

/// Waits for any self-test running, then keeps others from starting until
/// the hold drops.
pub(crate) fn hold() -> Hold {
    RUNNING.lock().unwrap_or_else(PoisonError::into_inner)
}

/// Runs each of `tests` that has not yet passed in this process, blocking
/// any other thread that needs one until it has.
pub(crate) fn ensure(tests: &[SelfTest]) {
    for &test in tests {
        let passed = &PASSED[index(test)];
        if !passed.load(Ordering::Acquire) {
            let _running = hold();
            if !passed.load(Ordering::Acquire) {
                run(test);
                passed.store(true, Ordering::Release);
            }
        }
    }
}

/// Runs every self-test now, passed before or not: the on-demand service.
pub(crate) fn run_all() {
    let _running = hold();
    for test in SelfTest::ALL {
        run(test);
        PASSED[index(test)].store(true, Ordering::Release);
    }
}

fn run(test: SelfTest) {
    if let Err(name) = test.run() {
        fail(name);
    }
}

fn index(test: SelfTest) -> usize {
    SelfTest::ALL.iter().position(|&t| t == test).unwrap()
}

/// A pairwise consistency test's outcome: aborts naming `name` unless
/// `passed`, which the break build forces false when `RIND_FIPS_BREAK`
/// names it.
pub(crate) fn pct(name: &str, passed: impl FnOnce() -> bool) {
    if broken(name) || !passed() {
        fail(name);
    }
}

/// A pairwise consistency test that first draws from the DRBG, as signing or
/// encapsulating does: `draw`'s [`Error::RngFailed`] is returned, as any
/// service returns it, rather than taken for an inconsistent key. Anything
/// else `draw` or `check` finds fails as [`pct`] does.
pub(crate) fn pct_drawing<T>(
    name: &str,
    draw: impl FnOnce() -> Result<T, Error>,
    check: impl FnOnce(T) -> bool,
) -> Result<(), Error> {
    let drawn = draw();
    if let Err(Error::RngFailed) = drawn {
        return Err(Error::RngFailed);
    }
    pct(name, || drawn.is_ok_and(check));
    Ok(())
}
