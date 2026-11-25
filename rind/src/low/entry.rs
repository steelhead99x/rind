// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::{enter_cpu_state, leave_cpu_state};

#[cfg(all(debug_assertions, not(test), rind_std))]
std::thread_local! {
    // This thread's live `Entry`s, for `Entry::assert_held`. Unit tests call
    // internals with no public function above them, so they don't count, and
    // a target without an OS has no threads to count per.
    static HELD: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
}

#[cfg(all(debug_assertions, rind_dit))]
std::thread_local! {
    // This thread's live secret `Entry`s, unit tests included: while one is
    // live, PSTATE.DIT must be set, which `check_dit` asserts. And how many
    // times it has asserted so, for the tests to see the check ran.
    static SECRET: core::cell::Cell<(usize, u64)> = const { core::cell::Cell::new((0, 0)) };
}

/// Panics, in a debug build where rind sets DIT, if a secret `Entry` is live
/// on this thread and PSTATE.DIT is clear on a CPU that has it.
///
/// Called as a secret `Entry` is made and dropped, and by every primitive
/// that calls [`Entry::assert_held`], so a debug run of the tests on an
/// aarch64 core with DIT, or under qemu-aarch64, reads PSTATE.DIT under each
/// kernel any secret call reaches.
#[cfg(all(debug_assertions, rind_dit))]
#[track_caller]
fn check_dit() {
    let (live, checks) = SECRET.get();
    if live == 0 {
        return;
    }
    if let Some(on) = super::dit_on() {
        assert!(on, "secret computation with PSTATE.DIT clear");
        SECRET.set((live, checks + 1));
    }
}

/// One of these should be made at library entry points: every `pub` function.
///
/// Trivial conversions, accessors (ie, functions which do no actual computation)
/// need not.
pub(crate) struct Entry {
    secret: bool,
    cpu_state: u32,
    // Neither `Send` nor `Sync`: DIT and the counts above belong to the
    // thread that made the `Entry`, so it must drop there, as
    // `crate::cpu::Dit` must.
    _thread: core::marker::PhantomData<*const ()>,
    // On x86 the portable backend's arithmetic may compile to any of the
    // multiplies Intel's MXCSR mitigation covers, anywhere, so every call,
    // public or secret, holds it. The x86_64 backend holds it only around
    // the algorithms that run them.
    #[cfg(all(
        rind_backend = "portable",
        any(target_arch = "x86", target_arch = "x86_64")
    ))]
    _mcdt: super::Mcdt,
}

impl Entry {
    /// Must be called at top-level crate entry points for public functions.
    ///
    /// Public functions have no secret data in their arguments or return values.
    #[must_use]
    pub(crate) fn new_public() -> Self {
        #[cfg(all(debug_assertions, not(test), rind_std))]
        HELD.set(HELD.get() + 1);
        #[cfg(all(rind_dit_autohold, rind_dit))]
        autohold::public_call();

        Self {
            secret: false,
            cpu_state: 0,
            _thread: core::marker::PhantomData,
            #[cfg(all(
                rind_backend = "portable",
                any(target_arch = "x86", target_arch = "x86_64")
            ))]
            _mcdt: super::Mcdt::enter(),
        }
    }

    /// Must be called at top-level crate entry points for secret functions.
    ///
    /// Secret functions have secret data in their arguments or return values
    /// (directly, or transitively).
    #[must_use]
    pub(crate) fn new_secret() -> Self {
        #[cfg(all(rind_dit_autohold, rind_dit))]
        autohold::enter();
        let cpu_state = enter_cpu_state();
        #[cfg(all(debug_assertions, not(test), rind_std))]
        HELD.set(HELD.get() + 1);
        #[cfg(all(debug_assertions, rind_dit))]
        {
            let (live, checks) = SECRET.get();
            SECRET.set((live + 1, checks));
            check_dit();
        }
        #[cfg(test)]
        model::enter();

        Self {
            secret: true,
            cpu_state,
            _thread: core::marker::PhantomData,
            #[cfg(all(
                rind_backend = "portable",
                any(target_arch = "x86", target_arch = "x86_64")
            ))]
            _mcdt: super::Mcdt::enter(),
        }
    }

    /// Panics in a debug build with an OS unless this thread holds an `Entry`.
    ///
    /// Primitives that make no `Entry` of their own call this, so a test
    /// reaching one through a public function that skipped its `Entry` fails.
    ///
    /// Where rind sets DIT, a debug build also panics if a secret `Entry` is
    /// live and PSTATE.DIT is clear.
    #[track_caller]
    pub(crate) fn assert_held() {
        #[cfg(all(debug_assertions, not(test), rind_std))]
        assert!(HELD.get() > 0, "computing outside an `Entry`");
        #[cfg(all(debug_assertions, rind_dit))]
        check_dit();
    }
}

impl Drop for Entry {
    fn drop(&mut self) {
        #[cfg(all(debug_assertions, not(test), rind_std))]
        HELD.set(HELD.get() - 1);
        if self.secret {
            #[cfg(all(debug_assertions, rind_dit))]
            {
                check_dit();
                let (live, checks) = SECRET.get();
                SECRET.set((live - 1, checks));
            }
            #[cfg(test)]
            model::leave();
            #[cfg(all(rind_dit_autohold, rind_dit))]
            autohold::leave(self.cpu_state);
            #[cfg(not(all(rind_dit_autohold, rind_dit)))]
            leave_secret(self.cpu_state);
        }
    }
}

/// Restores what `enter_cpu_state` changed, as the last secret `Entry` or
/// [`crate::cpu::Dit`] guard drops.
///
/// `--cfg rind_dit_sticky` instead leaves DIT on for the rest of the
/// thread's life once rind has set it, so a thread that makes many small
/// calls pays one toggle in all, as a guard held for its life would. It
/// only ever adds DIT, so every secret computation still runs under it,
/// but everything else the thread runs does too. It is a measuring
/// prototype for the toggle cost on Apple silicon, not a supported
/// configuration, and the FIPS module refuses it.
pub(super) fn leave_secret(cpu_state: u32) {
    if cfg!(rind_dit_sticky) {
        let _ = cpu_state;
    } else {
        leave_cpu_state(cpu_state);
    }
}

// The FIPS module restores DIT as each guard drops; a cfg that leaves it
// set for the rest of the thread changes that, so it is refused there.
#[cfg(all(rind_fips, rind_dit_sticky))]
compile_error!("rind_dit_sticky is a measuring prototype, not a FIPS configuration");

/// `--cfg rind_dit_autohold`: a prototype of coalescing DIT toggles across
/// calls without a guard, for measuring only (see
/// `benchmarks/apple-dit-coalescing.md`). When the last secret `Entry` on a
/// thread drops, DIT stays on if rind set it, and the thread is in a batch.
/// The batch ends, and DIT is cleared, at the next public call into rind
/// (verifying, parsing a public key), or after [`autohold::BATCH`] secret
/// calls in a row, whichever comes first. A guard taken outside a batch
/// still clears DIT as it drops, as its docs promise; one taken inside a
/// batch finds DIT on, so its drop leaves DIT to the batch, which ends as
/// above. It only ever delays clearing DIT, so every secret computation
/// still runs under it; the cost is that the caller's own code between
/// calls in a batch runs with DIT too. It never clears DIT that was on
/// before rind set it, but a caller that sets DIT itself during a batch
/// (which changes nothing, DIT being on) loses it when the batch ends.
///
/// The bound is in calls into rind, not in time: nothing clears DIT while
/// the thread makes no call. A thread whose last call into rind is a secret
/// one keeps DIT on, for all its own code, until it calls rind again or
/// exits, however long that is.
#[cfg(all(rind_dit_autohold, rind_dit))]
pub(super) mod autohold {
    use core::cell::Cell;

    /// Secret calls a batch may span before rind clears DIT anyway, so a
    /// thread that keeps calling rind, but never with a public call, still
    /// has DIT cleared every `BATCH + 1` secret calls. It bounds calls, not
    /// time: after a thread's last call, DIT stays on until it calls again.
    pub(crate) const BATCH: u32 = 64;

    std::thread_local! {
        // Live secret entries on this thread, and secret calls since rind
        // left DIT on (0: not in a batch).
        static STATE: Cell<(u32, u32)> = const { Cell::new((0, 0)) };
    }

    pub(super) fn enter() {
        let (live, batch) = STATE.get();
        STATE.set((live + 1, batch));
    }

    pub(super) fn leave(cpu_state: u32) {
        let (live, batch) = STATE.get();
        let live = live - 1;
        let batch = match (live, cpu_state, batch) {
            // Inside another secret entry: nothing to decide.
            (1.., _, _) => batch,
            // rind set DIT for this call: keep it, and start a batch.
            (0, 1, _) => 1,
            // DIT was on before this call, and rind left it on: count.
            // Saturating: under a held guard the count is not bounded, and a
            // wrap to 0 would read as DIT the caller set, never cleared.
            (0, _, 1..) if batch < BATCH || crate::cpu::Dit::is_held() => batch.saturating_add(1),
            (0, _, 1..) => {
                super::leave_cpu_state(1);
                0
            }
            // DIT was on before this call, set by the caller: theirs.
            (0, _, 0) => 0,
        };
        STATE.set((live, batch));
    }

    /// A public call outside any secret entry or guard ends the batch.
    pub(super) fn public_call() {
        if matches!(STATE.get(), (0, 1..)) && !crate::cpu::Dit::is_held() {
            super::leave_cpu_state(1);
            STATE.set((0, 0));
        }
    }

    /// Whether this thread is in a batch, DIT left on by rind.
    #[cfg(test)]
    pub(crate) fn in_batch() -> bool {
        STATE.get().1 > 0
    }
}

// A measuring prototype, which the FIPS module, which ships, refuses.
#[cfg(all(rind_fips, rind_dit_autohold))]
compile_error!("rind_dit_autohold is a measuring prototype, not a FIPS configuration");

// Autohold clears DIT itself, around `leave_secret`, so sticky would hold for
// guards but not for entries: the pair measures neither.
#[cfg(all(rind_dit_sticky, rind_dit_autohold))]
compile_error!("rind_dit_autohold and rind_dit_sticky are two measuring prototypes; pick one");

/// How many PSTATE.DIT checks this thread has passed.
#[cfg(all(test, debug_assertions, rind_dit))]
pub(crate) fn dit_checks() -> u64 {
    SECRET.get().1
}

/// A model of when rind toggles DIT, for tests on any target: a toggle is a
/// secret `Entry`, or a [`crate::cpu::Dit`] guard, made while none of either
/// is live on this thread, which is when Apple's targets turn DIT on (and
/// off again when the last drops). The count is the same on every backend,
/// so x86_64 CI checks how many toggles each operation costs on Apple's.
#[cfg(test)]
pub(crate) mod model {
    std::thread_local! {
        // Live secret entries and guards, and toggles so far.
        static STATE: core::cell::Cell<(usize, u64)> = const { core::cell::Cell::new((0, 0)) };
    }

    pub(crate) fn enter() {
        let (live, toggles) = STATE.get();
        STATE.set((live + 1, toggles + u64::from(live == 0)));
    }

    pub(crate) fn leave() {
        let (live, toggles) = STATE.get();
        STATE.set((live - 1, toggles));
    }

    /// Toggles this thread has made so far.
    pub(crate) fn toggles() -> u64 {
        STATE.get().1
    }

    /// Whether a secret `Entry` or guard is live on this thread.
    pub(crate) fn live() -> bool {
        STATE.get().0 > 0
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests;
