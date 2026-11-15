// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::{enter_cpu_state, leave_cpu_state};

// A bare-metal build (`target_os = "none"`) has no thread-local storage.
// One count shared by every core and interrupt handler would race, and a
// debug build would then panic while another core still held an `Entry`.
// The check stays in every hosted debug build of this library except its
// unit tests (`cfg(test)` is set only for that harness): a debug binary and
// the integration tests under `rind/tests` compile it. It counts entries,
// it does not branch on a secret, and `enter_cpu_state` still runs.
#[cfg(all(debug_assertions, not(test), not(target_os = "none")))]
std::thread_local! {
    // This thread's live `Entry`s, for `Entry::assert_held`. Unit tests call
    // internals with no public function above them, so they don't count.
    static HELD: core::cell::Cell<usize> = const { core::cell::Cell::new(0) };
}

/// One of these should be made at library entry points: every `pub` function.
///
/// Trivial conversions, accessors (ie, functions which do no actual computation)
/// need not.
pub(crate) struct Entry {
    secret: bool,
    cpu_state: u32,
    // On x86 the portable backend's arithmetic may compile to any of the
    // multiplies Intel's MXCSR mitigation covers, anywhere, so every call,
    // public or secret, holds it. The x86_64 backend holds it only around
    // the algorithms that run them.
    #[cfg(all(
        rind_backend = "portable",
        any(
            target_arch = "x86",
            all(target_arch = "x86_64", target_feature = "sse2")
        )
    ))]
    _mcdt: super::Mcdt,
}

impl Entry {
    /// Must be called at top-level crate entry points for public functions.
    ///
    /// Public functions have no secret data in their arguments or return values.
    #[must_use]
    pub(crate) fn new_public() -> Self {
        #[cfg(all(debug_assertions, not(test), not(target_os = "none")))]
        HELD.set(HELD.get() + 1);

        Self {
            secret: false,
            cpu_state: 0,
            #[cfg(all(
                rind_backend = "portable",
                any(
                    target_arch = "x86",
                    all(target_arch = "x86_64", target_feature = "sse2")
                )
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
        let cpu_state = enter_cpu_state();
        #[cfg(all(debug_assertions, not(test), not(target_os = "none")))]
        HELD.set(HELD.get() + 1);

        Self {
            secret: true,
            cpu_state,
            #[cfg(all(
                rind_backend = "portable",
                any(
                    target_arch = "x86",
                    all(target_arch = "x86_64", target_feature = "sse2")
                )
            ))]
            _mcdt: super::Mcdt::enter(),
        }
    }

    /// Panics in a debug build unless this thread holds an `Entry`.
    ///
    /// Primitives that make no `Entry` of their own call this, so a test
    /// reaching one through a public function that skipped its `Entry` fails.
    pub(crate) fn assert_held() {
        #[cfg(all(debug_assertions, not(test), not(target_os = "none")))]
        assert!(HELD.get() > 0, "computing outside an `Entry`");
    }
}

impl Drop for Entry {
    fn drop(&mut self) {
        #[cfg(all(debug_assertions, not(test), not(target_os = "none")))]
        HELD.set(HELD.get() - 1);
        if self.secret {
            leave_cpu_state(self.cpu_state);
        }
    }
}
