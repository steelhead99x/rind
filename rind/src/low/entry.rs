// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use super::cpu::verify_cpu_features;
use super::{enter_cpu_state, leave_cpu_state};

// A bare-metal build (`target_os = "none"`) has no thread-local storage,
// and a shared count would race between cores and interrupt handlers, so it
// leaves the check out; the hosted test suites run it.
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
}

impl Entry {
    /// Must be called at top-level crate entry points for public functions.
    ///
    /// Public functions have no secret data in their arguments or return values.
    #[must_use]
    pub(crate) fn new_public() -> Self {
        verify_cpu_features();
        #[cfg(all(debug_assertions, not(test), not(target_os = "none")))]
        HELD.set(HELD.get() + 1);

        Self {
            secret: false,
            cpu_state: 0,
        }
    }

    /// Must be called at top-level crate entry points for secret functions.
    ///
    /// Secret functions have secret data in their arguments or return values
    /// (directly, or transitively).
    #[must_use]
    pub(crate) fn new_secret() -> Self {
        verify_cpu_features();
        let cpu_state = enter_cpu_state();
        #[cfg(all(debug_assertions, not(test), not(target_os = "none")))]
        HELD.set(HELD.get() + 1);

        Self {
            secret: true,
            cpu_state,
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
