// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::cell::UnsafeCell;
use core::fmt;
use core::panic::{RefUnwindSafe, UnwindSafe};
#[cfg(target_has_atomic = "8")]
use core::sync::atomic::AtomicU8;
use core::sync::atomic::Ordering;

// ARMv6-M, the RP2040's core, has atomic loads and stores but no
// compare-and-swap, which `fetch_max` and `compare_exchange` need, so there
// `portable-atomic` runs them inside the binary's `critical-section`.
#[cfg(not(target_has_atomic = "8"))]
use portable_atomic::AtomicU8;

// Each use only raises the state. Zero is a fresh cache, so a wiped one is too.
const UNUSED: u8 = 0;
const USED_ONCE: u8 = 1;
const BUILDING: u8 = 2;
const READY: u8 = 3;

/// A public value its owner builds once and keeps: on the first use that
/// needs it, or on the second use, so an owner used once never pays for it.
///
/// No use waits: one built on another thread is not there yet.
pub(crate) struct ReuseCache<T> {
    state: AtomicU8,
    value: UnsafeCell<T>,
}

// SAFETY: `value` is written once, by the one thread that moves `state` up
// to `BUILDING`, and read only once `state` is `READY`, which that thread
// stores with release ordering after writing it.
unsafe impl<T: Send + Sync> Sync for ReuseCache<T> {}

// A panicking `build` leaves `state` at `BUILDING`, so `value` is never read.
impl<T: RefUnwindSafe + UnwindSafe> RefUnwindSafe for ReuseCache<T> {}

impl<T: Copy + Default> ReuseCache<T> {
    pub(crate) fn new() -> Self {
        Self {
            state: AtomicU8::new(UNUSED),
            value: UnsafeCell::new(T::default()),
        }
    }

    /// The value, building it with `build` on the second call; `None` on the
    /// first, and while another thread builds it.
    pub(crate) fn get_or_build(&self, build: impl FnOnce() -> T) -> Option<&T> {
        match self.state.load(Ordering::Acquire) {
            UNUSED => {
                self.state.fetch_max(USED_ONCE, Ordering::Relaxed);
                None
            }
            USED_ONCE => {
                self.state
                    .compare_exchange(USED_ONCE, BUILDING, Ordering::Relaxed, Ordering::Relaxed)
                    .ok()?;
                let value = build();
                // SAFETY: winning the exchange makes this the only writer,
                // and no reader reads before `READY`.
                unsafe { *self.value.get() = value };
                self.state.store(READY, Ordering::Release);
                self.get()
            }
            _ => self.get(),
        }
    }

    /// The value, built with `build` if no use has kept it yet; one racing
    /// another thread's build builds its own copy.
    pub(crate) fn get_or_build_now(&self, build: impl FnOnce() -> T) -> T {
        if let Some(value) = self.get() {
            return *value;
        }
        let value = build();
        let state = self.state.load(Ordering::Relaxed);
        if state < BUILDING
            && self
                .state
                .compare_exchange(state, BUILDING, Ordering::Relaxed, Ordering::Relaxed)
                .is_ok()
        {
            // SAFETY: winning the exchange makes this the only writer, and no
            // reader reads before `READY`.
            unsafe { *self.value.get() = value };
            self.state.store(READY, Ordering::Release);
        }
        value
    }

    fn get(&self) -> Option<&T> {
        match self.state.load(Ordering::Acquire) {
            // SAFETY: nothing writes `value` once `state` is `READY`.
            READY => Some(unsafe { &*self.value.get() }),
            _ => None,
        }
    }
}

impl<T: Copy + Default> Clone for ReuseCache<T> {
    fn clone(&self) -> Self {
        match self.get() {
            Some(value) => Self {
                state: AtomicU8::new(READY),
                value: UnsafeCell::new(*value),
            },
            None => Self::new(),
        }
    }
}

impl<T: Copy + Default + fmt::Debug> fmt::Debug for ReuseCache<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("ReuseCache").field(&self.get()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builds_on_second_use() {
        let cache = ReuseCache::<u64>::new();
        assert_eq!(cache.get_or_build(|| unreachable!()), None);
        assert_eq!(cache.clone().get_or_build(|| unreachable!()), None);
        assert_eq!(cache.get_or_build(|| 7), Some(&7));
        assert_eq!(cache.get_or_build(|| unreachable!()), Some(&7));
        assert_eq!(cache.clone().get_or_build(|| unreachable!()), Some(&7));
    }

    #[test]
    fn builds_now_on_first_use() {
        let cache = ReuseCache::<u64>::new();
        assert_eq!(cache.get_or_build_now(|| 7), 7);
        assert_eq!(cache.get_or_build_now(|| unreachable!()), 7);
        assert_eq!(cache.get_or_build(|| unreachable!()), Some(&7));

        let cache = ReuseCache::<u64>::new();
        assert_eq!(cache.get_or_build(|| unreachable!()), None);
        assert_eq!(cache.get_or_build_now(|| 7), 7);
        assert_eq!(cache.clone().get_or_build_now(|| unreachable!()), 7);
        assert_eq!(format!("{cache:?}"), "ReuseCache(Some(7))");
    }

    /// A build that panicked holds `BUILDING`, as one on another thread
    /// would: the value is built and returned, but no use keeps it.
    #[test]
    // Catches the panic, which a `panic = "abort"` target such as wasm cannot.
    #[cfg(panic = "unwind")]
    fn never_keeps_beside_a_build() {
        let cache = ReuseCache::<u64>::new();
        assert_eq!(cache.get_or_build(|| unreachable!()), None);
        let build = core::panic::AssertUnwindSafe(|| cache.get_or_build(|| panic!("build")));
        assert!(std::panic::catch_unwind(build).is_err());
        assert_eq!(cache.get_or_build_now(|| 7), 7);
        assert_eq!(cache.get_or_build(|| unreachable!()), None);
        assert_eq!(format!("{cache:?}"), "ReuseCache(None)");
    }

    /// Threads racing to build and read one cache each see the whole value,
    /// and Miri finds no data race between the build and a read.
    #[test]
    // wasm32-wasip2 cannot spawn threads.
    #[cfg(not(target_family = "wasm"))]
    fn shared_across_threads() {
        let cache = ReuseCache::<[u64; 4]>::new();
        std::thread::scope(|s| {
            for _ in 0..4 {
                s.spawn(|| {
                    for _ in 0..3 {
                        if let Some(value) = cache.get_or_build(|| [7; 4]) {
                            assert_eq!(*value, [7; 4]);
                        }
                        assert_eq!(cache.get_or_build_now(|| [7; 4]), [7; 4]);
                    }
                });
            }
        });
        assert_eq!(cache.get_or_build(|| unreachable!()), Some(&[7; 4]));
    }
}
