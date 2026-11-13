// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The reuse cache on targets without compare-and-swap, such as ARMv6-M's
//! `thumbv6m-none-eabi` (the RP2040) and `riscv32imc-unknown-none-elf`: it
//! keeps nothing.
//!
//! `reuse_cache.rs` lets exactly one use write the value by winning a
//! compare-and-swap. Without one, two uses, on two cores or in a core and an
//! interrupt handler, could both write it, or one read it half-written, which
//! is undefined behavior. A lock would need a critical-section implementation
//! from every program, so instead nothing is kept: each use builds the value,
//! as a key used once does. That costs speed, never correctness, and leaves
//! nothing `unsafe` here; the type is `Sync` only because its contents are.

use core::fmt;
use core::marker::PhantomData;

/// `reuse_cache.rs`'s `ReuseCache`, keeping nothing.
pub(crate) struct ReuseCache<T>(PhantomData<T>);

impl<T: Copy + Default> ReuseCache<T> {
    pub(crate) fn new() -> Self {
        Self(PhantomData)
    }

    /// Always `None`, as on a first use: the caller does without the value.
    pub(crate) fn get_or_build(&self, _build: impl FnOnce() -> T) -> Option<&T> {
        None
    }

    /// The value, built with `build` on every call.
    pub(crate) fn get_or_build_now(&self, build: impl FnOnce() -> T) -> T {
        build()
    }
}

impl<T> Clone for ReuseCache<T> {
    fn clone(&self) -> Self {
        Self(PhantomData)
    }
}

impl<T> fmt::Debug for ReuseCache<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("ReuseCache(None)")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn keeps_nothing() {
        let cache = ReuseCache::<u64>::new();
        for _ in 0..3 {
            assert_eq!(cache.get_or_build(|| unreachable!()), None);
        }
        let mut builds = 0;
        for _ in 0..3 {
            let value = cache.get_or_build_now(|| {
                builds += 1;
                7
            });
            assert_eq!(value, 7);
        }
        assert_eq!(builds, 3);
        assert_eq!(cache.clone().get_or_build(|| unreachable!()), None);
        assert_eq!(format!("{cache:?}"), "ReuseCache(None)");
    }

    /// Shared between threads with no `unsafe`: `Sync` comes from its
    /// contents, not from a promise about how it is used.
    #[test]
    // wasm32-wasip2 cannot spawn threads.
    #[cfg(not(target_family = "wasm"))]
    fn shared_across_threads() {
        let cache = ReuseCache::<[u64; 4]>::new();
        std::thread::scope(|s| {
            for _ in 0..4 {
                s.spawn(|| {
                    assert_eq!(cache.get_or_build(|| [7; 4]), None);
                    assert_eq!(cache.get_or_build_now(|| [7; 4]), [7; 4]);
                });
            }
        });
    }
}
