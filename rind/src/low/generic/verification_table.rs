// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::sync::atomic::{AtomicBool, AtomicU32, Ordering};

/// A table of eight public ECDSA points, filled without compare-and-swap.
///
/// Every build for a given cache must return the same coordinate words. A
/// second builder may publish while a reader is copying the table, so all
/// accesses to the stored words are atomic. Acquiring readiness guarantees
/// at least one complete build, and concurrent stores write identical words.
#[derive(Debug)]
pub(crate) struct VerificationTable<const N: usize> {
    used: AtomicBool,
    ready: AtomicBool,
    coordinates: [[[AtomicU32; 2]; N]; 8],
}

impl<const N: usize> VerificationTable<N> {
    pub(crate) fn new() -> Self {
        Self {
            used: AtomicBool::new(false),
            ready: AtomicBool::new(false),
            coordinates: [const { [const { [const { AtomicU32::new(0) }; 2] }; N] }; 8],
        }
    }

    /// Uses the shorter table on the first call that observes an unused cache.
    pub(crate) fn get_or_build(
        &self,
        build: impl FnOnce() -> [[u64; N]; 8],
    ) -> Option<[[u64; N]; 8]> {
        if !self.used.load(Ordering::Relaxed) {
            self.used.store(true, Ordering::Relaxed);
            return None;
        }
        Some(self.get_or_build_now(build))
    }

    /// Returns the cached coordinates, computing them if needed.
    pub(crate) fn get_or_build_now(&self, build: impl FnOnce() -> [[u64; N]; 8]) -> [[u64; N]; 8] {
        if let Some(value) = self.get() {
            return value;
        }
        let value = build();
        self.publish(&value);
        value
    }

    fn get(&self) -> Option<[[u64; N]; 8]> {
        self.ready.load(Ordering::Acquire).then(|| {
            self.coordinates.each_ref().map(|point| {
                point.each_ref().map(|[lo, hi]| {
                    u64::from(lo.load(Ordering::Relaxed))
                        | (u64::from(hi.load(Ordering::Relaxed)) << 32)
                })
            })
        })
    }

    fn publish(&self, value: &[[u64; N]; 8]) {
        for (point, words) in self.coordinates.iter().zip(value) {
            for ([lo, hi], word) in point.iter().zip(words) {
                lo.store(*word as u32, Ordering::Relaxed);
                hi.store((*word >> 32) as u32, Ordering::Relaxed);
            }
        }
        self.used.store(true, Ordering::Relaxed);
        self.ready.store(true, Ordering::Release);
    }
}

impl<const N: usize> Clone for VerificationTable<N> {
    fn clone(&self) -> Self {
        let clone = Self::new();
        if let Some(value) = self.get() {
            clone.publish(&value);
        }
        clone
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const VALUE: [[u64; 2]; 8] = [[0x1234_5678_9abc_def0, u64::MAX]; 8];

    #[test]
    fn builds_now_or_on_second_use() {
        let cache = VerificationTable::new();
        assert_eq!(cache.get_or_build(|| unreachable!()), None);
        assert_eq!(cache.get_or_build(|| VALUE), Some(VALUE));
        assert_eq!(cache.get_or_build_now(|| unreachable!()), VALUE);
        assert_eq!(cache.clone().get_or_build(|| unreachable!()), Some(VALUE));

        let cache = VerificationTable::new();
        assert_eq!(cache.get_or_build_now(|| VALUE), VALUE);
        assert_eq!(cache.get_or_build(|| unreachable!()), Some(VALUE));
    }

    #[test]
    #[cfg(not(target_family = "wasm"))]
    fn concurrent_builders_publish_the_same_table() {
        let cache = VerificationTable::new();
        let both_building = std::sync::Barrier::new(2);
        std::thread::scope(|scope| {
            for _ in 0..2 {
                scope.spawn(|| {
                    assert_eq!(
                        cache.get_or_build_now(|| {
                            both_building.wait();
                            VALUE
                        }),
                        VALUE
                    );
                    assert_eq!(cache.get_or_build_now(|| unreachable!()), VALUE);
                });
            }
        });
    }
}
