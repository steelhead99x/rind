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
    ready: AtomicBool,
    coordinates: [[[AtomicU32; 2]; N]; 8],
}

impl<const N: usize> VerificationTable<N> {
    pub(crate) fn new() -> Self {
        Self {
            ready: AtomicBool::new(false),
            coordinates: [const { [const { [const { AtomicU32::new(0) }; 2] }; N] }; 8],
        }
    }

    /// Copies into the caller's table, computing it if needed.
    pub(crate) fn fill<T>(
        &self,
        out: &mut [T; 8],
        limbs: impl Fn(&mut T) -> &mut [u64; N],
        build: impl FnOnce() -> [T; 8],
    ) {
        if self.ready.load(Ordering::Acquire) {
            for (point, slots) in out.iter_mut().zip(&self.coordinates) {
                for (word, [lo, hi]) in limbs(point).iter_mut().zip(slots) {
                    *word = u64::from(lo.load(Ordering::Relaxed))
                        | (u64::from(hi.load(Ordering::Relaxed)) << 32);
                }
            }
            return;
        }

        *out = build();
        for (slots, point) in self.coordinates.iter().zip(out) {
            for ([lo, hi], word) in slots.iter().zip(limbs(point)) {
                lo.store(*word as u32, Ordering::Relaxed);
                hi.store((*word >> 32) as u32, Ordering::Relaxed);
            }
        }
        self.ready.store(true, Ordering::Release);
    }
}

impl<const N: usize> Clone for VerificationTable<N> {
    fn clone(&self) -> Self {
        let clone = Self::new();
        if self.ready.load(Ordering::Acquire) {
            for (dst, src) in clone
                .coordinates
                .iter()
                .flatten()
                .flatten()
                .zip(self.coordinates.iter().flatten().flatten())
            {
                dst.store(src.load(Ordering::Relaxed), Ordering::Relaxed);
            }
            clone.ready.store(true, Ordering::Release);
        }
        clone
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const VALUE: [[u64; 2]; 8] = [[0x1234_5678_9abc_def0, u64::MAX]; 8];

    #[test]
    fn fills_on_first_use_and_copies_on_clone() {
        let cache = VerificationTable::new();
        let mut out = [[0; 2]; 8];
        cache.fill(&mut out, |p| p, || VALUE);
        assert_eq!(out, VALUE);

        let clone = cache.clone();
        let mut copied = [[0; 2]; 8];
        clone.fill(&mut copied, |p| p, || unreachable!());
        assert_eq!(copied, VALUE);
    }

    #[test]
    #[cfg(not(target_family = "wasm"))]
    fn concurrent_builders_publish_the_same_table() {
        let cache = VerificationTable::new();
        let both_building = std::sync::Barrier::new(2);
        std::thread::scope(|scope| {
            for _ in 0..2 {
                scope.spawn(|| {
                    let mut out = [[0; 2]; 8];
                    cache.fill(
                        &mut out,
                        |p| p,
                        || {
                            both_building.wait();
                            VALUE
                        },
                    );
                    assert_eq!(out, VALUE);
                    out.fill([0; 2]);
                    cache.fill(&mut out, |p| p, || unreachable!());
                    assert_eq!(out, VALUE);
                });
            }
        });
    }
}
