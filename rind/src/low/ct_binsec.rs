// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The symbolic constant-time check: `admin/ct-binsec` stops each test named
//! `ct_binsec` as it enters a [`checked`] region, dumps the process, and has
//! BINSEC explore the region from there. Inside it, what `ct::secret_slice`
//! and `ct::into_secret` mark takes every value at once, and BINSEC fails on
//! a branch or memory address that depends on it; what `ct::public_slice`
//! and `ct::into_public` mark becomes public again, as under valgrind.

/// Runs `f` as the region BINSEC checks, after a first run that fixes what
/// rind sets up lazily, such as the CPU features it detects.
pub(crate) fn checked<T>(f: impl Fn() -> T) -> T {
    core::hint::black_box(f());
    rind_ct_binsec_start();
    let r = core::hint::black_box(f());
    rind_ct_binsec_stop();
    r
}

/// Marks the `len` bytes at `value` secret: BINSEC replaces the call with a
/// write of fresh secret bytes, which the caller rereads, since it passed
/// them mutably.
#[inline]
pub(crate) fn classify(value: *mut u8, len: usize) {
    rind_ct_binsec_secret(value, len);
}

/// Marks the `len` bytes at `value` public, by a write of fresh public bytes.
#[inline]
pub(crate) fn declassify(value: *mut u8, len: usize) {
    rind_ct_binsec_public(value, len);
}

/// A public length: `max` when run, and every length up to `max` at once
/// under BINSEC, which then explores the path each takes.
#[inline]
pub(crate) fn length(max: usize) -> usize {
    rind_ct_binsec_length(max)
}

// The symbols `admin/ct-binsec` finds. Each does nothing when run, but
// differently, so that no two are folded into one.

#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn rind_ct_binsec_start() {
    core::hint::black_box(1u8);
}

#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn rind_ct_binsec_stop() {
    core::hint::black_box(2u8);
}

#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn rind_ct_binsec_secret(value: *mut u8, len: usize) {
    core::hint::black_box((value, len, 3u8));
}

#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn rind_ct_binsec_public(value: *mut u8, len: usize) {
    core::hint::black_box((value, len, 4u8));
}

#[unsafe(no_mangle)]
#[inline(never)]
extern "C" fn rind_ct_binsec_length(max: usize) -> usize {
    core::hint::black_box(max)
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;

    // `admin/ct-binsec` requires BINSEC to find these leaks, so that a
    // harness that checks nothing, or a marker it fails to replace, fails.

    #[test]
    #[ignore = "admin/ct-binsec runs it under BINSEC"]
    fn ct_binsec_planted_branch() {
        checked(|| {
            let secret = ct::into_secret(core::hint::black_box(0u8));
            if secret & 1 == 1 {
                core::hint::black_box(0);
            }
        });
    }

    #[test]
    #[ignore = "admin/ct-binsec runs it under BINSEC"]
    fn ct_binsec_planted_index() {
        let table = core::hint::black_box([0u8; 64]);
        checked(|| {
            let secret = [0u8; 8];
            ct::secret_slice(&secret);
            core::hint::black_box(&table)[core::hint::black_box(&secret)[5] as usize % 64]
        });
    }
}
