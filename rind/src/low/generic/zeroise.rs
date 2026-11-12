// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::mem::{size_of, size_of_val};

use crate::low::zero_bytes;

// Without the `wipe` feature these do nothing, so the `Drop` impls that call
// them compile away; `cfg!` rather than `#[cfg]` keeps `zero_bytes` compiled,
// and its test running, in every build.

/// Writes zeroes over the whole of the `v` slice, under the `wipe` feature.
pub(crate) fn zeroise<T: Zeroable>(v: &mut [T]) {
    if cfg!(feature = "wipe") {
        // SAFETY: `v` is `size_of_val(v)` writable bytes, and `T: Zeroable`
        // makes all-zero bytes a valid `T`.
        unsafe { zero_bytes(v.as_mut_ptr().cast(), size_of_val(v)) };
    }
}

/// Writes zeroes over the whole of the `v` value, under the `wipe` feature.
pub(crate) fn zeroise_value<T: Zeroable>(v: &mut T) {
    if cfg!(feature = "wipe") {
        // SAFETY: as above, for the `size_of::<T>()` bytes of `v`.
        unsafe { zero_bytes((v as *mut T).cast(), size_of::<T>()) };
    }
}

/// Marker trait for types who have valid all-bits-zero values.
pub(crate) trait Zeroable {}

/// A `&'static T` that a wiped value may hold: all-bits-zero is `None`.
///
/// It is `Some` from construction until the drop that wipes it.
pub(crate) struct ZeroableRef<T: 'static>(Option<&'static T>);

impl<T> ZeroableRef<T> {
    pub(crate) const fn new(value: &'static T) -> Self {
        Self(Some(value))
    }

    pub(crate) fn get(&self) -> &'static T {
        self.0.expect("wiped only on drop")
    }
}

impl<T> Clone for ZeroableRef<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for ZeroableRef<T> {}

impl<T> Zeroable for ZeroableRef<T> {}

impl Zeroable for u8 {}
impl Zeroable for i16 {}
impl Zeroable for u32 {}
impl Zeroable for u64 {}
impl Zeroable for u128 {}
impl Zeroable for usize {}

#[cfg(rind_backend = "x86_64")]
impl Zeroable for core::arch::x86_64::__m128i {}
#[cfg(rind_backend = "x86_64")]
impl Zeroable for core::arch::x86_64::__m256i {}
#[cfg(rind_backend = "x86_64")]
impl Zeroable for core::arch::x86_64::__m512i {}

#[cfg(rind_backend = "aarch64")]
impl Zeroable for core::arch::aarch64::uint8x16_t {}
#[cfg(rind_backend = "aarch64")]
impl Zeroable for core::arch::aarch64::uint64x2_t {}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn zero_bytes_clears_only_its_range() {
        for n in 0..1024 {
            for offset in 0..4 {
                zero_bytes_equiv(offset, n);
            }
        }
    }

    // Zeroes `len` bytes from `offset` in, so the wide stores start unaligned
    // too, and checks the bytes either side are untouched.
    fn zero_bytes_equiv(offset: usize, len: usize) {
        let mut expect = vec![0xffu8; offset + len + 1];
        expect[offset..offset + len].fill(0);
        let mut bytes = vec![0xffu8; offset + len + 1];
        // SAFETY: `bytes` holds `len` writable bytes from `offset`.
        unsafe { zero_bytes(bytes[offset..].as_mut_ptr(), len) };
        assert_eq!(expect, bytes);
    }
}
