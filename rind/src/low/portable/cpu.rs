// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

/// The portable code needs nothing beyond the base instruction set.
pub(crate) fn missing_cpu_feature() -> Option<&'static str> {
    None
}

/// No data-independent timing mode to enable.
pub(crate) fn enter_cpu_state() -> u32 {
    0
}

/// Nothing to restore, since `enter_cpu_state` changed nothing.
pub(crate) fn leave_cpu_state(_old: u32) {}

/// Effectively memset(ptr, 0, len), but not visible to optimiser
///
/// # Safety:
/// There must be `len` writable bytes at `ptr`; with no alignment
/// requirement.
pub(in crate::low) unsafe fn zero_bytes(ptr: *mut u8, len: usize) {
    for i in 0..len {
        // SAFETY: the caller guarantees `len` writable bytes at `ptr`, and a
        // volatile write is one the compiler must keep.
        unsafe { ptr.add(i).write_volatile(0) };
    }
}

/// Compares the first `min(a.len(), b.len())` bytes of `a` and `b`, reading
/// every one of them whatever their values.
///
/// Returns zero if they are equal, otherwise non-zero.
pub(in crate::low) fn ct_compare_bytes(a: &[u8], b: &[u8]) -> u8 {
    let (len, a, b) = (a.len().min(b.len()), a.as_ptr(), b.as_ptr());
    let mut acc = 0;
    for i in 0..len {
        // SAFETY: both hold `len` readable bytes, and a
        // volatile read is one the compiler must keep, so it cannot stop
        // early once `acc` has every bit set.
        acc |= unsafe { a.add(i).read_volatile() ^ b.add(i).read_volatile() };
    }
    acc
}

/// Compares two 16-byte blocks, such as AEAD tags, in constant time.
///
/// Returns zero if `a == b`, otherwise non-zero. The difference is folded
/// behind `black_box`, so the compiler cannot split the test into early
/// exits.
pub(in crate::low) fn ct_compare_16(a: &[u8; 16], b: &[u8; 16]) -> usize {
    let diff = core::hint::black_box(u128::from_ne_bytes(*a) ^ u128::from_ne_bytes(*b));
    let diff = diff as u64 | (diff >> 64) as u64;
    (diff as u32 | (diff >> 32) as u32) as usize
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn needs_nothing_and_keeps_no_state() {
        assert_eq!(missing_cpu_feature(), None);
        assert_eq!(enter_cpu_state(), 0);
        leave_cpu_state(0);
        leave_cpu_state(1);
    }

    #[test]
    fn zero_and_compare() {
        let mut buf = [1u8, 2, 3, 4];
        // SAFETY: `buf` is four writable bytes.
        unsafe { zero_bytes(buf.as_mut_ptr(), 3) };
        assert_eq!(buf, [0, 0, 0, 4]);

        assert_eq!(ct_compare_bytes(b"", b"ab"), 0);
        assert_eq!(ct_compare_bytes(b"ab", b"ab"), 0);
        assert_eq!(ct_compare_bytes(b"ab", b"a"), 0);
        assert_ne!(ct_compare_bytes(b"ab", b"ac"), 0);
        assert_ne!(ct_compare_bytes(b"ab", b"xb"), 0);

        assert_eq!(ct_compare_16(&[0; 16], &[0; 16]), 0);
        let mut other = [0u8; 16];
        other[15] = 1;
        assert_ne!(ct_compare_16(&[0; 16], &other), 0);
    }
}
