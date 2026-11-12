// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

// Once const generics is completed this should be able to be
// done better that way.

// 32-bit ARM swaps out the curves that use some of these.
#![cfg_attr(any(rind_backend = "arm", rind_backend = "portable"), allow(dead_code))]

macro_rules! little_endian {
    ([u64; $N:literal], $fn_array_to:ident, $fn_slice_to:ident, $fn_to_bytes:ident) => {
        pub(crate) fn $fn_array_to(b: &[u8; $N * 8]) -> [u64; $N] {
            let mut r = [0; $N];
            for (ir, b) in (0..$N).zip(b.chunks_exact(8)) {
                r[ir] = u64::from_le_bytes(b.try_into().unwrap());
            }
            r
        }

        #[allow(dead_code)]
        pub(crate) fn $fn_slice_to(bytes: &[u8]) -> Option<[u64; $N]> {
            let as_array: [u8; $N * 8] = bytes.try_into().ok()?;
            Some($fn_array_to(&as_array))
        }

        // Indexes rather than zipping `chunks_exact_mut`, which Aeneas cannot
        // translate, so `proofs/` can prove X25519's encoding.
        #[allow(dead_code)]
        pub(crate) fn $fn_to_bytes(v: &[u64; $N]) -> [u8; $N * 8] {
            let mut r = [0u8; $N * 8];
            for (i, word) in v.iter().enumerate() {
                r[i * 8..(i + 1) * 8].copy_from_slice(&word.to_le_bytes());
            }
            r
        }
    };
}

little_endian!(
    [u64; 4],
    little_endian_to_u64x4,
    little_endian_slice_to_u64x4,
    u64x4_to_little_endian
);
little_endian!(
    [u64; 8],
    little_endian_to_u64x8,
    little_endian_slice_to_u64x8,
    u64x8_to_little_endian
);

// Indexes rather than reversing `chunks_exact` and `chunks_exact_mut`, which
// Aeneas cannot translate, so `proofs/` can prove P-256's encoding. The
// compiled code is the same.
macro_rules! big_endian {
    ([u64; $N:literal], $fn_array_to:ident, $fn_slice_to:ident, $fn_slice_any_size_to:ident, $fn_to_bytes:ident) => {
        pub(crate) fn $fn_array_to(b: &[u8; $N * 8]) -> [u64; $N] {
            let mut r = [0; $N];
            for ir in 0..$N {
                let b = &b[($N - 1 - ir) * 8..($N - ir) * 8];
                r[ir] = u64::from_be_bytes(b.try_into().unwrap());
            }
            r
        }

        #[allow(dead_code)]
        pub(crate) fn $fn_slice_to(bytes: &[u8]) -> Option<[u64; $N]> {
            let as_array: [u8; $N * 8] = bytes.try_into().ok()?;
            Some($fn_array_to(&as_array))
        }

        pub(crate) fn $fn_slice_any_size_to(bytes: &[u8]) -> Option<[u64; $N]> {
            // short circuit for correct lengths
            if let Ok(array) = bytes.try_into() {
                return Some($fn_array_to(array));
            }

            fn add_leading_zeroes(bytes: &[u8]) -> [u64; $N] {
                let mut tmp = [0u8; $N * 8];
                tmp[$N * 8 - bytes.len()..].copy_from_slice(bytes);
                $fn_array_to(&tmp)
            }

            fn remove_leading_zeroes(mut bytes: &[u8]) -> Option<[u64; $N]> {
                loop {
                    // remove the next leading zero
                    match bytes.split_first() {
                        Some((first, remain)) if *first == 0x00 => {
                            if let Ok(array) = remain.try_into() {
                                return Some($fn_array_to(array));
                            }
                            bytes = remain;
                        }
                        _ => return None,
                    }
                }
            }

            if bytes.len() < $N * 8 {
                Some(add_leading_zeroes(bytes))
            } else {
                remove_leading_zeroes(bytes)
            }
        }

        pub(crate) fn $fn_to_bytes(v: &[u64; $N]) -> [u8; $N * 8] {
            let mut r = [0u8; $N * 8];
            for iv in 0..$N {
                r[($N - 1 - iv) * 8..($N - iv) * 8].copy_from_slice(&v[iv].to_be_bytes());
            }
            r
        }
    };
}

big_endian!(
    [u64; 4],
    big_endian_to_u64x4,
    big_endian_slice_to_u64x4,
    big_endian_slice_any_size_to_u64x4,
    u64x4_to_big_endian
);
big_endian!(
    [u64; 6],
    big_endian_to_u64x6,
    big_endian_slice_to_u64x6,
    big_endian_slice_any_size_to_u64x6,
    u64x6_to_big_endian
);
big_endian!(
    [u64; 9],
    big_endian_to_u64x9,
    big_endian_slice_to_u64x9,
    big_endian_slice_any_size_to_u64x9,
    u64x9_to_big_endian
);

/// Writes the width-`W` non-adjacent form of `k` into `digits`, lowest
/// digit first: each digit is zero or odd and below 2^(W - 1) in
/// magnitude, and any `W` digits in a row hold at most one that is nonzero.
/// `digits` needs one more digit than `k` has bits.
///
/// The digits follow `k`'s bits, so it must not be secret.
pub(crate) fn public_naf<const W: u32>(k: &[u64], digits: &mut [i8]) {
    // The low W bits of what remains of k, above the digits written.
    let mut window = (k[0] & ((1 << W) - 1)) as i32;
    // Indexed rather than `iter_mut`, which Aeneas cannot translate.
    #[allow(clippy::needless_range_loop)]
    for i in 0..digits.len() {
        digits[i] = 0;
        if window & 1 == 1 {
            let d = match window < 1 << (W - 1) {
                true => window,
                false => window - (1 << W),
            };
            window -= d;
            digits[i] = d as i8;
        }
        window = (window >> 1) + (bit(k, i + W as usize) << (W - 1));
    }
}

/// Bit `i` of `k`, zero above its top.
///
/// A function rather than a closure in [`public_naf`], whose `W` Aeneas then
/// cannot place.
fn bit(k: &[u64], i: usize) -> i32 {
    match k.get(i / 64) {
        Some(word) => ((word >> (i % 64)) & 1) as i32,
        None => 0,
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use proptest::prelude::*;

    use super::*;

    proptest! {
        #![proptest_config(crate::test::proptest_config())]
        #[test]
        fn naf(k: [u64; 4]) {
            let mut digits = [0i8; 257];
            public_naf::<5>(&k, &mut digits);

            // Digits sum back to k, as 257-bit two's complement.
            let mut sum = [0u64; 5];
            for &d in digits.iter().rev() {
                let mut carry = 0;
                for word in &mut sum {
                    let shifted = (*word << 1) | carry;
                    carry = *word >> 63;
                    *word = shifted;
                }
                let addend = i64::from(d) as u64;
                let fill = if d < 0 { u64::MAX } else { 0 };
                let mut c = false;
                for (j, word) in sum.iter_mut().enumerate() {
                    let a = if j == 0 { addend } else { fill };
                    let (s1, c1) = word.overflowing_add(a);
                    let (s2, c2) = s1.overflowing_add(u64::from(c));
                    *word = s2;
                    c = c1 | c2;
                }
            }
            prop_assert_eq!(&sum[..4], &k[..]);
            prop_assert_eq!(sum[4], 0);

            for window in digits.windows(5) {
                prop_assert!(window.iter().filter(|&&d| d != 0).count() <= 1);
            }
            for d in digits {
                prop_assert!(d == 0 || (d % 2 != 0 && d.abs() < 16));
            }
        }
    }
}
