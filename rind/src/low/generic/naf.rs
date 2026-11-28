// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Non-adjacent forms of public scalars, which variable-time multiplications
//! read.

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

    /// The digits sum back to `k`, as 257-bit two's complement, and each
    /// `W` in a row hold at most one nonzero digit, odd and below 2^(W - 1).
    fn check<const W: u32>(k: [u64; 4]) -> Result<(), TestCaseError> {
        let mut digits = [0i8; 257];
        public_naf::<W>(&k, &mut digits);

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

        for window in digits.windows(W as usize) {
            prop_assert!(window.iter().filter(|&&d| d != 0).count() <= 1);
        }
        for d in digits {
            prop_assert!(d == 0 || (d % 2 != 0 && i32::from(d).abs() < 1 << (W - 1)));
        }
        Ok(())
    }

    proptest! {
        // Ed25519 verification takes widths 5 and 8, the NIST curves 5 and 6.
        #[test]
        fn naf(k: [u64; 4]) {
            check::<5>(k)?;
            check::<6>(k)?;
            check::<8>(k)?;
        }
    }
}
