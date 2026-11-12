// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! P-384's Montgomery multiplication and squaring on 32-bit limbs, mod p and
//! mod n, for `p384`.
//!
//! fiat-crypto's multiplication runs interleaved carry chains, which LLVM
//! keeps in the one carry flag on armv7, saving and restoring it between
//! them, so rind multiplies with 64-bit accumulators instead (`umaal`), as
//! Montgomery's method in the textbook form, with no secret-dependent branch
//! or index either.  It is not proven: the tests check it against
//! fiat-crypto and s2n-bignum.
//!
//! Arithmetic on secrets wraps: the bounds rule out overflow, and a debug
//! build's overflow check would branch on secret values.

use super::p384::{Fe, Fs, N, P, split, subtract_if_above};

/// `x * y / 2^384 mod p_384`, for `x` and `y` below p.
pub(super) fn fe_mul(x: &Fe, y: &Fe) -> Fe {
    Fe(reduce_p(&mul_wide(&x.0, &y.0)))
}

/// `x^2 / 2^384 mod p_384`, for `x` below p.
pub(super) fn fe_sqr(x: &Fe) -> Fe {
    Fe(reduce_p(&sqr_wide(&x.0)))
}

/// `x * y / 2^384 mod n_384`, for `x` and `y` below n.
pub(super) fn fs_mul(x: &Fs, y: &Fs) -> Fs {
    Fs(reduce_n(&mul_wide(&x.0, &y.0)))
}

/// `x^2 / 2^384 mod n_384`, for `x` below n.
pub(super) fn fs_sqr(x: &Fs) -> Fs {
    Fs(reduce_n(&sqr_wide(&x.0)))
}

/// The 768-bit `x * y`, a row of `x * y[i]` at a time.
fn mul_wide(x: &[u32; 12], y: &[u32; 12]) -> [u32; 24] {
    let mut t = [0; 24];
    mul_row::<0>(&mut t, x, y[0]);
    mul_row::<1>(&mut t, x, y[1]);
    mul_row::<2>(&mut t, x, y[2]);
    mul_row::<3>(&mut t, x, y[3]);
    mul_row::<4>(&mut t, x, y[4]);
    mul_row::<5>(&mut t, x, y[5]);
    mul_row::<6>(&mut t, x, y[6]);
    mul_row::<7>(&mut t, x, y[7]);
    mul_row::<8>(&mut t, x, y[8]);
    mul_row::<9>(&mut t, x, y[9]);
    mul_row::<10>(&mut t, x, y[10]);
    mul_row::<11>(&mut t, x, y[11]);
    t
}

/// Adds `x * yi` to `t` at word `I`, where words `I + 12` and up are zero.
///
/// Each row is its own instance, so LLVM unrolls all twelve.
fn mul_row<const I: usize>(t: &mut [u32; 24], x: &[u32; 12], yi: u32) {
    let mut carry = 0;
    for (j, x) in x.iter().enumerate() {
        (t[I + j], carry) = mul_add(*x, yi, t[I + j], carry);
    }
    t[I + 12] = carry;
}

/// The 768-bit `x^2`: each product of two different words once, doubled,
/// plus the square of each word.
fn sqr_wide(x: &[u32; 12]) -> [u32; 24] {
    let mut t = [0; 24];
    sqr_row::<0>(&mut t, x);
    sqr_row::<1>(&mut t, x);
    sqr_row::<2>(&mut t, x);
    sqr_row::<3>(&mut t, x);
    sqr_row::<4>(&mut t, x);
    sqr_row::<5>(&mut t, x);
    sqr_row::<6>(&mut t, x);
    sqr_row::<7>(&mut t, x);
    sqr_row::<8>(&mut t, x);
    sqr_row::<9>(&mut t, x);
    sqr_row::<10>(&mut t, x);

    // The products sum to below 2^767, so doubling them cannot overflow.
    for k in (1..24).rev() {
        t[k] = (t[k] << 1) | (t[k - 1] >> 31);
    }
    t[0] <<= 1;

    let mut carry = 0;
    for (i, x) in x.iter().enumerate() {
        let (lo, hi) = mul_add(*x, *x, t[2 * i], carry);
        t[2 * i] = lo;
        (t[2 * i + 1], carry) = add(t[2 * i + 1], hi, 0);
    }
    t
}

/// Adds `x[I + 1..] * x[I]` to `t` at word `2I + 1`, where words `I + 12`
/// and up are zero.
fn sqr_row<const I: usize>(t: &mut [u32; 24], x: &[u32; 12]) {
    let mut carry = 0;
    for j in I + 1..12 {
        (t[I + j], carry) = mul_add(x[j], x[I], t[I + j], carry);
    }
    t[I + 12] = carry;
}

/// `t / 2^384 mod p_384`, for `t` below 2^384 p, by Montgomery reduction.
///
/// p is 2^384 - 2^128 - 2^96 + 2^32 - 1, so -p^-1 mod 2^32 is 1, and step
/// i adds `m p 2^(32i)` for word i's value m, which zeroes it: m added at
/// words i + 1 and i + 12, and subtracted at i + 3 and i + 4.  Those gather
/// in signed 64-bit columns, each carried into the next only when its step
/// reaches it, so no carry chain runs across another.  Column k holds its
/// word of t, two words added and two subtracted, and a carry of -2 to 3
/// from column k - 1, so it stays within [-2^33, 3 * 2^32] and carries -2
/// to 3 itself.  The result is below 2p < 2^385.
fn reduce_p(t: &[u32; 24]) -> [u32; 12] {
    let mut col = t.map(i64::from);
    for i in 0..12 {
        let m = i64::from(col[i] as u32);
        col[i + 1] = col[i + 1].wrapping_add(col[i] >> 32).wrapping_add(m);
        col[i + 3] = col[i + 3].wrapping_sub(m);
        col[i + 4] = col[i + 4].wrapping_sub(m);
        col[i + 12] = col[i + 12].wrapping_add(m);
    }

    let mut r = [0; 12];
    let mut carry = 0i64;
    for (r, col) in r.iter_mut().zip(&col[12..]) {
        let s = col.wrapping_add(carry);
        *r = s as u32;
        carry = s >> 32;
    }
    subtract_if_above(&r, carry as u32, &split(&P))
}

/// `t / 2^384 mod n_384`, for `t` below 2^384 n, by Montgomery reduction:
/// step i adds the multiple of `n 2^(32i)` that zeroes word i.  The running
/// value stays below 2^768 + 2^384 n, so the 24 words and a carry above
/// them hold it, and the result is below 2n.
fn reduce_n(t: &[u32; 24]) -> [u32; 12] {
    let n = split(&N);
    let mut t = *t;
    let mut top = 0;
    for i in 0..12 {
        let m = t[i].wrapping_mul(N_INV_NEG);
        let (_, mut carry) = mul_add(m, n[0], t[i], 0);
        for j in 1..12 {
            (t[i + j], carry) = mul_add(m, n[j], t[i + j], carry);
        }
        (t[i + 12], top) = add(t[i + 12], carry, top);
    }
    let (_, hi) = t.split_at(12);
    subtract_if_above(hi.try_into().unwrap(), top, &n)
}

/// `a * b + c + d` as its low and high words, which cannot overflow: one
/// `umaal`, which carries in its 64-bit sum rather than the flags.
fn mul_add(a: u32, b: u32, c: u32, d: u32) -> (u32, u32) {
    let s = u64::from(a)
        .wrapping_mul(u64::from(b))
        .wrapping_add(u64::from(c))
        .wrapping_add(u64::from(d));
    (s as u32, (s >> 32) as u32)
}

/// `a + b + c` as its low and high words.
fn add(a: u32, b: u32, c: u32) -> (u32, u32) {
    let s = u64::from(a)
        .wrapping_add(u64::from(b))
        .wrapping_add(u64::from(c));
    (s as u32, (s >> 32) as u32)
}

/// -n_384^-1 mod 2^32.
const N_INV_NEG: u32 = 0xe88f_dc45;

/// Checks rind's Montgomery multiplication and squaring against
/// fiat-crypto's, on every target with 32-bit limbs, since armv7 compiles
/// them to different instructions.
#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod fiat_tests {
    use proptest::prelude::*;

    use super::super::fiat_p384 as fp;
    use super::super::fiat_p384_scalar as fs;
    use super::super::p384::reduce;
    use super::*;

    /// A value below `m`, from words that are mostly all zeros or all ones,
    /// to run the carries the length of the value, or random.
    fn below(m: [u64; 6]) -> impl Strategy<Value = [u32; 12]> {
        let word = prop_oneof![
            Just(0),
            Just(1),
            Just(u32::MAX - 1),
            Just(u32::MAX),
            Just(1 << 31),
            any::<u32>(),
        ];
        let edges = prop_oneof![
            Just(add_small(m, -1)),
            Just(add_small(m, -2)),
            Just([0, 0, 0, 0, 0, 1 << 63]),
        ];
        // Every 384-bit value is below 2m, so one subtraction reduces it.
        prop_oneof![
            4 => any::<[u32; 12]>(),
            4 => proptest::array::uniform12(word),
            1 => edges.prop_map(|x| split(&x)),
        ]
        .prop_map(move |x| reduce(x, &split(&m)))
    }

    /// `x + d`, for a low word that neither carries nor borrows.
    fn add_small(mut x: [u64; 6], d: i64) -> [u64; 6] {
        x[0] = x[0].checked_add_signed(d).unwrap();
        x
    }

    proptest! {
        #[test]
        fn field(x in below(P), y in below(P)) {
            let (x, y) = (Fe(x), Fe(y));
            let mut want = Fe([0; 12]);
            fp::fiat_p384_mul(&mut want, &x, &y);
            prop_assert_eq!(fe_mul(&x, &y).0, want.0);
            fp::fiat_p384_square(&mut want, &x);
            prop_assert_eq!(fe_sqr(&x).0, want.0);
        }

        #[test]
        fn scalar(x in below(N), y in below(N)) {
            let (x, y) = (Fs(x), Fs(y));
            let mut want = Fs([0; 12]);
            fs::fiat_p384_scalar_mul(&mut want, &x, &y);
            prop_assert_eq!(fs_mul(&x, &y).0, want.0);
            fs::fiat_p384_scalar_square(&mut want, &x);
            prop_assert_eq!(fs_sqr(&x).0, want.0);
        }
    }
}
