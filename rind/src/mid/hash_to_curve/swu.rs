// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Simplified SWU, straight-line, for a prime field with `p = 3 (mod 4)`.
//!
//! The map is RFC 9380 Appendix F.2. `sqrt_ratio` is Appendix F.2.1.2, one
//! exponentiation by the public `(p - 3) / 4` and a conditional select, with
//! no branch on the value. The field operations are the ones the NIST curves
//! already run: s2n-bignum's verified routines on x86_64 and aarch64, and
//! fiat-crypto's proven arithmetic on armv7 and the portable backend (whose
//! multiplication is rind's, checked against fiat-crypto, as
//! `low::generic::p256` states). Exponentiation is that multiplication and
//! squaring, in a fixed order. Affine addition is the curve group law on the
//! same operations, with the equal-point and opposite-point cases selected
//! rather than branched on. That composition is the correctness argument.
//!
//! `clear_cofactor` for these suites is the identity: each cofactor is 1.

use crate::low::PosInt;

/// A prime field element in the representation its curve arithmetic uses.
pub(in crate::mid) trait SwuField: Copy {
    /// `(p - 3) / 4`, little-endian, including any high zero bits of the last limb.
    const C1: &'static [u64];

    fn zero() -> Self;
    fn one() -> Self;
    fn field_add(self, rhs: Self) -> Self;
    fn field_sub(self, rhs: Self) -> Self;
    fn field_mul(self, rhs: Self) -> Self;
    fn field_sqr(self) -> Self;
    fn neg(self) -> Self;
    /// Inverse of a nonzero element, and zero at zero.
    fn inv0(self) -> Self;
    /// `b` if `flag` is nonzero, otherwise `a`. Matches RFC 9380's `CMOV(a, b, c)`.
    fn cmov(a: Self, b: Self, flag: u64) -> Self;
    /// 1 if `self` and `rhs` are equal, otherwise 0.
    fn ct_eq(self, rhs: Self) -> u64;
    /// `sgn0` for a prime field: the least significant bit of the canonical integer.
    fn sgn0(self) -> u64;

    fn pow_c1(self) -> Self {
        pow_public(self, Self::C1)
    }
}

/// `base` to the public power `exp`, little-endian.
///
/// Every bit is squared and multiplied, including leading zeros, so the
/// operation count depends only on `exp.len()`. The bits are public.
pub(super) fn pow_public<F: SwuField>(base: F, exp: &[u64]) -> F {
    let mut acc = F::one();
    for i in (0..exp.len() * 64).rev() {
        acc = acc.field_sqr();
        let bit = (exp[i / 64] >> (i % 64)) & 1;
        let product = acc.field_mul(base);
        acc = F::cmov(acc, product, bit);
    }
    acc
}

/// Curve constants for Appendix F.2, in the field representation.
#[derive(Clone, Copy)]
pub(in crate::mid) struct SwuConstants<F> {
    pub(in crate::mid) a: F,
    pub(in crate::mid) b: F,
    /// `Z` from the suite.
    pub(in crate::mid) z: F,
    /// `sqrt(-Z)`, the `c2` of `sqrt_ratio_3mod4`.
    pub(in crate::mid) sqrt_neg_z: F,
}

/// An affine point. `infinity` is 1 at the point at infinity, and then `x` and `y` are zero.
#[derive(Clone, Copy)]
pub(in crate::mid) struct Affine<F> {
    pub(in crate::mid) x: F,
    pub(in crate::mid) y: F,
    pub(in crate::mid) infinity: u64,
}

/// `sqrt_ratio_3mod4(u, v)` from Appendix F.2.1.2.
///
/// `v` must be nonzero. The map calls it with a cube of a nonzero element:
/// `A` is -3, and `Z` and `tv2` in step 7 are not both zero.
pub(super) fn sqrt_ratio<F: SwuField>(u: F, v: F, sqrt_neg_z: F) -> (u64, F) {
    let tv1 = v.field_sqr();
    let tv2 = u.field_mul(v);
    let tv1 = tv1.field_mul(tv2);
    let y1 = tv1.pow_c1().field_mul(tv2);
    let y2 = y1.field_mul(sqrt_neg_z);
    let tv3 = y1.field_sqr().field_mul(v);
    let is_qr = F::ct_eq(tv3, u);
    (is_qr, F::cmov(y2, y1, is_qr))
}

/// `map_to_curve_simple_swu` from Appendix F.2.
///
/// The result is a finite affine point. Step 25 divides by `tv4`, which is
/// `A` times either `Z` or `-tv2`, and that product is nonzero: `A` is -3,
/// `Z` is the suite's nonzero constant, and step 7 selects `-tv2` only when
/// `tv2` is nonzero.
pub(in crate::mid) fn map_to_curve<F: SwuField>(u: F, c: &SwuConstants<F>) -> Affine<F> {
    let tv1 = c.z.field_mul(u.field_sqr());
    let tv2 = tv1.field_sqr().field_add(tv1);
    let tv3 = c.b.field_mul(tv2.field_add(F::one()));
    let tv2_nonzero = F::ct_eq(tv2, F::zero()) ^ 1;
    let tv4 = F::cmov(c.z, tv2.neg(), tv2_nonzero).field_mul(c.a);
    let tv2 = tv3.field_sqr();
    let tv6 = tv4.field_sqr();
    let tv5 = c.a.field_mul(tv6);
    let tv2 = tv2.field_add(tv5).field_mul(tv3);
    let tv6 = tv6.field_mul(tv4);
    let tv5 = c.b.field_mul(tv6);
    let tv2 = tv2.field_add(tv5);
    let x = tv1.field_mul(tv3);
    let (is_square, y1) = sqrt_ratio(tv2, tv6, c.sqrt_neg_z);
    let y = tv1.field_mul(u).field_mul(y1);
    let x = F::cmov(x, tv3, is_square);
    let y = F::cmov(y, y1, is_square);
    let same_sign = (u.sgn0() ^ y.sgn0()) ^ 1;
    let y = F::cmov(y.neg(), y, same_sign);
    let x = x.field_mul(tv4.inv0());
    Affine { x, y, infinity: 0 }
}

/// Affine sum of two finite points.
///
/// Distinct points use the chord slope. Equal points use the tangent slope.
/// Opposite points, and a doubling with `y = 0`, are the point at infinity.
/// Which case applies is a field equality, selected with `CMOV`.
pub(in crate::mid) fn add_affine<F: SwuField>(p: Affine<F>, q: Affine<F>, a: F) -> Affine<F> {
    let same = F::ct_eq(p.x, q.x) & F::ct_eq(p.y, q.y);
    let opposite = F::ct_eq(p.x, q.x) & (F::ct_eq(p.y, q.y) ^ 1);
    let dx = q.x.field_sub(p.x);
    let dy = q.y.field_sub(p.y);
    let x2 = p.x.field_sqr();
    let num_double = x2.field_add(x2).field_add(x2).field_add(a);
    let den_double = p.y.field_add(p.y);
    let num = F::cmov(dy, num_double, same);
    let den = F::cmov(F::cmov(dx, den_double, same), F::zero(), opposite);
    let lam = num.field_mul(den.inv0());
    let x = lam.field_sqr().field_sub(p.x).field_sub(q.x);
    let y = lam.field_mul(p.x.field_sub(x)).field_sub(p.y);
    let infinity = F::ct_eq(den, F::zero());
    Affine {
        x: F::cmov(x, F::zero(), infinity),
        y: F::cmov(y, F::zero(), infinity),
        infinity,
    }
}

/// `OS2IP(bytes) mod modulus`.
///
/// `modulus` is `M` little-endian limbs with a nonzero top limb, and `r2` is
/// `2^(128 M) mod modulus`, the Montgomery factor `bignum_montifier` returns.
/// `bytes` is a big-endian integer of 1 to 128 bytes, below `2^(64 M)` times
/// the modulus, which holds for every suite `L`: the input is shorter than
/// two field elements. Reduction is Montgomery reduction of that width, which
/// s2n-bignum's `bignum_montredc` performs, then multiplication by `r2` to
/// cancel the Montgomery factor. The lengths are public.
pub(in crate::mid) fn reduce_be<const M: usize>(
    bytes: &[u8],
    modulus: &[u64; M],
    r2: &[u64; M],
) -> [u64; M] {
    assert!(M < 16, "hash-to-field modulus is wider than its input");
    assert!(!bytes.is_empty(), "hash-to-field element is empty");
    assert!(bytes.len() <= 128, "hash-to-field element is wider than L");

    let limbs = bytes.len().div_ceil(8);
    let mut words = [0u64; 16];
    for (i, &byte) in bytes.iter().enumerate() {
        let from_right = bytes.len() - 1 - i;
        words[from_right / 8] |= u64::from(byte) << ((from_right % 8) * 8);
    }
    let input = PosInt::<16>::from_words(&words[..limbs]).expect("input fits");
    let modulus = PosInt::<M>::from_words(modulus).expect("modulus width");
    let r2 = PosInt::<M>::from_words(r2).expect("montifier width");
    let reduced = input.reduce(&modulus, &r2);
    let mut out = [0u64; M];
    out.copy_from_slice(reduced.as_words());
    out
}
