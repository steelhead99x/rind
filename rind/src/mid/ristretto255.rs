// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ristretto255 (RFC 9496), the prime-order group over edwards25519, on
//! s2n-bignum's field and point routines. RFC 9496's formulas are rind's
//! own, covered by its vectors and by tests against curve25519-dalek.
//!
//! Every operation runs in constant time: the OPRF client maps and blinds its
//! private input, and the server multiplies by its key.

// FROST, ECVRF, and OPAQUE are their own quests. The OPRF is the caller.

use crate::low;
pub(crate) use crate::mid::edwards25519::Scalar;
use crate::mid::edwards25519::{Fe, Point};

/// `sqrt(a * d - 1)`, for `a = -1`.
const SQRT_AD_MINUS_ONE: Fe = Fe([
    0x7e97f6a0497b2e1b,
    0xaf9d8e0c1b7854bd,
    0x0f3cfcc931f5d1fd,
    0x376931bf2b8348ac,
]);

/// `1 / sqrt(a - d)`, for `a = -1`.
const INVSQRT_A_MINUS_D: Fe = Fe([
    0x99c8fdaa805d40ea,
    0x9d2f16175a4172be,
    0x16c27b91fe01d840,
    0x786c8905cfaffca2,
]);

/// `1 - d^2`.
const ONE_MINUS_D_SQ: Fe = Fe([
    0xe27c09c1945fc176,
    0x2c81a138cd5e350f,
    0x9994abddbe70dfe4,
    0x029072a8b2b3e0d7,
]);

/// `(d - 1)^2`.
const D_MINUS_ONE_SQ: Fe = Fe([
    0x31ad5aaa44ed4d20,
    0xd29e4a2cb01e1999,
    0x4cdcd32f529b4eeb,
    0x5968b37af66c2241,
]);

/// A ristretto255 element, held as one of the edwards25519 points it stands
/// for.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Element(Point);

impl Element {
    /// `[scalar]G`, for the generator `G`.
    pub(crate) fn mul_base(scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self(Point::mul_base(scalar))
    }

    /// RFC 9496 4.3.1's decoding, or `None` for an encoding it rejects.
    ///
    /// Whether it decodes is public; the element stays secret.
    pub(crate) fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        low::Entry::assert_held();
        let (s, canonical) = Fe::from_le_bytes(bytes);

        let ss = s.square();
        let u1 = Fe::ONE.sub(&ss);
        let u2 = Fe::ONE.add(&ss);
        let u2_sqr = u2.square();
        let v = Fe::D.mul(&u1.square()).neg().sub(&u2_sqr);
        // SQRT_RATIO_M1(1, w) is (1, 1 / sqrt(w)) for a nonzero square `w`,
        // and otherwise rejected, whatever the root.
        let (was_square, invsqrt) = v.mul(&u2_sqr).invsqrt();
        let den_x = invsqrt.mul(&u2);
        let den_y = invsqrt.mul(&den_x).mul(&v);
        let x = s.add(&s).mul(&den_x).abs();
        let y = u1.mul(&den_y);
        let t = x.mul(&y);

        let valid = canonical
            & (1 ^ s.is_negative())
            & was_square
            & (1 ^ t.is_negative())
            & (1 ^ y.ct_eq(&Fe::ZERO));
        (low::ct::into_public(valid) == 1)
            .then(|| Self(Point::from_coordinates(&x, &y, &Fe::ONE, &t)))
    }

    /// RFC 9496 4.3.2's encoding.
    pub(crate) fn to_bytes(self) -> [u8; 32] {
        low::Entry::assert_held();
        let [x0, y0, z0, t0] = self.0.coordinates();
        let u1 = z0.add(&y0).mul(&z0.sub(&y0));
        let u2 = x0.mul(&y0);
        // SQRT_RATIO_M1(1, w) is 1 / sqrt(w) for a nonzero square `w`, and
        // `w = Z^6 (1 - y^2) x^2 y^2` is one unless `x y = 0`. Every element
        // is held as a point of 2E, and for `(x, y) = 2(a, b)` the curve's
        // equation makes `1 - y^2` a square times `1 + d`, a square. Where
        // `x y = 0`, `u2` is 0, so `den2`, `z_inv`, and the encoding are 0
        // whatever the root.
        let (_, invsqrt) = u1.mul(&u2.square()).invsqrt();
        let den1 = invsqrt.mul(&u1);
        let den2 = invsqrt.mul(&u2);
        let z_inv = den1.mul(&den2).mul(&t0);
        let ix0 = x0.mul(&Fe::SQRT_M1);
        let iy0 = y0.mul(&Fe::SQRT_M1);
        let enchanted_denominator = den1.mul(&INVSQRT_A_MINUS_D);
        let rotate = t0.mul(&z_inv).is_negative();
        let x = Fe::select(rotate, &iy0, &x0);
        let y = Fe::select(rotate, &ix0, &y0);
        let den_inv = Fe::select(rotate, &enchanted_denominator, &den2);
        let y = y.negate_if(x.mul(&z_inv).is_negative());
        den_inv.mul(&z0.sub(&y)).abs().to_le_bytes()
    }

    /// RFC 9496 4.3.4's one-way map from 64 uniformly random bytes.
    pub(crate) fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        low::Entry::assert_held();
        let (lo, hi) = bytes.split_at(32);
        let p1 = map(lo.try_into().unwrap());
        let p2 = map(hi.try_into().unwrap());
        Self(p1.add(&p2))
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        Self(self.0.add(&other.0))
    }

    /// `[scalar]self`, in constant time.
    pub(crate) fn mul(&self, scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self(self.0.mul(scalar))
    }
}

/// RFC 9496 4.3.4's `MAP`, from 32 bytes to a point.
fn map(bytes: &[u8; 32]) -> Point {
    let mut bytes = *bytes;
    bytes[31] &= 0x7f;
    let (t, _) = Fe::from_le_bytes(&bytes);

    let r = Fe::SQRT_M1.mul(&t.square());
    let u = r.add(&Fe::ONE).mul(&ONE_MINUS_D_SQ);
    let minus_one = Fe::ONE.neg();
    let v = minus_one.sub(&r.mul(&Fe::D)).mul(&r.add(&Fe::D));
    let (was_square, s) = Fe::sqrt_ratio_m1(&u, &v);
    let s_prime = s.mul(&t).abs().neg();
    let s = Fe::select(was_square, &s, &s_prime);
    let c = Fe::select(was_square, &minus_one, &r);
    let n = c.mul(&r.sub(&Fe::ONE)).mul(&D_MINUS_ONE_SQ).sub(&v);

    let ss = s.square();
    let w0 = s.add(&s).mul(&v);
    let w1 = n.mul(&SQRT_AD_MINUS_ONE);
    let w2 = Fe::ONE.sub(&ss);
    let w3 = Fe::ONE.add(&ss);
    Point::from_coordinates(&w0.mul(&w3), &w2.mul(&w1), &w1.mul(&w3), &w0.mul(&w2))
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    #[test]
    fn constants() {
        let d = Fe::D;
        let minus_one = Fe::ONE.neg();
        // (a d - 1) = SQRT_AD_MINUS_ONE^2
        assert_eq!(
            SQRT_AD_MINUS_ONE.square().0,
            minus_one.mul(&d).sub(&Fe::ONE).0
        );
        // (a - d) INVSQRT_A_MINUS_D^2 = 1
        assert_eq!(
            INVSQRT_A_MINUS_D.square().mul(&minus_one.sub(&d)).0,
            Fe::ONE.0
        );
        assert_eq!(ONE_MINUS_D_SQ.0, Fe::ONE.sub(&d.square()).0);
        assert_eq!(D_MINUS_ONE_SQ.0, d.sub(&Fe::ONE).square().0);
    }
}
