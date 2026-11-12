// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RFC 9380's `P521_XMD:SHA-512_SSWU_RO_`, and hashing to a scalar mod n.

#![cfg_attr(not(test), allow(dead_code))]

use super::{
    CURVE_A, CURVE_B, CURVE_ONE, CURVE_ORDER_MM, FieldElement, JacobianPoint, PublicKey, Scalar,
    util,
};
use crate::error::Error;
use crate::low;
use crate::mid::hash_to_curve::{self, Curve};
use crate::mid::sha2::Sha512Context;

/// Hashes `msg` to a point, by RFC 9380's `P521_XMD:SHA-512_SSWU_RO_` with
/// the domain separation tag `dst`.
///
/// The two map outputs are added in constant time. Opposite outputs would
/// sum to infinity (`Z = 0`); no message is known to reach that. This
/// selects a 1 for `Z` in that case so `as_affine` inverts a nonzero
/// element, and neither declassifies nor branches on the bit.
pub(crate) fn hash_to_curve(msg: &[u8], dst: &[u8]) -> Result<PublicKey, Error> {
    let _entry = low::Entry::new_secret();
    let mut point = hash_to_curve::hash_to_curve::<FieldElement, Sha512Context>(msg, dst)?;
    point[2] = point[2].select(&FieldElement::ONE, point[2].ct_eq(&FieldElement::ZERO));
    Ok(PublicKey {
        point: jacobian(&point).as_affine(),
    })
}

/// Hashes `msg` to a scalar mod n, by RFC 9380's `hash_to_field` over
/// `expand_message_xmd` with SHA-512 and the domain separation tag `dst`,
/// as RFC 9497's P-521 suite does. It may be zero.
pub(crate) fn hash_to_scalar(msg: &[u8], dst: &[u8]) -> Result<Scalar, Error> {
    let _entry = low::Entry::new_secret();
    let mut uniform = [0; 98];
    hash_to_curve::expand_message_xmd::<Sha512Context>(msg, dst, &mut uniform)?;
    // `hi * 2^576 + lo`, where `hi * R^2 / R` is `hi * 2^576` mod n, and
    // `reduce_mod_n` reduces any nine words.
    let (hi, lo) = uniform.split_at(26);
    let lo = Scalar(util::big_endian_slice_to_u64x9(lo).unwrap()).reduce_mod_n();
    let hi = Scalar(util::big_endian_slice_any_size_to_u64x9(hi).unwrap());
    Ok(lo.add(&hi.mont_mul(&Scalar(CURVE_ORDER_MM))))
}

fn jacobian([x, y, z]: &[FieldElement; 3]) -> JacobianPoint {
    let mut xyz = [0; 27];
    xyz[JacobianPoint::X].copy_from_slice(&x.0);
    xyz[JacobianPoint::Y].copy_from_slice(&y.0);
    xyz[JacobianPoint::Z].copy_from_slice(&z.0);
    JacobianPoint { xyz }
}

impl Curve for FieldElement {
    const L: usize = 98;
    const ZERO: Self = Self([0; 9]);
    const ONE: Self = CURVE_ONE;
    const A: Self = CURVE_A;
    const B: Self = CURVE_B;

    /// -4.
    const Z: Self = Self([
        0xfffffffffffffffb,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0xffffffffffffffff,
        0x00000000000001ff,
    ]);

    /// The square root of 4 that is its `(p + 1) / 4`th power.
    const SQRT_MINUS_Z: Self = Self([2, 0, 0, 0, 0, 0, 0, 0, 0]);

    /// `hi * 2^520 + lo`, each below p, so reduced.
    fn from_wide(bytes: &[u8]) -> Self {
        const TWO_520: FieldElement = FieldElement([0, 0, 0, 0, 0, 0, 0, 0, 1 << 8]);
        let (hi, lo) = bytes.split_at(33);
        let lo = Self(util::big_endian_slice_any_size_to_u64x9(lo).unwrap());
        let hi = Self(util::big_endian_slice_any_size_to_u64x9(hi).unwrap());
        hi.mul(&TWO_520).add(&lo)
    }

    fn mul(&self, other: &Self) -> Self {
        self.mul(other)
    }

    fn sqr(&self) -> Self {
        self.sqr()
    }

    fn add(&self, other: &Self) -> Self {
        self.add(other)
    }

    fn neg(&self) -> Self {
        self.negate()
    }

    /// `(p - 3) / 4` is `2^519 - 1`, so `xN = self^(2^N - 1)` builds it by
    /// doubling N to 512, then adding `x7`.
    fn pow_c1(&self) -> Self {
        let sqr_n = |x: &Self, n| (0..n).fold(*x, |x, _| x.sqr());
        let x2 = self.sqr().mul(self);
        let x3 = x2.sqr().mul(self);
        let x4 = sqr_n(&x2, 2).mul(&x2);
        let x7 = sqr_n(&x4, 3).mul(&x3);
        let x8 = sqr_n(&x4, 4).mul(&x4);
        let x16 = sqr_n(&x8, 8).mul(&x8);
        let x32 = sqr_n(&x16, 16).mul(&x16);
        let x64 = sqr_n(&x32, 32).mul(&x32);
        let x128 = sqr_n(&x64, 64).mul(&x64);
        let x256 = sqr_n(&x128, 128).mul(&x128);
        let x512 = sqr_n(&x256, 256).mul(&x256);
        sqr_n(&x512, 7).mul(&x7)
    }

    fn sgn0(&self) -> u8 {
        (self.0[0] & 1) as u8
    }

    fn ct_eq(&self, other: &Self) -> bool {
        low::bignum_eq(&self.0, &other.0)
    }

    fn select(&self, other: &Self, choice: bool) -> Self {
        Self::select(self, other, choice.into())
    }

    fn add_points(p: &[Self; 3], q: &[Self; 3]) -> [Self; 3] {
        coordinates(&jacobian(p).add(&jacobian(q)))
    }

    fn double_point(p: &[Self; 3]) -> [Self; 3] {
        coordinates(&jacobian(p).double())
    }
}

fn coordinates(p: &JacobianPoint) -> [FieldElement; 3] {
    [p.x(), p.y(), p.z()]
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use p521::NistP521;
    use p521::elliptic_curve::array::typenum::U98;
    use p521::elliptic_curve::sec1::ToSec1Point;
    use p521::hash2curve::{self as rustcrypto, GroupDigest};

    use super::*;
    use crate::mid::hash_to_curve::tests;

    fn affine(p: &[FieldElement; 3]) -> Vec<u8> {
        jacobian(p).as_affine().as_bytes_uncompressed().to_vec()
    }

    fn doubled(p: &[FieldElement; 3]) -> [FieldElement; 3] {
        coordinates(&jacobian(p).double())
    }

    #[test]
    fn rfc9380() {
        tests::check_suite::<FieldElement, Sha512Context>("P521_XMD_SHA-512_SSWU_RO_", 66, affine);
    }

    #[test]
    fn sum() {
        tests::check_sum::<FieldElement>(affine, doubled);
    }

    #[test]
    fn pow_c1() {
        tests::check_pow_c1::<FieldElement>(|x| (0..519).fold(*x, |x, _| x.sqr()));
    }

    #[test]
    fn from_wide() {
        tests::check_from_wide::<FieldElement>();
    }

    #[test]
    fn constants() {
        let four = FieldElement([4, 0, 0, 0, 0, 0, 0, 0, 0]);
        assert!(FieldElement::Z.ct_eq(&four.negate()));
        assert!(FieldElement::SQRT_MINUS_Z.sqr().ct_eq(&four));
    }

    #[test]
    fn hashes_in_constant_time() {
        tests::hashes_in_constant_time::<FieldElement, Sha512Context>(|p| {
            let p = affine(p);
            low::ct::public_slice(&p);
            p
        });
        // The wrapper, so a branch on Z is under taint.
        let msg = low::ct::into_secret(*b"password");
        let point = hash_to_curve(&msg, b"QUUX-V01-CS02").unwrap();
        low::ct::public_slice(&point.point.as_bytes_uncompressed());
    }

    /// The public functions, against RustCrypto's, as aws-lc has no
    /// P-521 suite.
    #[test]
    fn crosscheck() {
        for (msg, dst) in crate::test::hash_to_curve_inputs() {
            let ours = hash_to_curve(&msg, &dst).unwrap();
            let theirs = NistP521::hash_from_bytes(&[&msg], &[&dst]).unwrap();
            assert_eq!(
                ours.point.as_bytes_uncompressed()[..],
                theirs.to_affine().to_sec1_point(false).as_bytes()[..]
            );

            let ours = hash_to_scalar(&msg, &dst).unwrap();
            let theirs = rustcrypto::hash_to_scalar::<
                NistP521,
                <NistP521 as GroupDigest>::ExpandMsg,
                U98,
            >(&[&msg], &[&dst])
            .unwrap();
            assert_eq!(ours.as_bytes()[..], theirs.to_bytes()[..]);
        }
    }

    /// An empty DST is refused. aws-lc has no P-521 suite, so this is
    /// only the local path.
    #[test]
    fn empty_dst() {
        tests::check_empty_dst(
            hash_to_curve(b"msg", b"").map(|_| ()),
            hash_to_scalar(b"msg", b"").map(|_| ()),
            None,
        );
    }

    #[test]
    fn scalar_in_constant_time() {
        let msg = low::ct::into_secret(*b"password");
        let scalar = hash_to_scalar(&msg, b"QUUX-V01-CS02").unwrap();
        low::ct::public_slice(&scalar.0);
        let again = hash_to_scalar(b"password", b"QUUX-V01-CS02").unwrap();
        assert_eq!(scalar.0, again.0);
    }
}
