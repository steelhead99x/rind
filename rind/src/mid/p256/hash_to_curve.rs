// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RFC 9380's `P256_XMD:SHA-256_SSWU_RO_`, and hashing to a scalar mod n.

use super::{
    CURVE_A_MONT, CURVE_B_MONT, CURVE_ONE_MONT, CURVE_ORDER_MM, FieldElement, JacobianMontPoint,
    PublicKey, Scalar, util,
};
use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::mid::hash_to_curve::{self, Curve};
use crate::mid::sha2::Sha256Context;

/// Hashes `msg` to a point, by RFC 9380's `P256_XMD:SHA-256_SSWU_RO_` with
/// the domain separation tag `dst`.
///
/// The point at infinity, which no message is known to reach, is refused as
/// a small-order point.
pub(crate) fn hash_to_curve(msg: &[u8], dst: &[u8]) -> Result<PublicKey, Error> {
    // The caller holds the `Entry`. A nested one would drop the CPU state
    // (DIT, on Apple) while the caller still handles the point.
    low::Entry::assert_held();
    let point = hash_to_curve::hash_to_curve::<FieldElement, Sha256Context>(msg, dst)?;
    match low::ct::into_public(point[2].ct_eq(&FieldElement::ZERO)) {
        true => Err(KeyFormatError::SmallOrder.into()),
        false => Ok(PublicKey {
            point: jacobian(&point).as_affine(),
        }),
    }
}

/// Hashes `msg` to a scalar mod n, by RFC 9380's `hash_to_field` over
/// `expand_message_xmd` with SHA-256 and the domain separation tag `dst`,
/// as RFC 9497's and RFC 9591's P-256 suites do. It may be zero.
pub(crate) fn hash_to_scalar(msg: &[u8], dst: &[u8]) -> Result<Scalar, Error> {
    low::Entry::assert_held();
    let mut uniform = [0; 48];
    hash_to_curve::expand_message_xmd::<Sha256Context>(msg, dst, &mut uniform)?;
    // `hi * 2^256 + lo`, where `hi * R^2 / R` is `hi * 2^256` mod n.
    let (hi, lo) = uniform.split_at(16);
    let lo = Scalar(util::big_endian_slice_to_u64x4(lo).unwrap()).reduce_mod_n();
    let hi = Scalar(util::big_endian_slice_any_size_to_u64x4(hi).unwrap());
    Ok(lo.add(&hi.mont_mul(&Scalar(CURVE_ORDER_MM))))
}

fn jacobian([x, y, z]: &[FieldElement; 3]) -> JacobianMontPoint {
    let mut xyz = [0; 12];
    xyz[JacobianMontPoint::X].copy_from_slice(&x.0);
    xyz[JacobianMontPoint::Y].copy_from_slice(&y.0);
    xyz[JacobianMontPoint::Z].copy_from_slice(&z.0);
    JacobianMontPoint { xyz }
}

impl Curve for FieldElement {
    const L: usize = 48;
    const ZERO: Self = Self([0; 4]);
    const ONE: Self = CURVE_ONE_MONT;
    const A: Self = CURVE_A_MONT;
    const B: Self = CURVE_B_MONT;

    /// -10, in Montgomery form.
    const Z: Self = Self([
        0xfffffffffffffff5,
        0x0000000affffffff,
        0x0000000000000000,
        0xfffffff50000000b,
    ]);

    /// The square root of 10 that is its `(p + 1) / 4`th power, in
    /// Montgomery form.
    const SQRT_MINUS_Z: Self = Self([
        0xa1fd38ee98a195fd,
        0x78400ad7423dcf70,
        0x6913c88f9ea8dfee,
        0x9051d26e12a8f304,
    ]);

    /// `hi * 2^256 + lo` in Montgomery form is `lo * R + hi * R * R`, and
    /// `as_mont` reduces any four words.
    fn from_wide(bytes: &[u8]) -> Self {
        let (hi, lo) = bytes.split_at(16);
        let lo = Self(util::big_endian_slice_to_u64x4(lo).unwrap()).as_mont();
        let hi = Self(util::big_endian_slice_any_size_to_u64x4(hi).unwrap());
        lo.add(&hi.as_mont().as_mont())
    }

    fn mul(&self, other: &Self) -> Self {
        self.mont_mul(other)
    }

    fn sqr(&self) -> Self {
        self.mont_sqr()
    }

    fn add(&self, other: &Self) -> Self {
        self.add(other)
    }

    fn neg(&self) -> Self {
        self.negate_mod_p()
    }

    /// `(p - 3) / 4` is `(p + 1) / 4` (see `mont_sqrt_candidate`) less one:
    /// 32 set bits, 31 clear, one set, 96 clear, and 94 set, so `xN =
    /// self^(2^N - 1)` builds `x32` and `x94 = x64 * 2^30 + x30`.
    fn pow_c1(&self) -> Self {
        let x2 = self.mont_sqr_n(1).mont_mul(self);
        let x3 = x2.mont_sqr_n(1).mont_mul(self);
        let x6 = x3.mont_sqr_n(3).mont_mul(&x3);
        let x12 = x6.mont_sqr_n(6).mont_mul(&x6);
        let x15 = x12.mont_sqr_n(3).mont_mul(&x3);
        let x30 = x15.mont_sqr_n(15).mont_mul(&x15);
        let x32 = x30.mont_sqr_n(2).mont_mul(&x2);
        let x32_shifted = x32.mont_sqr_n(32);
        let x64 = x32_shifted.mont_mul(&x32);
        let x94 = x64.mont_sqr_n(30).mont_mul(&x30);
        x32_shifted.mont_mul(self).mont_sqr_n(190).mont_mul(&x94)
    }

    fn sgn0(&self) -> u8 {
        (self.demont().0[0] & 1) as u8
    }

    fn ct_eq(&self, other: &Self) -> bool {
        low::bignum_eq(&self.0, &other.0)
    }

    fn select(&self, other: &Self, choice: bool) -> Self {
        let mut r = Self::default();
        low::bignum_mux(choice.into(), &mut r.0, &other.0, &self.0);
        r
    }

    fn add_points(p: &[Self; 3], q: &[Self; 3]) -> [Self; 3] {
        coordinates(&jacobian(p).add(&jacobian(q)))
    }

    fn double_point(p: &[Self; 3]) -> [Self; 3] {
        coordinates(&jacobian(p).double())
    }
}

fn coordinates(p: &JacobianMontPoint) -> [FieldElement; 3] {
    [p.x(), p.y(), p.z()]
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use p256::NistP256;
    use p256::elliptic_curve::array::typenum::U48;
    use p256::hash2curve::{self as rustcrypto, GroupDigest};

    use super::*;
    use crate::mid::hash_to_curve::tests;

    fn affine(p: &[FieldElement; 3]) -> Vec<u8> {
        jacobian(p).as_affine().as_bytes_uncompressed().to_vec()
    }

    #[test]
    fn rfc9380() {
        tests::check_suite::<FieldElement, Sha256Context>("P256_XMD_SHA-256_SSWU_RO_", 32, affine);
    }

    #[test]
    fn sum() {
        tests::check_sum::<FieldElement>(affine);
    }

    #[test]
    fn pow_c1() {
        tests::check_pow_c1::<FieldElement>(FieldElement::mont_sqrt_candidate);
    }

    #[test]
    fn from_wide() {
        tests::check_from_wide::<FieldElement>();
    }

    #[test]
    fn constants() {
        let ten = FieldElement([10, 0, 0, 0]).as_mont();
        assert!(FieldElement::Z.ct_eq(&ten.negate_mod_p()));
        assert!(FieldElement::SQRT_MINUS_Z.mont_sqr().ct_eq(&ten));
        assert!(FieldElement::SQRT_MINUS_Z.ct_eq(&ten.mont_sqrt_candidate()));
    }

    #[test]
    fn hashes_in_constant_time() {
        tests::hashes_in_constant_time::<FieldElement, Sha256Context>(|p| {
            let p = affine(p);
            low::ct::public_slice(&p);
            p
        });
    }

    /// The public functions, against aws-lc's hash to the curve and
    /// RustCrypto's to a scalar.
    #[cfg(not(any(miri, target_family = "wasm")))]
    #[test]
    fn crosscheck() {
        for (msg, dst) in crate::test::hash_to_curve_inputs() {
            let ours = hash_to_curve(&msg, &dst).unwrap();
            let theirs = crate::test::aws_lc_hash_to_curve(256, &msg, &dst);
            assert_eq!(ours.point.as_bytes_uncompressed()[..], theirs[..]);

            let ours = hash_to_scalar(&msg, &dst).unwrap();
            let theirs = rustcrypto::hash_to_scalar::<
                NistP256,
                <NistP256 as GroupDigest>::ExpandMsg,
                U48,
            >(&[&msg], &[&dst])
            .unwrap();
            assert_eq!(ours.as_bytes()[..], theirs.to_bytes()[..]);
        }
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
