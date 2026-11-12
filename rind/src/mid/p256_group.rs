// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! P-256 points for ECVRF, over this module's parent arithmetic.
//!
//! Proving multiplies with the constant-time variable-base and base-point
//! products ECDH already uses. Verification adds public points with the
//! complete sum, which has to accept a peer forcing equal or opposite inputs.

pub(crate) use super::Scalar;
use super::{AffineMontPoint, JacobianMontPoint};
use crate::error::Error;
use crate::low;

/// A P-256 point, or the identity, which the compressed encoding cannot hold.
#[derive(Clone, Copy)]
pub(crate) struct Point {
    inner: Kind,
}

/// Private, so the parent's affine point stays a private type.
#[derive(Clone, Copy)]
enum Kind {
    Identity,
    Affine(AffineMontPoint),
}

impl Point {
    /// Decodes an X9.62 compressed point. The identity is not that encoding.
    pub(crate) fn from_compressed(bytes: &[u8]) -> Result<Self, Error> {
        low::Entry::assert_held();
        Ok(Self {
            inner: Kind::Affine(AffineMontPoint::from_x962_compressed(bytes)?),
        })
    }

    /// The X9.62 compressed encoding, or `None` for the identity.
    pub(crate) fn to_compressed(self) -> Option<[u8; 33]> {
        let Kind::Affine(point) = self.inner else {
            return None;
        };
        let raw = point.as_bytes_uncompressed();
        let mut out = [0u8; 33];
        // Big-endian `y`'s low bit is the low bit of its last byte.
        out[0] = 0x02 | (raw[64] & 1);
        out[1..].copy_from_slice(&raw[1..33]);
        Some(out)
    }

    /// `[scalar]self`, in constant time.
    ///
    /// `scalar` is in `[1, n)`. Zero is not a secret this proves with, and
    /// the product of zero is the identity only through [`Self::mul_public`].
    pub(crate) fn mul(self, scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self {
            inner: match self.inner {
                Kind::Identity => Kind::Identity,
                Kind::Affine(point) => Kind::Affine(point.multiply(scalar)),
            },
        }
    }

    /// `[scalar]G`, in constant time. `scalar` is in `[1, n)`.
    pub(crate) fn mul_base(scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self {
            inner: Kind::Affine(AffineMontPoint::base_multiply(scalar)),
        }
    }

    /// `[scalar]self` for a public scalar, including zero.
    pub(crate) fn mul_public(self, scalar: &Scalar) -> Self {
        if low::ct::into_public(scalar.is_zero()) {
            return Self {
                inner: Kind::Identity,
            };
        }
        self.mul(scalar)
    }

    /// `[scalar]G` for a public scalar, including zero.
    pub(crate) fn mul_base_public(scalar: &Scalar) -> Self {
        if low::ct::into_public(scalar.is_zero()) {
            return Self {
                inner: Kind::Identity,
            };
        }
        Self::mul_base(scalar)
    }

    pub(crate) fn negate(self) -> Self {
        Self {
            inner: match self.inner {
                Kind::Identity => Kind::Identity,
                Kind::Affine(mut point) => {
                    point.negate_y();
                    Kind::Affine(point)
                }
            },
        }
    }

    /// `self + other` for public points, including equal, opposite, and the
    /// identity.
    pub(crate) fn add_public(self, other: Self) -> Self {
        Self {
            inner: match (self.inner, other.inner) {
                (Kind::Identity, point) | (point, Kind::Identity) => point,
                (Kind::Affine(left), Kind::Affine(right)) => {
                    let sum = JacobianMontPoint::from_affine(&left).public_add_affine(&right);
                    match affine_if_finite(sum) {
                        Some(point) => Kind::Affine(point),
                        None => Kind::Identity,
                    }
                }
            },
        }
    }
}

/// The affine point, or `None` at infinity, where inverting `z` is undefined.
fn affine_if_finite(point: JacobianMontPoint) -> Option<AffineMontPoint> {
    if point.public_is_infinity() {
        return None;
    }
    let z_inv = point.z().demont().inv().as_mont();
    Some(point.as_affine_by(&z_inv))
}

pub(crate) fn scalar_checked(bytes: &[u8]) -> Result<Scalar, Error> {
    Scalar::from_bytes_checked(bytes)
}

/// A 32-byte big-endian scalar in `0..n`, zero included.
///
/// Whether it is in range is public. A proof's `s` may be zero; a secret
/// key may not, and uses [`scalar_checked`].
pub(crate) fn scalar_canonical(bytes: &[u8]) -> Result<Scalar, Error> {
    if bytes.len() != 32 {
        return Err(Error::BadSignature);
    }
    let reduced = Scalar::from_bytes_reduced(bytes)?;
    let canonical = low::ct_equal(&reduced.as_bytes(), bytes);
    if !low::ct::into_public(canonical) {
        return Err(Error::BadSignature);
    }
    Ok(reduced)
}

/// A big-endian integer reduced modulo the group order. It may be zero.
pub(crate) fn scalar_reduced(bytes: &[u8]) -> Result<Scalar, Error> {
    Scalar::from_bytes_reduced(bytes)
}

pub(crate) fn scalar_mul(left: &Scalar, right: &Scalar) -> Scalar {
    left.as_mont().mont_mul(&right.as_mont()).demont()
}

pub(crate) fn scalar_add(left: &Scalar, right: &Scalar) -> Scalar {
    left.add(right)
}

pub(crate) fn scalar_bytes(scalar: &Scalar) -> [u8; 32] {
    scalar.as_bytes()
}
