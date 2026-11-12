// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! edwards25519 points and scalars over curve25519-dalek, for the portable
//! backend and armv7, where rind has no s2n-bignum edwards25519.
//!
//! The names match `mid::edwards25519` on the assembly backends, so FROST
//! calls one module. dalek's arithmetic is constant time.

#![cfg_attr(not(test), allow(dead_code))]

use curve25519_dalek::constants::ED25519_BASEPOINT_TABLE;
use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::traits::Identity;
use subtle::ConstantTimeEq;

use crate::low;

/// An integer modulo the group's prime order `L`, reduced.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Scalar(curve25519_dalek::Scalar);

impl Scalar {
    /// Reads a little-endian scalar, or `None` unless it is below `L`.
    ///
    /// Whether it is below `L` is public; the value stays secret.
    pub(crate) fn from_canonical_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let s = curve25519_dalek::Scalar::from_canonical_bytes(*bytes);
        let canonical = low::ct::into_public(bool::from(s.is_some()));
        canonical.then(|| Self(s.unwrap_or(curve25519_dalek::Scalar::ZERO)))
    }

    /// Reduces 64 little-endian bytes modulo `L`.
    pub(crate) fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        Self(curve25519_dalek::Scalar::from_bytes_mod_order_wide(bytes))
    }

    pub(crate) fn to_bytes(self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// The scalar `v`. Every `u64` is below `L`.
    pub(crate) fn from_u64(v: u64) -> Self {
        Self(curve25519_dalek::Scalar::from(v))
    }

    /// `self + other mod L`.
    pub(crate) fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }

    /// `self - other mod L`.
    pub(crate) fn sub(&self, other: &Self) -> Self {
        Self(self.0 - other.0)
    }

    /// `self * other mod L`.
    pub(crate) fn mul(&self, other: &Self) -> Self {
        Self(self.0 * other.0)
    }

    /// `1 / self mod L`, or `None` for zero, which has no inverse.
    ///
    /// Whether `self` is zero is public; the value stays secret.
    pub(crate) fn invert(&self) -> Option<Self> {
        let zero = low::ct::into_public(self.0 == curve25519_dalek::Scalar::ZERO);
        (!zero).then(|| Self(self.0.invert()))
    }

    /// Whether this scalar is zero. The answer is public.
    pub(crate) fn is_zero(&self) -> bool {
        low::ct::into_public(self.0 == curve25519_dalek::Scalar::ZERO)
    }
}

/// A point on edwards25519.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Point(EdwardsPoint);

impl Point {
    /// `[scalar]B`, for the curve's base point `B`.
    pub(crate) fn mul_base(scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self(&scalar.0 * ED25519_BASEPOINT_TABLE)
    }

    /// `[scalar]self`, in constant time.
    pub(crate) fn mul(&self, scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self(self.0 * scalar.0)
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }

    /// Whether this is the identity. The answer is public.
    pub(crate) fn is_identity(&self) -> bool {
        // dalek 5.0.0's `==` is `ct_eq().into()`. Declassify the choice before
        // that conversion, which `serialize` then branches on.
        let equal = self.0.ct_eq(&EdwardsPoint::identity());
        bool::from(low::ct::into_public(equal))
    }

    /// RFC 8032's compressed Edwards `y`.
    pub(crate) fn to_edwards_bytes(self) -> [u8; 32] {
        self.0.compress().to_bytes()
    }

    /// RFC 8032's decompression, or `None` when the encoding is non-canonical
    /// or off the curve. The prime-order check is the caller's.
    pub(crate) fn from_edwards_bytes(bytes: &[u8; 32]) -> Option<Self> {
        CompressedEdwardsY(*bytes).decompress().map(Self)
    }

    /// Whether the point is in the prime-order subgroup.
    ///
    /// dalek multiplies by the group order. The point is public.
    pub(crate) fn is_torsion_free(&self) -> bool {
        self.0.is_torsion_free()
    }
}
