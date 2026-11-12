// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! edwards25519 over curve25519-dalek, for armv7 and the portable backend.
//!
//! Those targets' Ed25519 already multiplies with dalek. ECVRF uses the same
//! points: variable-base [`Point::mul`] is dalek's constant-time Edwards
//! multiplication, and the base-point product uses its precomputed table.

use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};

use crate::low;

/// An integer modulo the prime order of edwards25519, reduced.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Scalar(curve25519_dalek::Scalar);

impl Scalar {
    /// Reads a little-endian scalar, or `None` unless it is below `L`.
    ///
    /// Whether it is below `L` is public; the value stays secret.
    pub(crate) fn from_canonical_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let s = curve25519_dalek::Scalar::from_canonical_bytes(*bytes);
        let canonical = low::ct::into_public(bool::from(s.is_some()));
        // `unwrap_or` selects in constant time, where `unwrap` branches.
        canonical.then(|| Self(s.unwrap_or(curve25519_dalek::Scalar::ZERO)))
    }

    /// Reduces 64 little-endian bytes modulo `L`.
    pub(crate) fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        Self(curve25519_dalek::Scalar::from_bytes_mod_order_wide(bytes))
    }

    pub(crate) fn to_bytes(self) -> [u8; 32] {
        self.0.to_bytes()
    }

    /// `self * other mod L`.
    pub(crate) fn mul(&self, other: &Self) -> Self {
        Self(self.0 * other.0)
    }

    /// `self + other mod L`.
    pub(crate) fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }
}

/// A point on edwards25519.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Point(EdwardsPoint);

impl Point {
    /// `[scalar]B`, for the curve's base point `B`.
    pub(crate) fn mul_base(scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self(EdwardsPoint::mul_base(&scalar.0))
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }

    /// `[scalar]self`, in constant time.
    pub(crate) fn mul(&self, scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self(self.0 * scalar.0)
    }

    /// `-(x, y) = (-x, y)`.
    pub(crate) fn negate(&self) -> Self {
        Self(-self.0)
    }

    /// `8 * self`.
    pub(crate) fn mul_cofactor(&self) -> Self {
        Self(self.0.mul_by_cofactor())
    }

    /// Whether this is the identity. The answer is public.
    ///
    /// Callers use it on points a peer sent or on a hash of public inputs,
    /// never on a secret scalar's product.
    pub(crate) fn is_identity(&self) -> bool {
        // RFC 8032 encodes the identity as `y = 1` with a clear sign bit.
        let mut identity = [0u8; 32];
        identity[0] = 1;
        low::ct::into_public(low::ct_equal(&self.to_bytes(), &identity))
    }

    /// RFC 8032's decoding, or `None` when the encoding is non-canonical or
    /// not a point.
    ///
    /// dalek reduces `y` modulo `p` and takes a set sign bit on `x = 0`, both
    /// of which RFC 8032 5.1.3 rejects. The point is kept only when its
    /// canonical encoding is the bytes it was given. Whether that holds is
    /// public; every encoding rind decodes here is a peer's, or a hash of one.
    pub(crate) fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        low::Entry::assert_held();
        let point = CompressedEdwardsY(*bytes).decompress()?;
        let encoded = point.compress().to_bytes();
        low::ct::into_public(low::ct_equal(&encoded[..], &bytes[..])).then_some(Self(point))
    }

    /// RFC 8032's encoding.
    pub(crate) fn to_bytes(self) -> [u8; 32] {
        low::Entry::assert_held();
        self.0.compress().to_bytes()
    }
}
