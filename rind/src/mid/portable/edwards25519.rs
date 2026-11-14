// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! The edwards25519 group over curve25519-dalek's, whose operations run in
//! constant time, for Ed25519, ristretto255, and ECVRF.

use curve25519_dalek::edwards::{CompressedEdwardsY, EdwardsPoint};
use curve25519_dalek::traits::Identity;
use subtle::ConstantTimeEq;

use crate::error::Error;
use crate::low;
use crate::mid::rng::{RandomSource, SystemRandom};

// Both are plain integer arrays in every dalek backend, so all zeroes is a
// value they can hold.
impl low::Zeroable for Scalar {}
impl low::Zeroable for Point {}

/// A point on edwards25519.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Point(pub(crate) EdwardsPoint);

impl Point {
    /// RFC 8032 5.1.3's decoding, or `None` for an encoding it rejects: `y`
    /// not below `p`, no point with that `y`, or `x = 0` with the sign bit
    /// set, as s2n-bignum's `edwards25519_decode` does on the other
    /// backends.
    ///
    /// Only public encodings are decoded: whether one decodes is public.
    pub(crate) fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        // dalek reduces `y` modulo `p`, and takes a set sign bit on `x = 0`
        // (where `y = ±1`) as `x = 0`, so each point would have a second
        // encoding.
        let mut y = *bytes;
        y[31] &= 0x7f;
        let negative_zero = bytes[31] >> 7 == 1 && (y == ONE || y == P_MINUS_ONE);
        if !is_below_p(&y) || negative_zero {
            return None;
        }
        CompressedEdwardsY(*bytes).decompress().map(Self)
    }

    /// RFC 8032 5.1.2's encoding.
    pub(crate) fn to_bytes(self) -> [u8; 32] {
        self.0.compress().0
    }

    pub(crate) fn neg(&self) -> Self {
        Self(-self.0)
    }

    /// `8 * self`, which leaves only its component in the prime-order
    /// subgroup.
    pub(crate) fn mul_by_cofactor(&self) -> Self {
        Self(self.0.mul_by_cofactor())
    }

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

/// `y = 1`, little-endian.
const ONE: [u8; 32] = {
    let mut one = [0u8; 32];
    one[0] = 1;
    one
};

/// `y = p - 1 = 2^255 - 20`, little-endian.
const P_MINUS_ONE: [u8; 32] = {
    let mut p = [0xffu8; 32];
    p[0] = 0xec;
    p[31] = 0x7f;
    p
};

/// Whether the little-endian `y` is below `p = 2^255 - 19`.
fn is_below_p(y: &[u8; 32]) -> bool {
    y.iter().rev().cmp(P_MINUS_ONE.iter().rev()).is_le()
}

/// An integer modulo the prime order `L` of edwards25519's base point,
/// reduced.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Scalar(pub(crate) curve25519_dalek::Scalar);

impl Scalar {
    /// Reads a little-endian scalar, or `None` unless it is below `L`.
    ///
    /// Whether it is below `L` is public; the value stays secret.
    pub(crate) fn from_canonical_bytes(bytes: &[u8; 32]) -> Option<Self> {
        let s = curve25519_dalek::Scalar::from_canonical_bytes(*bytes);
        // dalek's `CtOption::is_some` is a `Choice`. Declassify it before
        // converting to `bool`.
        let canonical = bool::from(low::ct::into_public(s.is_some()));
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
    // Only tests multiply scalars alone until FROST does.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn mul(&self, other: &Self) -> Self {
        Self(self.0 * other.0)
    }

    /// `self * other + addend mod L`.
    pub(crate) fn mul_add(&self, other: &Self, addend: &Self) -> Self {
        Self(self.0 * other.0 + addend.0)
    }

    /// `1 / self mod L`, or `None` for zero, which has no inverse.
    ///
    /// Whether `self` is zero is public; the value stays secret.
    pub(crate) fn invert(&self) -> Option<Self> {
        // dalek 5.0.0's `==` is `ct_eq().into()`. Declassify the choice before
        // that conversion.
        let equal = self.0.ct_eq(&curve25519_dalek::Scalar::ZERO);
        let zero = bool::from(low::ct::into_public(equal));
        (!zero).then(|| Self(self.0.invert()))
    }

    /// `-self mod L`.
    pub(crate) fn neg(&self) -> Self {
        Self(-self.0)
    }

    /// Whether this is zero. The bit is public.
    ///
    /// dalek 5.0.0's `==` is `ct_eq().into()`, which converts the `Choice`
    /// to `bool` inside the comparison. Declassify the choice first, as
    /// `invert` does, so the conversion runs on a public bit.
    pub(crate) fn is_zero(&self) -> bool {
        let equal = self.0.ct_eq(&curve25519_dalek::Scalar::ZERO);
        bool::from(low::ct::into_public(equal))
    }

    /// A uniformly random nonzero scalar: 64 bytes from the system's random
    /// source, reduced modulo `L`.
    pub(crate) fn random() -> Result<Self, Error> {
        let _entry = low::Entry::new_secret();
        // Zero has a chance of 2^-252 a draw, so only a broken source fails.
        for _ in 0..64 {
            let mut bytes = [0u8; 64];
            SystemRandom.fill(&mut bytes)?;
            low::ct::secret_slice(&bytes);
            let scalar = Self::from_uniform_bytes(&bytes);
            if !low::ct::into_public(scalar.is_zero()) {
                return Ok(scalar);
            }
        }
        Err(Error::RngFailed)
    }
}
