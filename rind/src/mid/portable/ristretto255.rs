// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ristretto255 (RFC 9496) over curve25519-dalek's, whose operations run in
//! constant time.

// ristretto255's consumers (OPRF, FROST, ECVRF, OPAQUE) are their own quests.
#![cfg_attr(not(test), allow(dead_code))]

use curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};

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

    /// `1 / self mod L`, or `None` for zero, which has no inverse.
    ///
    /// Whether `self` is zero is public; the value stays secret.
    pub(crate) fn invert(&self) -> Option<Self> {
        let zero = low::ct::into_public(self.0 == curve25519_dalek::Scalar::ZERO);
        (!zero).then(|| Self(self.0.invert()))
    }
}

/// A ristretto255 element.
#[derive(Clone, Copy, Debug)]
pub(crate) struct Element(RistrettoPoint);

impl Element {
    /// `[scalar]G`, for the generator `G`.
    pub(crate) fn mul_base(scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self(RISTRETTO_BASEPOINT_TABLE * &scalar.0)
    }

    /// RFC 9496 4.3.1's decoding, or `None` for an encoding it rejects.
    ///
    /// dalek branches on whether the encoding is canonical and non-negative,
    /// and then on whether it decodes, so only a public encoding is in
    /// constant time; every encoding rind decodes is a peer's.
    pub(crate) fn from_bytes(bytes: &[u8; 32]) -> Option<Self> {
        low::Entry::assert_held();
        CompressedRistretto(*bytes).decompress().map(Self)
    }

    /// RFC 9496 4.3.2's encoding.
    pub(crate) fn to_bytes(self) -> [u8; 32] {
        low::Entry::assert_held();
        self.0.compress().to_bytes()
    }

    /// RFC 9496 4.3.4's one-way map from 64 uniformly random bytes.
    pub(crate) fn from_uniform_bytes(bytes: &[u8; 64]) -> Self {
        low::Entry::assert_held();
        Self(RistrettoPoint::from_uniform_bytes(bytes))
    }

    pub(crate) fn add(&self, other: &Self) -> Self {
        Self(self.0 + other.0)
    }

    /// `[scalar]self`, in constant time.
    pub(crate) fn mul(&self, scalar: &Scalar) -> Self {
        low::Entry::assert_held();
        Self(self.0 * scalar.0)
    }
}
