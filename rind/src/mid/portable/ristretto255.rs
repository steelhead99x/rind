// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ristretto255 (RFC 9496) over curve25519-dalek's, whose operations run in
//! constant time.

// FROST, ECVRF, and OPAQUE are their own quests. The OPRF is the caller.

use curve25519_dalek::constants::RISTRETTO_BASEPOINT_TABLE;
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};

use crate::low;
pub(crate) use crate::mid::edwards25519::Scalar;

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
