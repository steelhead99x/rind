// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! FROST(Ed25519, SHA-512), RFC 9591 section 6.1.
//!
//! On x86_64 and aarch64 the group is s2n-bignum's edwards25519. On armv7
//! and the portable backend it is curve25519-dalek's, behind the same module
//! name.

use super::protocol::Group;
use crate::error::{Error, KeyFormatError};
use crate::low::ct;
use crate::mid::edwards25519::{Point, Scalar};
use crate::mid::rng::RandomSource;
use crate::mid::sha2::Sha512Context;

pub(super) struct Ed25519;

impl Group for Ed25519 {
    const CONTEXT: &'static [u8] = b"FROST-ED25519-SHA512-v1";
    const ELEMENT_LEN: usize = 32;
    const HASH_LEN: usize = 64;
    /// Scalars are little-endian, so integer order is not byte order.
    const SCALAR_BE: bool = false;

    type Scalar = Scalar;
    type Element = Point;

    fn scalar_from_canonical(bytes: &[u8; 32]) -> Option<Self::Scalar> {
        Scalar::from_canonical_bytes(bytes)
    }

    fn scalar_to_bytes(scalar: &Self::Scalar) -> [u8; 32] {
        scalar.to_bytes()
    }

    fn scalar_from_u64(value: u64) -> Self::Scalar {
        Scalar::from_u64(value)
    }

    fn scalar_add(a: &Self::Scalar, b: &Self::Scalar) -> Self::Scalar {
        a.add(b)
    }

    fn scalar_sub(a: &Self::Scalar, b: &Self::Scalar) -> Self::Scalar {
        a.sub(b)
    }

    fn scalar_mul(a: &Self::Scalar, b: &Self::Scalar) -> Self::Scalar {
        a.mul(b)
    }

    fn scalar_invert(scalar: &Self::Scalar) -> Option<Self::Scalar> {
        scalar.invert()
    }

    fn scalar_is_zero(scalar: &Self::Scalar) -> bool {
        // Zero is public: a rejected share or nonce says nothing of the one kept.
        ct::into_public(scalar.is_zero())
    }

    fn random_scalar(rng: &mut dyn RandomSource) -> Result<Self::Scalar, Error> {
        // RFC 9591 appendix D.2. Sixty-four bytes is more than the 48 it
        // requires, and `from_uniform_bytes` reduces them modulo L.
        for _ in 0..64 {
            let mut wide = [0u8; 64];
            rng.fill(&mut wide)?;
            ct::secret_slice(&wide);
            let scalar = Scalar::from_uniform_bytes(&wide);
            // Zero is public and discarded. It says nothing of the next draw.
            if !ct::into_public(scalar.is_zero()) {
                return Ok(scalar);
            }
        }
        Err(Error::RngFailed)
    }

    fn base(scalar: &Self::Scalar) -> Option<Self::Element> {
        if ct::into_public(scalar.is_zero()) {
            None
        } else {
            Some(Point::mul_base(scalar))
        }
    }

    fn mul(point: &Self::Element, scalar: &Self::Scalar) -> Option<Self::Element> {
        if ct::into_public(scalar.is_zero()) {
            None
        } else {
            Some(point.mul(scalar))
        }
    }

    fn add(a: &Self::Element, b: &Self::Element) -> Option<Self::Element> {
        let sum = a.add(b);
        if sum.is_identity() { None } else { Some(sum) }
    }

    fn equals(a: &Self::Element, b: &Self::Element) -> bool {
        a.to_edwards_bytes() == b.to_edwards_bytes()
    }

    fn serialize(point: &Self::Element) -> Result<[u8; 33], Error> {
        if point.is_identity() {
            return Err(KeyFormatError::SmallOrder.into());
        }
        let mut out = [0u8; 33];
        out[..32].copy_from_slice(&point.to_edwards_bytes());
        Ok(out)
    }

    fn deserialize(bytes: &[u8]) -> Result<Self::Element, Error> {
        let bytes: &[u8; 32] = bytes.try_into().map_err(|_| KeyFormatError::WrongLength)?;
        let point = Point::from_edwards_bytes(bytes).ok_or(KeyFormatError::NotOnCurve)?;
        if point.is_identity() || !point.is_torsion_free() {
            return Err(KeyFormatError::SmallOrder.into());
        }
        Ok(point)
    }

    fn h1(msg: &[u8]) -> Result<Self::Scalar, Error> {
        Ok(Scalar::from_uniform_bytes(&sha512(&[
            Self::CONTEXT,
            b"rho",
            msg,
        ])))
    }

    fn h2(msg: &[u8]) -> Result<Self::Scalar, Error> {
        // No domain separator: RFC 8032's challenge is SHA-512(R || PK || M).
        Ok(Scalar::from_uniform_bytes(&sha512(&[msg])))
    }

    fn h3(msg: &[u8]) -> Result<Self::Scalar, Error> {
        Ok(Scalar::from_uniform_bytes(&sha512(&[
            Self::CONTEXT,
            b"nonce",
            msg,
        ])))
    }

    fn h4(msg: &[u8]) -> [u8; 64] {
        sha512(&[Self::CONTEXT, b"msg", msg])
    }

    fn h5(msg: &[u8]) -> [u8; 64] {
        sha512(&[Self::CONTEXT, b"com", msg])
    }
}

fn sha512(parts: &[&[u8]]) -> [u8; 64] {
    let mut hash = Sha512Context::new();
    for part in parts {
        hash.update(part);
    }
    hash.finish()
}
