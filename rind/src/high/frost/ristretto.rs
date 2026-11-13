// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! FROST(ristretto255, SHA-512), RFC 9591 section 6.2.
//!
//! Scalars are edwards25519's. Elements are the crate-internal ristretto255.

use super::protocol::Group;
use crate::error::{Error, KeyFormatError};
use crate::low::ct;
use crate::mid::ristretto255::{Element, Scalar};
use crate::mid::rng::RandomSource;
use crate::mid::sha2::Sha512Context;

pub(super) struct Ristretto;

impl Group for Ristretto {
    const CONTEXT: &'static [u8] = b"FROST-RISTRETTO255-SHA512-v1";
    const ELEMENT_LEN: usize = 32;
    const HASH_LEN: usize = 64;
    const SCALAR_BE: bool = false;

    type Scalar = Scalar;
    type Element = Element;

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
            Some(Element::mul_base(scalar))
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
        a.equals(b)
    }

    fn serialize(point: &Self::Element) -> Result<[u8; 33], Error> {
        if point.is_identity() {
            return Err(KeyFormatError::SmallOrder.into());
        }
        let mut out = [0u8; 33];
        out[..32].copy_from_slice(&point.to_bytes());
        Ok(out)
    }

    fn deserialize(bytes: &[u8]) -> Result<Self::Element, Error> {
        let bytes: &[u8; 32] = bytes.try_into().map_err(|_| KeyFormatError::WrongLength)?;
        let point = Element::from_bytes(bytes).ok_or(KeyFormatError::NotOnCurve)?;
        if point.is_identity() {
            return Err(KeyFormatError::SmallOrder.into());
        }
        Ok(point)
    }

    fn h1(msg: &[u8]) -> Result<Self::Scalar, Error> {
        // RFC 9496 section 4.4 maps 64 uniform bytes to a scalar by reducing
        // them modulo L, which is what H1, H2, and H3 specify.
        Ok(Scalar::from_uniform_bytes(&sha512(&[
            Self::CONTEXT,
            b"rho",
            msg,
        ])))
    }

    fn h2(msg: &[u8]) -> Result<Self::Scalar, Error> {
        Ok(Scalar::from_uniform_bytes(&sha512(&[
            Self::CONTEXT,
            b"chal",
            msg,
        ])))
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
