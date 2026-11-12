// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! FROST(P-256, SHA-256), RFC 9591 section 6.4.
//!
//! The hashes to scalars are `mid::p256::hash_to_curve::hash_to_scalar`,
//! RFC 9380's `hash_to_field`. The group is rind's P-256, s2n-bignum on
//! x86_64 and aarch64 and fiat-crypto on armv7 and the portable backend.

use crate::error::Error;
use crate::low::ct;
use crate::mid::p256::hash_to_curve::hash_to_scalar;
use crate::mid::p256::{PublicKey, Scalar};
use crate::mid::rng::RandomSource;
use crate::mid::sha2::Sha256Context;

use super::protocol::Group;

pub(super) struct P256;

impl Group for P256 {
    const CONTEXT: &'static [u8] = b"FROST-P256-SHA256-v1";
    const ELEMENT_LEN: usize = 33;
    const HASH_LEN: usize = 32;
    const SCALAR_BE: bool = true;

    type Scalar = Scalar;
    type Element = PublicKey;

    fn scalar_from_canonical(bytes: &[u8; 32]) -> Option<Self::Scalar> {
        Scalar::from_bytes_canonical(bytes).ok()
    }

    fn scalar_to_bytes(scalar: &Self::Scalar) -> [u8; 32] {
        scalar.as_bytes()
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
        ct::into_public(scalar.is_zero())
    }

    fn random_scalar(rng: &mut dyn RandomSource) -> Result<Self::Scalar, Error> {
        // RFC 9591 appendix D.2: 48 bytes is `ceil((3 * 256 / 2) / 8)`.
        for _ in 0..64 {
            let mut wide = [0u8; 48];
            rng.fill(&mut wide)?;
            ct::secret_slice(&wide);
            let scalar = Scalar::from_be_wide_48(&wide);
            if !Self::scalar_is_zero(&scalar) {
                return Ok(scalar);
            }
        }
        Err(Error::RngFailed)
    }

    fn base(scalar: &Self::Scalar) -> Option<Self::Element> {
        if Self::scalar_is_zero(scalar) {
            None
        } else {
            Some(PublicKey::mul_base(scalar))
        }
    }

    fn mul(point: &Self::Element, scalar: &Self::Scalar) -> Option<Self::Element> {
        if Self::scalar_is_zero(scalar) {
            None
        } else {
            Some(point.mul(scalar))
        }
    }

    fn add(a: &Self::Element, b: &Self::Element) -> Option<Self::Element> {
        a.add(b)
    }

    fn equals(a: &Self::Element, b: &Self::Element) -> bool {
        a.equals(b)
    }

    fn serialize(point: &Self::Element) -> Result<[u8; 33], Error> {
        Ok(point.to_compressed())
    }

    fn deserialize(bytes: &[u8]) -> Result<Self::Element, Error> {
        PublicKey::from_compressed(bytes)
    }

    fn h1(msg: &[u8]) -> Result<Self::Scalar, Error> {
        hash_to_scalar(msg, &dst(b"rho"))
    }

    fn h2(msg: &[u8]) -> Result<Self::Scalar, Error> {
        hash_to_scalar(msg, &dst(b"chal"))
    }

    fn h3(msg: &[u8]) -> Result<Self::Scalar, Error> {
        hash_to_scalar(msg, &dst(b"nonce"))
    }

    fn h4(msg: &[u8]) -> [u8; 64] {
        let mut out = [0u8; 64];
        out[..32].copy_from_slice(&sha256(&[Self::CONTEXT, b"msg", msg]));
        out
    }

    fn h5(msg: &[u8]) -> [u8; 64] {
        let mut out = [0u8; 64];
        out[..32].copy_from_slice(&sha256(&[Self::CONTEXT, b"com", msg]));
        out
    }
}

/// `contextString || label`, the DST RFC 9591 gives `hash_to_field`.
fn dst(label: &[u8]) -> Vec<u8> {
    let mut out = Vec::with_capacity(P256::CONTEXT.len() + label.len());
    out.extend_from_slice(P256::CONTEXT);
    out.extend_from_slice(label);
    out
}

fn sha256(parts: &[&[u8]]) -> [u8; 32] {
    let mut hash = Sha256Context::new();
    for part in parts {
        hash.update(part);
    }
    hash.finish()
}
