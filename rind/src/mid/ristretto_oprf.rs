// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! ristretto255 group operations for RFC 9497.
//!
//! The group is the crate-internal ristretto255. Edwards addition is complete,
//! so the batch proof's sums need no separate formula.

use super::hash_to_curve::expand_message_xmd;
use super::ristretto255::{Element, Scalar};
use super::sha2::Sha512Context;
use super::util;
use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::mid::rng::RandomSource;

pub(crate) const ELEMENT: usize = 32;
pub(crate) const SCALAR: usize = 32;

/// `scalar * HashToGroup(msg)`, multiplying the mapped element directly.
///
/// The product's encoding is what the client sends.
pub(crate) fn mul_hash(msg: &[u8], dst: &[u8], scalar: &[u8]) -> Result<[u8; ELEMENT], Error> {
    let scalar = scalar_words(scalar)?;
    if low::ct::into_public(is_zero(&scalar)) {
        return Err(KeyFormatError::ScalarOutOfRange.into());
    }
    let mut uniform = [0u8; 64];
    expand_message_xmd::<Sha512Context>(msg, dst, &mut uniform)?;
    encode(Element::from_uniform_bytes(&uniform).mul(&scalar))
}

pub(crate) fn hash_to_scalar(msg: &[u8], dst: &[u8]) -> Result<[u8; SCALAR], Error> {
    let mut uniform = [0u8; 64];
    expand_message_xmd::<Sha512Context>(msg, dst, &mut uniform)?;
    // RFC 9497: 64 little-endian bytes, reduced modulo the group order.
    // Zero is a valid scalar here; DeriveKeyPair retries it.
    Ok(Scalar::from_uniform_bytes(&uniform).to_bytes())
}

pub(crate) fn random_scalar(rng: &mut dyn RandomSource) -> Result<[u8; SCALAR], Error> {
    // L is just above 2^252, so about 1 in 16 candidates is in range. The cap
    // makes exhaustion negligible.
    for _ in 0..8192 {
        let mut bytes = [0u8; SCALAR];
        rng.fill(&mut bytes)?;
        low::ct::secret_slice(&bytes);
        if let Ok(scalar) = scalar_nonzero(&bytes) {
            return Ok(scalar);
        }
    }
    Err(Error::RngFailed)
}

pub(crate) fn scalar_nonzero(bytes: &[u8]) -> Result<[u8; SCALAR], Error> {
    let scalar = scalar_words(bytes)?;
    match low::ct::into_public(is_zero(&scalar)) {
        true => Err(KeyFormatError::ScalarOutOfRange.into()),
        false => Ok(scalar.to_bytes()),
    }
}

pub(crate) fn scalar_any(bytes: &[u8]) -> Result<[u8; SCALAR], Error> {
    Ok(scalar_words(bytes)?.to_bytes())
}

pub(crate) fn scalar_is_zero(bytes: &[u8]) -> bool {
    match scalar_words(bytes) {
        Ok(scalar) => low::ct::into_public(is_zero(&scalar)),
        Err(_) => false,
    }
}

pub(crate) fn generator() -> [u8; ELEMENT] {
    let mut one = [0u8; SCALAR];
    one[0] = 1;
    base_mul(&one).expect("1 is a scalar")
}

pub(crate) fn base_mul(scalar: &[u8]) -> Result<[u8; ELEMENT], Error> {
    let scalar = scalar_words(scalar)?;
    if low::ct::into_public(is_zero(&scalar)) {
        return Err(KeyFormatError::ScalarOutOfRange.into());
    }
    encode(Element::mul_base(&scalar))
}

pub(crate) fn mul(element: &[u8], scalar: &[u8]) -> Result<[u8; ELEMENT], Error> {
    let scalar = scalar_words(scalar)?;
    if low::ct::into_public(is_zero(&scalar)) {
        return Err(KeyFormatError::ScalarOutOfRange.into());
    }
    encode(decode(element)?.mul(&scalar))
}

pub(crate) fn invert(scalar: &[u8]) -> Result<[u8; SCALAR], Error> {
    let scalar = scalar_words(scalar)?;
    scalar
        .invert()
        .map(|inv| inv.to_bytes())
        .ok_or_else(|| KeyFormatError::ScalarOutOfRange.into())
}

pub(crate) fn mul_scalars(a: &[u8], b: &[u8]) -> Result<[u8; SCALAR], Error> {
    Ok(scalar_words(a)?.mul(&scalar_words(b)?).to_bytes())
}

pub(crate) fn sub_scalars(a: &[u8], b: &[u8]) -> Result<[u8; SCALAR], Error> {
    Ok(scalar_words(a)?.sub(&scalar_words(b)?).to_bytes())
}

pub(crate) fn sum_scaled(points: &[&[u8]], scalars: &[&[u8]]) -> Result<[u8; ELEMENT], Error> {
    if points.len() != scalars.len() {
        return Err(Error::WrongLength);
    }
    let mut acc = Element::mul_base(&scalar_words(&[0; SCALAR])?);
    for (point, scalar) in points.iter().zip(scalars) {
        acc = acc.add(&decode(point)?.mul(&scalar_words(scalar)?));
    }
    encode(acc)
}

fn scalar_words(bytes: &[u8]) -> Result<Scalar, Error> {
    let bytes: &[u8; SCALAR] = bytes.try_into().map_err(|_| Error::WrongLength)?;
    Scalar::from_canonical_bytes(bytes).ok_or_else(|| KeyFormatError::ScalarOutOfRange.into())
}

fn is_zero(scalar: &Scalar) -> bool {
    low::bignum_eq(&util::little_endian_to_u64x4(&scalar.to_bytes()), &[0; 4])
}

fn decode(bytes: &[u8]) -> Result<Element, Error> {
    let bytes: &[u8; ELEMENT] = bytes.try_into().map_err(|_| Error::WrongLength)?;
    let element = Element::from_bytes(bytes).ok_or(KeyFormatError::PointEncoding)?;
    match is_identity(&element.to_bytes()) {
        true => Err(KeyFormatError::SmallOrder.into()),
        false => Ok(element),
    }
}

fn encode(element: Element) -> Result<[u8; ELEMENT], Error> {
    let bytes = element.to_bytes();
    match is_identity(&bytes) {
        true => Err(KeyFormatError::SmallOrder.into()),
        false => Ok(bytes),
    }
}

fn is_identity(bytes: &[u8; ELEMENT]) -> bool {
    low::ct::into_public(low::bignum_eq(
        &util::little_endian_to_u64x4(bytes),
        &[0; 4],
    ))
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;

    fn le(first: u8) -> [u8; SCALAR] {
        let mut bytes = [0u8; SCALAR];
        bytes[0] = first;
        bytes
    }

    #[test]
    fn addition_matches_the_generator_multiples() {
        let _entry = low::Entry::new_secret();
        let one = le(1);
        let two = le(2);
        let g = generator();
        let double = base_mul(&two).unwrap();
        assert_eq!(sum_scaled(&[&g, &g], &[&one, &one]).unwrap(), double);
        assert_eq!(sum_scaled(&[&g, &g], &[&[0; SCALAR], &one]).unwrap(), g);
    }
}
