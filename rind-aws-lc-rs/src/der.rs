//! The little DER that aws-lc-rs's API needs rind-aws-lc-rs to read itself:
//! a PKCS#1 RSA public key's fields, which rind keeps to itself, and the
//! algorithm a PKCS#8 document names. rind parses and encodes the keys; every
//! byte read here is public.

use crate::error::{Unspecified, unspecified};

const INTEGER: u8 = 0x02;
const OBJECT_IDENTIFIER: u8 = 0x06;
const SEQUENCE: u8 = 0x30;

/// Reads a DER element tagged `tag` and returns its contents, refusing a
/// length that is not minimally encoded or takes over two bytes.
fn read<'a>(
    input: &mut untrusted::Reader<'a>,
    tag: u8,
) -> Result<untrusted::Input<'a>, Unspecified> {
    if input.read_byte().map_err(unspecified)? != tag {
        return Err(Unspecified);
    }
    let len = match input.read_byte().map_err(unspecified)? {
        len @ 0..=0x7f => usize::from(len),
        0x81 => match input.read_byte().map_err(unspecified)? {
            len @ 0x80..=0xff => usize::from(len),
            _ => return Err(Unspecified),
        },
        0x82 => {
            let high = input.read_byte().map_err(unspecified)?;
            let low = input.read_byte().map_err(unspecified)?;
            match u16::from_be_bytes([high, low]) {
                len @ 0x100..=0xffff => usize::from(len),
                _ => return Err(Unspecified),
            }
        }
        _ => return Err(Unspecified),
    };
    input.read_bytes(len).map_err(unspecified)
}

/// Reads a positive INTEGER and returns its magnitude, without the zero byte
/// DER adds when its top bit is set.
fn positive_integer<'a>(input: &mut untrusted::Reader<'a>) -> Result<&'a [u8], Unspecified> {
    let value = read(input, INTEGER)?.as_slice_less_safe();
    match value {
        [] | [0x80..=0xff, ..] => Err(Unspecified),
        [0, rest @ ..] => match rest {
            [0x80..=0xff, ..] => Ok(rest),
            _ => Err(Unspecified),
        },
        _ => Ok(value),
    }
}

/// Reads a PKCS#1 `RSAPublicKey`, returning the modulus and the exponent.
pub(crate) fn rsa_public_key(der: &[u8]) -> Result<(&[u8], &[u8]), Unspecified> {
    untrusted::Input::from(der).read_all(Unspecified, |input| {
        read(input, SEQUENCE)?.read_all(Unspecified, |input| {
            Ok((positive_integer(input)?, positive_integer(input)?))
        })
    })
}

/// The contents of the object identifier in a PKCS#8 document's
/// `privateKeyAlgorithm`, or `None` if its header does not parse. Only the
/// version and the algorithm identifier are read, never the private key.
pub(crate) fn pkcs8_algorithm(der: &[u8]) -> Option<&[u8]> {
    let mut outer = untrusted::Reader::new(untrusted::Input::from(der));
    let body = read(&mut outer, SEQUENCE).ok()?;
    let mut body = untrusted::Reader::new(body);
    read(&mut body, INTEGER).ok()?;
    let mut algorithm = untrusted::Reader::new(read(&mut body, SEQUENCE).ok()?);
    let oid = read(&mut algorithm, OBJECT_IDENTIFIER).ok()?;
    Some(oid.as_slice_less_safe())
}

/// A PKCS#8 document's algorithm parameters and private key, the parts a
/// non-ML-DSA decoder inspects. `parameters` is empty when the algorithm
/// identifier has none. Bytes after the outer sequence are ignored, as
/// `EVP_parse_private_key` reads one value.
pub(crate) struct Pkcs8Parts<'a> {
    pub parameters: &'a [u8],
    pub private_key: &'a [u8],
}

/// Splits a v1 or v2 PKCS#8 document. The version must be 0 or 1. An
/// attributes set and a public key, in that order, may follow the private key.
pub(crate) fn pkcs8_parts(der: &[u8]) -> Option<Pkcs8Parts<'_>> {
    let mut outer = untrusted::Reader::new(untrusted::Input::from(der));
    let body = read(&mut outer, SEQUENCE).ok()?;
    let mut body = untrusted::Reader::new(body);
    let version = read(&mut body, INTEGER).ok()?;
    if !matches!(version.as_slice_less_safe(), [0] | [1]) {
        return None;
    }
    let mut algorithm = untrusted::Reader::new(read(&mut body, SEQUENCE).ok()?);
    read(&mut algorithm, OBJECT_IDENTIFIER).ok()?;
    let parameters = algorithm.read_bytes_to_end().as_slice_less_safe();
    let private_key = read(&mut body, 0x04).ok()?.as_slice_less_safe();
    if body.peek(0xa0) {
        read(&mut body, 0xa0).ok()?;
    }
    if body.peek(0x81) {
        read(&mut body, 0x81).ok()?;
    }
    if !body.at_end() {
        return None;
    }
    Some(Pkcs8Parts {
        parameters,
        private_key,
    })
}

/// The tag and body of the first DER element in `der`. Bytes after it are
/// left unread.
pub(crate) fn first_element(der: &[u8]) -> Option<(u8, &[u8])> {
    let tag = *der.first()?;
    let mut input = untrusted::Reader::new(untrusted::Input::from(der));
    let body = read(&mut input, tag).ok()?;
    Some((tag, body.as_slice_less_safe()))
}

/// Whether `der` is a `SubjectPublicKeyInfo` rather than PKCS#1: its first
/// field is a `SEQUENCE`, where PKCS#1's is an `INTEGER`.
pub(crate) fn is_spki(der: &[u8]) -> bool {
    let mut input = untrusted::Reader::new(untrusted::Input::from(der));
    read(&mut input, SEQUENCE)
        .map(|body| body.as_slice_less_safe().first() == Some(&SEQUENCE))
        .unwrap_or(false)
}

/// The bit length of a big-endian magnitude without leading zero bytes.
pub(crate) fn bits(magnitude: &[u8]) -> usize {
    8 * magnitude.len()
        - magnitude
            .first()
            .map_or(8, |top| top.leading_zeros() as usize)
}
