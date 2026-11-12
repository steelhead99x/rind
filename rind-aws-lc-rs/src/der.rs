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
    pkcs8_algorithm_identifier(der).map(|(oid, _)| oid)
}

/// The object identifier's contents in a PKCS#8 document's
/// `privateKeyAlgorithm`, and the encoded parameters after it (empty when
/// there are none), as [`pkcs8_algorithm`] reads them.
pub(crate) fn pkcs8_algorithm_identifier(der: &[u8]) -> Option<(&[u8], &[u8])> {
    let mut outer = untrusted::Reader::new(untrusted::Input::from(der));
    let body = read(&mut outer, SEQUENCE).ok()?;
    let mut body = untrusted::Reader::new(body);
    read(&mut body, INTEGER).ok()?;
    let mut algorithm = untrusted::Reader::new(read(&mut body, SEQUENCE).ok()?);
    let oid = read(&mut algorithm, OBJECT_IDENTIFIER).ok()?;
    let parameters = algorithm.read_bytes_to_end();
    Some((oid.as_slice_less_safe(), parameters.as_slice_less_safe()))
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
