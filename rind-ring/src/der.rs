//! The little DER that ring's API needs rind-ring to read itself: an RSA
//! public key's fields, an ECDSA PKCS#8 document's public key, and an
//! Ed25519 PKCS#8 document's structure, whose secret seed it slices out but
//! never branches on.

use crate::error::{self, KeyRejected};

const INTEGER: u8 = 0x02;
const SEQUENCE: u8 = 0x30;

/// Reads a DER element tagged `tag` and returns its contents, refusing a
/// length that is not minimally encoded or takes over two bytes.
fn read<'a>(
    input: &mut untrusted::Reader<'a>,
    tag: u8,
) -> Result<untrusted::Input<'a>, error::Unspecified> {
    if input.read_byte()? != tag {
        return Err(error::Unspecified);
    }
    let len = match input.read_byte()? {
        len @ 0..=0x7f => usize::from(len),
        0x81 => match input.read_byte()? {
            len @ 0x80..=0xff => usize::from(len),
            _ => return Err(error::Unspecified),
        },
        0x82 => {
            let high = input.read_byte()?;
            let low = input.read_byte()?;
            match u16::from_be_bytes([high, low]) {
                len @ 0x100..=0xffff => usize::from(len),
                _ => return Err(error::Unspecified),
            }
        }
        _ => return Err(error::Unspecified),
    };
    Ok(input.read_bytes(len)?)
}

/// Reads a positive INTEGER and returns its magnitude, without the zero byte DER
/// adds when its top bit is set.
fn positive_integer<'a>(input: &mut untrusted::Reader<'a>) -> Result<&'a [u8], error::Unspecified> {
    let value = read(input, INTEGER)?.as_slice_less_safe();
    match value {
        [] | [0x80..=0xff, ..] => Err(error::Unspecified),
        [0, rest @ ..] => match rest {
            [0x80..=0xff, ..] => Ok(rest),
            _ => Err(error::Unspecified),
        },
        _ => Ok(value),
    }
}

/// Reads a PKCS#1 `RSAPublicKey`, returning the modulus and the exponent.
pub(crate) fn rsa_public_key(der: &[u8]) -> Result<(&[u8], &[u8]), error::Unspecified> {
    untrusted::Input::from(der).read_all(error::Unspecified, |input| {
        read(input, SEQUENCE)?.read_all(error::Unspecified, |input| {
            Ok((positive_integer(input)?, positive_integer(input)?))
        })
    })
}

/// The public key in an ECDSA PKCS#8 document's `ECPrivateKey`, if it has one.
///
/// rind has already checked the document; this only finds the field, and
/// skips the private key without reading it.
pub(crate) fn ecdsa_pkcs8_public_key(der: &[u8]) -> Option<&[u8]> {
    const OCTET_STRING: u8 = 0x04;
    const BIT_STRING: u8 = 0x03;
    const PARAMETERS: u8 = 0xa0;
    const PUBLIC_KEY: u8 = 0xa1;

    fn ec_private_key<'a>(
        input: &mut untrusted::Reader<'a>,
    ) -> Result<&'a [u8], error::Unspecified> {
        read(input, INTEGER)?;
        read(input, OCTET_STRING)?;
        if input.peek(PARAMETERS) {
            read(input, PARAMETERS)?;
        }
        let bits =
            read(input, PUBLIC_KEY)?.read_all(error::Unspecified, |bits| read(bits, BIT_STRING))?;
        match bits.as_slice_less_safe() {
            [0, public_key @ ..] => Ok(public_key),
            _ => Err(error::Unspecified),
        }
    }
    untrusted::Input::from(der)
        .read_all(error::Unspecified, |outer| {
            read(outer, SEQUENCE)?.read_all(error::Unspecified, |input| {
                read(input, INTEGER)?;
                read(input, SEQUENCE)?;
                let key = read(input, OCTET_STRING)?;
                input.skip_to_end();
                key.read_all(error::Unspecified, |key| {
                    read(key, SEQUENCE)?.read_all(error::Unspecified, ec_private_key)
                })
            })
        })
        .ok()
}

/// An Ed25519 PKCS#8 document's parts, as ring reads them.
pub(crate) struct Ed25519Pkcs8<'a> {
    /// The 32-byte seed, or another length the caller refuses.
    pub(crate) seed: &'a [u8],
    /// The public key, which only a v2 document carries.
    pub(crate) public_key: Option<&'a [u8]>,
}

/// Reads an Ed25519 PKCS#8 document as ring does, which rind's stricter
/// parser does not: a v2 public key may be tagged `[1] EXPLICIT`, as early
/// ring versions wrote it.
///
/// `v1` says whether a v1 document, which carries no public key, is taken.
/// The seed is only sliced out, never branched on.
pub(crate) fn ed25519_pkcs8(der: &[u8], v1: bool) -> Result<Ed25519Pkcs8<'_>, KeyRejected> {
    const ALGORITHM: &[u8] = &[0x06, 0x03, 0x2b, 0x65, 0x70];
    const OCTET_STRING: u8 = 0x04;
    const BIT_STRING: u8 = 0x03;
    const ATTRIBUTES: u8 = 0xa0;
    const PUBLIC_KEY: u8 = 0x81;
    const LEGACY_PUBLIC_KEY: u8 = 0xa1;

    let invalid = |_| KeyRejected::invalid_encoding();
    let mut outer = untrusted::Reader::new(untrusted::Input::from(der));
    let mut input = untrusted::Reader::new(read(&mut outer, SEQUENCE).map_err(invalid)?);
    if !outer.at_end() {
        return Err(KeyRejected::invalid_encoding());
    }

    let version = match read(&mut input, INTEGER)
        .map_err(invalid)?
        .as_slice_less_safe()
    {
        [version @ (0 | 1)] => *version,
        [2..=0x7f] => return Err(KeyRejected::version_not_supported()),
        _ => return Err(KeyRejected::invalid_encoding()),
    };
    if read(&mut input, SEQUENCE)
        .map_err(invalid)?
        .as_slice_less_safe()
        != ALGORITHM
    {
        return Err(KeyRejected::wrong_algorithm());
    }
    if version == 0 && !v1 {
        return Err(KeyRejected::version_not_supported());
    }

    let seed = read(&mut input, OCTET_STRING)
        .and_then(|key| key.read_all(error::Unspecified, |key| read(key, OCTET_STRING)))
        .map_err(invalid)?
        .as_slice_less_safe();

    if input.peek(ATTRIBUTES) {
        read(&mut input, ATTRIBUTES).map_err(invalid)?;
    }

    let public_key = match version {
        0 => None,
        _ if input.at_end() => return Err(KeyRejected::public_key_is_missing()),
        _ => {
            let bits = match input.peek(LEGACY_PUBLIC_KEY) {
                true => read(&mut input, LEGACY_PUBLIC_KEY).and_then(|bits| {
                    bits.read_all(error::Unspecified, |bits| read(bits, BIT_STRING))
                }),
                false => read(&mut input, PUBLIC_KEY),
            };
            match bits.map_err(invalid)?.as_slice_less_safe() {
                [0, public_key @ ..] => Some(public_key),
                _ => return Err(KeyRejected::invalid_encoding()),
            }
        }
    };
    if !input.at_end() {
        return Err(KeyRejected::invalid_encoding());
    }
    Ok(Ed25519Pkcs8 { seed, public_key })
}

#[cfg(test)]
mod tests {
    use super::{ed25519_pkcs8, rsa_public_key};

    #[test]
    fn positive_integer_refuses_a_negative_encoding() {
        // An INTEGER whose first byte has the high bit set is negative unless
        // a leading 0x00 precedes it. Deleting that arm accepts 0x80.
        let negative = tlv(0x02, &[0x80]);
        let exponent = tlv(0x02, &[0x01, 0x00, 0x01]);
        let refused = tlv(0x30, &[negative, exponent.clone()].concat());
        assert!(rsa_public_key(&refused).is_err());

        let non_negative = tlv(0x02, &[0x00, 0x80]);
        let accepted = tlv(0x30, &[non_negative, exponent].concat());
        assert!(rsa_public_key(&accepted).is_ok());
    }

    #[test]
    fn ed25519_pkcs8_refuses_the_versions_ring_refuses() {
        // Version 2 is in range but not a version ring reads. Deleting that
        // arm reports it as a bad encoding instead.
        let unsupported = ed25519_document(2, false);
        let Err(error) = ed25519_pkcs8(&unsupported, false) else {
            panic!("version 2 was accepted");
        };
        assert_eq!(error.to_string(), "VersionNotSupported");

        // PKCS#8 v2 is version integer 1. Ending before the public key is
        // `PublicKeyIsMissing`, which the `at_end` guard names. Replacing that
        // guard with `false` parses on and reports a bad encoding.
        let missing = ed25519_document(1, false);
        let Err(error) = ed25519_pkcs8(&missing, false) else {
            panic!("a v2 document without a public key was accepted");
        };
        assert_eq!(error.to_string(), "PublicKeyIsMissing");

        // Replacing the guard with `true` reports every v2 document as missing
        // its public key, including one that has the key ring reads.
        let present = ed25519_document(1, true);
        let key = ed25519_pkcs8(&present, false).expect("a v2 document with its public key");
        assert_eq!(key.seed, &[0x11; 32]);
        assert_eq!(key.public_key, Some(&[0x22; 32][..]));
    }

    fn ed25519_document(version: u8, with_public_key: bool) -> Vec<u8> {
        let oid = tlv(0x06, &[0x2b, 0x65, 0x70]);
        let algorithm = tlv(0x30, &oid);
        let seed = tlv(0x04, &tlv(0x04, &[0x11; 32]));
        let mut body = [tlv(0x02, &[version]), algorithm, seed].concat();
        if with_public_key {
            // [1] IMPLICIT OCTET STRING: a leading 0x00, then the 32-byte key.
            let mut public = vec![0x00];
            public.extend_from_slice(&[0x22; 32]);
            body.extend(tlv(0x81, &public));
        }
        tlv(0x30, &body)
    }

    fn tlv(tag: u8, body: &[u8]) -> Vec<u8> {
        assert!(body.len() < 128);
        let mut out = vec![tag, body.len() as u8];
        out.extend_from_slice(body);
        out
    }
}
