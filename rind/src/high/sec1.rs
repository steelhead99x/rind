// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! A NIST curve private key's encodings, SEC1's (RFC 5915) `ECPrivateKey`
//! alone or in PKCS#8, which ECDSA and ECDH keys share.

use super::asn1::{self, Type};
use super::curve::{MAX_SCALAR_LEN, MAX_UNCOMPRESSED_PUBLIC_KEY_LEN};
use super::pkcs8;
use crate::error::{Error, KeyFormatError};
use crate::low::ct;

/// The longest `ECPrivateKey`: P-521's scalar and uncompressed point, and
/// its curve.
pub(crate) const MAX_LEN: usize = MAX_SCALAR_LEN + MAX_UNCOMPRESSED_PUBLIC_KEY_LEN + 128;

/// Decompresses an X9.62 compressed point on one curve to its uncompressed
/// encoding, written to the start of the output.
pub(crate) type Decompress = for<'a> fn(&[u8], &'a mut [u8]) -> Result<&'a [u8], Error>;

/// `encoded`, an X9.62 point, as its uncompressed encoding: itself, for the
/// curve's parser to check, or the compressed point `decompress` checks and
/// decompresses into `output`. A hybrid point is refused, as BoringSSL does.
pub(crate) fn uncompressed<'a>(
    encoded: &'a [u8],
    decompress: Decompress,
    output: &'a mut [u8],
) -> Result<&'a [u8], Error> {
    match encoded.first() {
        Some(0x04) => Ok(encoded),
        Some(0x02 | 0x03) => decompress(encoded, output),
        Some(_) => Err(KeyFormatError::PointEncoding.into()),
        None => Err(KeyFormatError::WrongLength.into()),
    }
}

/// A decoded `ECPrivateKey`: its scalar's bytes, and the public key it
/// carries, if any.
pub(crate) struct Decoded<'a> {
    pub(crate) private_key: &'a [u8],
    pub(crate) public_key: Option<&'a [u8]>,
}

/// Decodes an `ECPrivateKey`, refused if it names a curve other than `curve`.
pub(crate) fn decode<'a>(der: &'a [u8], curve: &asn1::ObjectId) -> Result<Decoded<'a>, Error> {
    let ecpk = asn1::pkix::EcPrivateKey::from_bytes(der).map_err(KeyFormatError::Asn1)?;

    // nb. ecpk.version has one variant, so if it decoded property it is guaranteed
    // to be EcPrivateKeyVer::ecPrivkeyVer1

    match ecpk.parameters.inner() {
        Some(x) if x == curve => {}
        None => {}
        _ => return Err(KeyFormatError::MismatchedSec1Curve.into()),
    }

    Ok(Decoded {
        private_key: ecpk.privateKey.as_octets(),
        public_key: ecpk.publicKey.inner().as_ref().map(|x| x.as_octets()),
    })
}

/// Decodes a PKCS#8 `ECPrivateKey` on `curve`.
///
/// A v2 document is taken only when it omits the PKCS#8 public key, which
/// this does not check. The public key inside the `ECPrivateKey` still is.
pub(crate) fn decode_pkcs8<'a>(
    der: &'a [u8],
    curve: &asn1::ObjectId,
) -> Result<Decoded<'a>, Error> {
    let key = pkcs8::Key::decode(
        der,
        &[&asn1::oid::id_ecPublicKey],
        Some(asn1::Any::ObjectId(curve.clone())),
    )?;
    decode(key.v1_private_key()?, curve)
}

/// Encodes `private_key`, a fixed-length scalar, and its uncompressed
/// `public_key` as an `ECPrivateKey`, naming `parameters` if given.
///
/// The encoding is written to the start of `output`, and the used span is
/// returned. [`Error::WrongLength`] is returned if `output` is not sufficient
/// to contain the full encoding.
pub(crate) fn encode<'a>(
    private_key: &[u8],
    public_key: &[u8],
    parameters: Option<asn1::ObjectId>,
    output: &'a mut [u8],
) -> Result<&'a [u8], Error> {
    let ecpk = asn1::pkix::EcPrivateKey {
        version: asn1::pkix::EcPrivateKeyVer::ecPrivkeyVer1,
        privateKey: asn1::OctetString::new(private_key),
        parameters: match parameters {
            Some(x) => x.into(),
            None => asn1::Context::absent(),
        },
        publicKey: asn1::BitString::new(public_key).into(),
    };

    let used = ecpk
        .encode(&mut asn1::Encoder::new(output))
        .map_err(|_| Error::WrongLength)?;

    // The caller owns the encoding, as with the key's `as_bytes`.
    let output = output.get(..used).ok_or(Error::WrongLength)?;
    ct::public_slice(output);
    Ok(output)
}

/// Encodes a key as [`encode`] does, in PKCS#8 v1 on `curve`.
pub(crate) fn encode_pkcs8<'a>(
    private_key: &[u8],
    public_key: &[u8],
    curve: asn1::ObjectId,
    output: &'a mut [u8],
) -> Result<&'a [u8], Error> {
    let mut sec1_buf = [0u8; MAX_LEN];
    let sec1 = encode(private_key, public_key, None, &mut sec1_buf)?;

    pkcs8::Key::construct(
        sec1,
        None,
        asn1::oid::id_ecPublicKey.clone(),
        Some(asn1::Any::ObjectId(curve)),
    )
    .encode(output)
}

/// Whether `encoded`, an X9.62 uncompressed or compressed point, is
/// `uncompressed`.
///
/// A compressed point is `x` and the parity of `y`, which name at most
/// one point, so comparing them with `uncompressed`'s matches exactly the
/// encodings that decompress to it, with no square root. A hybrid point
/// is refused.
pub(crate) fn is_public_key(uncompressed: &[u8], encoded: &[u8]) -> bool {
    let Some((_, xy)) = uncompressed.split_first() else {
        return false;
    };
    let (x, y) = xy.split_at(xy.len() / 2);
    match encoded.split_first() {
        Some((&tag @ (0x02 | 0x03), compressed)) => {
            compressed == x && y.last().is_some_and(|y| tag == 0x02 | (y & 1))
        }
        _ => encoded == uncompressed,
    }
}
