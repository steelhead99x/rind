// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! What the signature modules share: the owned encodings every key type
//! exports, and the fixed-capacity buffer behind them and the signatures.

use core::fmt;

use super::digest::Digest;
use super::sec1;
use crate::error::Error;
use crate::low::{self, Zeroable};
use crate::mid::mldsa::{self, MlDsa87};

pub(crate) mod ecdsa;
pub(crate) mod ed25519;
pub(crate) mod ml_dsa;
pub(crate) mod rsa;
pub(crate) mod slh_dsa;

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests;

/// The hash a signature algorithm applies to the message.
///
/// No variant is SHA-1, so SHA-1 never reaches signing or ECDSA: only
/// [`rsa::VerificationAlgorithm`]'s PKCS#1 v1.5 with SHA-1 takes it.
#[derive(Clone, Copy, Debug, PartialEq)]
#[repr(u8)]
enum HashId {
    Sha256,
    Sha384,
    Sha512,
}

impl HashId {
    /// The hash's output length, in bytes.
    const fn len(self) -> usize {
        match self {
            Self::Sha256 => 32,
            Self::Sha384 => 48,
            Self::Sha512 => 64,
        }
    }
}

/// Runs `$body` with `$H` naming the hash type for `$hash`.
macro_rules! with_hash {
    ($hash:expr, |$H:ident| $body:expr) => {
        match $hash {
            HashId::Sha256 => {
                type $H = crate::high::hash::Sha256;
                $body
            }
            HashId::Sha384 => {
                type $H = crate::high::hash::Sha384;
                $body
            }
            HashId::Sha512 => {
                type $H = crate::high::hash::Sha512;
                $body
            }
        }
    };
}
use with_hash;

/// Verifies with a key: `(key, signature, message)`.
type Verify<K> = fn(&K, &[u8], &[u8]) -> Result<(), Error>;

/// Signs a message into the start of an output and returns the signature:
/// `(key, output, message)`.
type Sign<K> = for<'a> fn(&K, &'a mut [u8], &[u8]) -> Result<&'a [u8], Error>;

/// Writes to the start of an output and returns the written span.
type Write<K> = for<'a> fn(&K, &'a mut [u8]) -> Result<&'a [u8], Error>;

/// Up to `N` bytes, as the owned encodings and signatures hold them.
#[derive(Clone, Copy)]
pub(super) struct Buffer<const N: usize> {
    bytes: [u8; N],
    len: usize,
}

impl<const N: usize> Buffer<N> {
    fn new() -> Self {
        Self {
            bytes: [0; N],
            len: 0,
        }
    }

    /// Runs `write`, which writes to the start of its argument and returns
    /// the written span.
    pub(super) fn write(
        write: impl FnOnce(&mut [u8]) -> Result<&[u8], Error>,
    ) -> Result<Self, Error> {
        let mut buffer = Self::new();
        buffer.len = write(&mut buffer.bytes)?.len();
        Ok(buffer)
    }

    /// Runs `encode` as [`Self::write`] does, for an encoder `N` is sized
    /// for.
    ///
    /// Every `N` holds the encoding of the largest key a loader accepts, so
    /// an encoder that runs out of room is a bug in rind, not bad input.
    pub(super) fn encode(encode: impl FnOnce(&mut [u8]) -> Result<&[u8], Error>) -> Self {
        Self::write(encode).expect("sized for the largest key")
    }
}

impl<const N: usize> From<[u8; N]> for Buffer<N> {
    fn from(bytes: [u8; N]) -> Self {
        Self { bytes, len: N }
    }
}

impl<const N: usize> AsRef<[u8]> for Buffer<N> {
    fn as_ref(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

// Bytes and a length, both valid at zero.
impl<const N: usize> Zeroable for Buffer<N> {}

/// The longest public key encoding: ML-DSA-87's, longer than RSA's largest.
const MAX_PUBLIC_KEY_LEN: usize = max(
    super::rsa::MAX_PUBLIC_KEY_LEN,
    mldsa::public_key_len::<MlDsa87>(),
);

/// The longest `SubjectPublicKeyInfo`: the longest key in a bit string,
/// after its algorithm identifier.
const MAX_SPKI_LEN: usize = MAX_PUBLIC_KEY_LEN + 32;

/// The longest PKCS#8 private key: RSA's, or an ML-DSA-87 key in its
/// expanded form.
const MAX_PKCS8_LEN: usize = max(super::rsa::MAX_PKCS8_LEN, ml_dsa::MAX_PRIVATE_KEY_LEN + 64);

const fn max(a: usize, b: usize) -> usize {
    if a > b { a } else { b }
}

/// The bytes of `digest`, refused unless a signature takes its hash.
fn signed_digest(digest: &Digest) -> Result<&[u8], Error> {
    match digest.signs() {
        true => Ok(digest.as_ref()),
        false => Err(Error::Unsupported),
    }
}

/// A private key encoded as PKCS#8 DER, wiped on drop under the `wipe` feature.
pub struct Pkcs8(pub(super) Buffer<MAX_PKCS8_LEN>);

impl AsRef<[u8]> for Pkcs8 {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Pkcs8 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Pkcs8").finish_non_exhaustive()
    }
}

impl Drop for Pkcs8 {
    fn drop(&mut self) {
        low::zeroise_value(&mut self.0);
    }
}

/// A public key encoded as a `SubjectPublicKeyInfo` in DER.
#[derive(Clone)]
pub struct Spki(pub(super) Buffer<MAX_SPKI_LEN>);

impl AsRef<[u8]> for Spki {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Spki {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Spki").field(&self.as_ref()).finish()
    }
}

/// An ECDSA private key encoded as a SEC1 (RFC 5915) `ECPrivateKey` in
/// DER, wiped on drop under the `wipe` feature.
pub struct Sec1(Buffer<{ sec1::MAX_LEN }>);

impl AsRef<[u8]> for Sec1 {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Sec1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Sec1").finish_non_exhaustive()
    }
}

impl Drop for Sec1 {
    fn drop(&mut self) {
        low::zeroise_value(&mut self.0);
    }
}
