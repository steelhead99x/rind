// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::hash::{Hash, LegacySha1, Sha256, Sha384, Sha512};
use super::pkcs1;
use super::rsa;
use super::signature::{Buffer, Pkcs8, PublicKeyComponents, RSA_MIN_BITS, Spki};
use crate::error::{Error, KeyFormatError};
use crate::low;
use crate::mid::rsa_key_size::RsaKeySize;
use crate::mid::rsa_pub::MAX_PUBLIC_MODULUS_BYTES;

/// Encrypts with a key: `(key, output, message, label)`.
type Encrypt =
    for<'a> fn(&rsa::VerifyingKey, &'a mut [u8], &[u8], &[u8]) -> Result<&'a [u8], Error>;

/// Decrypts with a key: `(key, output, ciphertext, label)`.
type Decrypt = for<'a> fn(&rsa::SigningKey, &'a mut [u8], &[u8], &[u8]) -> Result<&'a [u8], Error>;

/// An RSA-OAEP algorithm: a hash, which MGF1 also uses.
pub struct OaepAlgorithm {
    hash: OaepHash,
    // The only paths to the hash's code, as `signature`'s algorithms hold.
    encrypt: Encrypt,
    decrypt: Decrypt,
    max_message_len: fn(usize) -> usize,
}

#[derive(Clone, Copy, Debug)]
enum OaepHash {
    Sha1,
    Sha256,
    Sha384,
    Sha512,
}

impl fmt::Debug for OaepAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("OaepAlgorithm").field(&self.hash).finish()
    }
}

const fn oaep<H: Hash>(hash: OaepHash) -> OaepAlgorithm {
    OaepAlgorithm {
        hash,
        encrypt: rsa::VerifyingKey::encrypt_oaep::<H>,
        decrypt: rsa::SigningKey::decrypt_oaep::<H>,
        max_message_len: pkcs1::oaep_max_message_len::<H>,
    }
}

/// RSA-OAEP with SHA-256 and MGF1 with SHA-256.
pub static OAEP_SHA256: OaepAlgorithm = oaep::<Sha256>(OaepHash::Sha256);

/// RSA-OAEP with SHA-384 and MGF1 with SHA-384.
pub static OAEP_SHA384: OaepAlgorithm = oaep::<Sha384>(OaepHash::Sha384);

/// RSA-OAEP with SHA-512 and MGF1 with SHA-512.
pub static OAEP_SHA512: OaepAlgorithm = oaep::<Sha512>(OaepHash::Sha512);

/// RSA-OAEP with SHA-1 and MGF1 with SHA-1, JWE's `RSA-OAEP`.
///
/// OAEP relies on no collision resistance, which SHA-1 lacks, but new
/// protocols should use SHA-256.
pub static OAEP_SHA1: OaepAlgorithm = oaep::<LegacySha1>(OaepHash::Sha1);

/// A two-prime RSA private key, with a modulus of 2048 to 8192 bits, bound
/// to the one RSA-OAEP algorithm it decrypts.
pub struct DecryptingKey {
    key: rsa::SigningKey,
    algorithm: AlgorithmRef,
}

/// The key's algorithm.
// Aligned like the private key's `u64` fields, which is 4 bytes on i686 and 8
// on armv7, so any padding `DecryptingKey` needs falls inside this value,
// which its drop wipes whole.
#[derive(Clone, Copy)]
struct AlgorithmRef(low::ZeroableRef<OaepAlgorithm>, [u64; 0]);

impl low::Zeroable for AlgorithmRef {}

impl DecryptingKey {
    /// Generates a key of `size` for `algorithm` from the system random
    /// source.
    ///
    /// This is slow: about 30 milliseconds for 2048 bits, and 15 seconds or
    /// more for 8192 bits, with no upper bound. Its timing reveals only which
    /// candidate primes it discards.
    pub fn generate(algorithm: &'static OaepAlgorithm, size: RsaKeySize) -> Result<Self, Error> {
        Ok(Self::new(algorithm, rsa::SigningKey::generate(size)?))
    }

    /// Loads a PKCS#8 RSA private key for `algorithm`, named
    /// `rsaEncryption`, `id-RSAES-OAEP`, or `id-ea-rsa`.
    ///
    /// A v2 document is taken when it omits its public key, as aws-lc does,
    /// and refused when it carries one.
    pub fn from_pkcs8(algorithm: &'static OaepAlgorithm, der: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(algorithm, rsa::SigningKey::from_pkcs8_der(der)?))
    }

    /// Loads a PKCS#1 `RSAPrivateKey` for `algorithm`.
    pub fn from_pkcs1(algorithm: &'static OaepAlgorithm, der: &[u8]) -> Result<Self, Error> {
        Ok(Self::new(algorithm, rsa::SigningKey::from_pkcs1_der(der)?))
    }

    fn new(algorithm: &'static OaepAlgorithm, key: rsa::SigningKey) -> Self {
        Self {
            key,
            algorithm: AlgorithmRef(low::ZeroableRef::new(algorithm), []),
        }
    }

    fn algorithm(&self) -> &'static OaepAlgorithm {
        self.algorithm.0.get()
    }

    /// Returns the public key, which encrypts to this key with its
    /// algorithm.
    pub fn public_key(&self) -> EncryptingKey {
        // A private key's modulus is at least 2048 bits.
        EncryptingKey::new_unchecked(self.algorithm(), self.key.public_key())
    }

    /// Decrypts `ciphertext`, which must have been encrypted with `label`.
    ///
    /// Every malformed ciphertext, of the wrong length, not below the
    /// modulus, or with bad padding, fails with the same
    /// [`Error::DecryptFailed`], and bad padding takes as long to find as
    /// good, so a caller that reveals the failure is no padding oracle.
    pub fn decrypt(&self, ciphertext: &[u8], label: &[u8]) -> Result<Plaintext, Error> {
        Buffer::write(|output| (self.algorithm().decrypt)(&self.key, output, ciphertext, label))
            .map(Plaintext)
    }

    /// Encodes the private key as PKCS#8.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| self.key.to_pkcs8_der(output)))
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo`.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| {
            self.key.public_key().to_spki_der(output)
        }))
    }
}

impl fmt::Debug for DecryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("DecryptingKey")
            .field("algorithm", self.algorithm())
            .finish_non_exhaustive()
    }
}

impl Drop for DecryptingKey {
    fn drop(&mut self) {
        // The private key wipes itself. Wiping this, which is not secret,
        // lets `tests/zeroing.rs` check every byte.
        low::zeroise_value(&mut self.algorithm);
    }
}

/// An RSA public key, with a modulus of 2048 to 8192 bits, bound to the one
/// RSA-OAEP algorithm it encrypts with.
///
/// Its bytes are its PKCS#1 `RSAPublicKey` DER, however it was given.
pub struct EncryptingKey {
    key: rsa::VerifyingKey,
    algorithm: &'static OaepAlgorithm,
    encoding: Buffer<{ rsa::MAX_PUBLIC_KEY_LEN }>,
}

impl EncryptingKey {
    /// Parses a PKCS#1 `RSAPublicKey` or a `SubjectPublicKeyInfo` for
    /// `algorithm`.
    pub fn new(algorithm: &'static OaepAlgorithm, der: &[u8]) -> Result<Self, Error> {
        Self::checked(algorithm, rsa::VerifyingKey::from_der(der)?)
    }

    /// Loads a key for `algorithm` from its big-endian modulus and exponent,
    /// as a JWK carries them.
    pub fn from_components(
        algorithm: &'static OaepAlgorithm,
        components: &PublicKeyComponents<impl AsRef<[u8]>>,
    ) -> Result<Self, Error> {
        Self::checked(
            algorithm,
            rsa::VerifyingKey::from_components(components.n.as_ref(), components.e.as_ref())?,
        )
    }

    /// Refuses a key below 2048 bits, which [`rsa::VerifyingKey`] takes for
    /// legacy verification.
    fn checked(algorithm: &'static OaepAlgorithm, key: rsa::VerifyingKey) -> Result<Self, Error> {
        match key.modulus_len_bits() >= RSA_MIN_BITS {
            true => Ok(Self::new_unchecked(algorithm, key)),
            false => Err(KeyFormatError::RsaModulus.into()),
        }
    }

    fn new_unchecked(algorithm: &'static OaepAlgorithm, key: rsa::VerifyingKey) -> Self {
        Self {
            encoding: Buffer::encode(|output| key.to_pkcs1_der(output)),
            algorithm,
            key,
        }
    }

    /// Encrypts `message` with `label`, which may be empty, returning a
    /// ciphertext as long as the modulus.
    ///
    /// A message longer than [`Self::max_message_len`] fails with
    /// [`Error::WrongLength`].
    pub fn encrypt(&self, message: &[u8], label: &[u8]) -> Result<Ciphertext, Error> {
        Buffer::write(|output| (self.algorithm.encrypt)(&self.key, output, message, label))
            .map(Ciphertext)
    }

    /// Returns the longest message this key encrypts: the modulus length,
    /// less twice the hash length and two.
    pub fn max_message_len(&self) -> usize {
        (self.algorithm.max_message_len)(self.key.modulus_len_bits().div_ceil(8))
    }

    /// Encodes the key as a `SubjectPublicKeyInfo` naming `rsaEncryption`
    /// with `NULL` parameters.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| self.key.to_spki_der(output)))
    }
}

impl AsRef<[u8]> for EncryptingKey {
    fn as_ref(&self) -> &[u8] {
        self.encoding.as_ref()
    }
}

impl fmt::Debug for EncryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("EncryptingKey")
            .field("algorithm", self.algorithm)
            .field("bytes", &self.as_ref())
            .finish()
    }
}

/// An RSA-OAEP ciphertext, as long as the modulus.
#[derive(Clone)]
pub struct Ciphertext(Buffer<MAX_PUBLIC_MODULUS_BYTES>);

impl AsRef<[u8]> for Ciphertext {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Ciphertext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Ciphertext").field(&self.as_ref()).finish()
    }
}

/// A decrypted message.
pub struct Plaintext(Buffer<MAX_PUBLIC_MODULUS_BYTES>);

impl AsRef<[u8]> for Plaintext {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Plaintext {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Plaintext").finish_non_exhaustive()
    }
}

#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod tests {
    use super::*;
    use crate::low::ct;

    const ALGORITHMS: [&OaepAlgorithm; 4] = [&OAEP_SHA1, &OAEP_SHA256, &OAEP_SHA384, &OAEP_SHA512];

    /// Keys whose modulus fills a whole number of words, or not, or bytes:
    /// at 2049 bits EM's first octet holds the modulus's top bit.
    const KEYS: [&[u8]; 4] = [
        include_bytes!("rsa/rsa2048.pkcs8.der"),
        include_bytes!("rsa/rsa2049.pkcs8.der"),
        include_bytes!("rsa/rsa2056.pkcs8.der"),
        include_bytes!("rsa/rsa4096.pkcs8.der"),
    ];

    fn hash_len(algorithm: &OaepAlgorithm) -> usize {
        match algorithm.hash {
            OaepHash::Sha1 => 20,
            OaepHash::Sha256 => 32,
            OaepHash::Sha384 => 48,
            OaepHash::Sha512 => 64,
        }
    }

    #[test]
    fn round_trip() {
        for der in KEYS {
            for algorithm in ALGORITHMS {
                let key = DecryptingKey::from_pkcs8(algorithm, der).unwrap();
                // Through its PKCS#1 bytes and its SPKI, as a peer gets it.
                let spki = key.to_spki();
                for public in [
                    EncryptingKey::new(algorithm, key.public_key().as_ref()).unwrap(),
                    EncryptingKey::new(algorithm, spki.as_ref()).unwrap(),
                ] {
                    assert_eq!(public.as_ref(), key.public_key().as_ref());
                    assert_eq!(public.to_spki().as_ref(), spki.as_ref());
                    let max = public.max_message_len();
                    for (len, label) in [(0, &b""[..]), (1, b"label"), (max, b"")] {
                        let message = vec![0xa5; len];
                        let ciphertext = public.encrypt(&message, label).unwrap();
                        assert_eq!(ciphertext.as_ref().len(), max + 2 * hash_len(algorithm) + 2);
                        let plaintext = key.decrypt(ciphertext.as_ref(), label).unwrap();
                        ct::public_slice(plaintext.as_ref());
                        assert_eq!(plaintext.as_ref(), message);
                    }
                    assert_eq!(
                        public.encrypt(&vec![0; max + 1], b"").err(),
                        Some(Error::WrongLength)
                    );
                }
            }
        }
    }

    /// Each way a ciphertext can be wrong fails the same way.
    #[test]
    fn every_failure_is_the_same() {
        let der = include_bytes!("rsa/rsa2048.der");
        let key = DecryptingKey::from_pkcs1(&OAEP_SHA256, der).unwrap();
        let public = key.public_key();
        let ciphertext = public.encrypt(b"message", b"label").unwrap();
        let ciphertext = ciphertext.as_ref();

        let mut flipped = ciphertext.to_vec();
        flipped[100] ^= 1;
        // The DER is a `SEQUENCE` of the modulus, with its sign byte, and
        // the exponent.
        let modulus = &public.as_ref()[9..265];

        for (ciphertext, label) in [
            (ciphertext, &b"other"[..]),
            (ciphertext, b""),
            (&flipped, b"label"),
            (&ciphertext[1..], b"label"),
            (&[ciphertext, &[0]].concat(), b"label"),
            (&[0; 256], b"label"),
            (modulus, b"label"),
            (&[0xff; 256], b"label"),
            (&[], b"label"),
        ] {
            assert_eq!(
                key.decrypt(ciphertext, label).err(),
                Some(Error::DecryptFailed)
            );
        }

        // The same key bound to another hash.
        let other = DecryptingKey::from_pkcs1(&OAEP_SHA384, der).unwrap();
        assert_eq!(
            other.decrypt(ciphertext, b"label").err(),
            Some(Error::DecryptFailed)
        );

        let plaintext = key.decrypt(ciphertext, b"label").unwrap();
        ct::public_slice(plaintext.as_ref());
        assert_eq!(plaintext.as_ref(), b"message");
    }

    #[test]
    fn refuses_small_public_keys() {
        assert_eq!(
            EncryptingKey::new(&OAEP_SHA256, include_bytes!("rsa/rsa2047.pub.der")).err(),
            Some(KeyFormatError::RsaModulus.into())
        );
    }

    /// Under `admin/ctgrind`, memcheck fails this if encryption branches on
    /// or indexes by the message or seed, or decryption by the key or the
    /// decrypted value, before its padding is found valid.
    #[test]
    fn stays_secret() {
        for algorithm in ALGORITHMS {
            let key = DecryptingKey::from_pkcs8(algorithm, include_bytes!("rsa/rsa2049.pkcs8.der"))
                .unwrap();
            let message = [0x5a; 32];
            ct::secret_slice(&message);
            let ciphertext = key.public_key().encrypt(&message, b"label").unwrap();

            let plaintext = key.decrypt(ciphertext.as_ref(), b"label").unwrap();
            ct::public_slice(plaintext.as_ref());
            assert_eq!(plaintext.as_ref(), [0x5a; 32]);

            // Bad padding from a wrong label, a tampered ciphertext, and a
            // value below the modulus that no one encrypted.
            let mut tampered = ciphertext.as_ref().to_vec();
            tampered[1] ^= 1;
            let unencrypted = [&[0][..], &[0x5a; 256]].concat();
            for (ciphertext, label) in [
                (ciphertext.as_ref(), &b"other"[..]),
                (&tampered, b"label"),
                (&unencrypted, b"label"),
            ] {
                assert_eq!(
                    key.decrypt(ciphertext, label).err(),
                    Some(Error::DecryptFailed)
                );
            }
        }
    }
}
