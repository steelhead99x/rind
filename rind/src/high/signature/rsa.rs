// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! RSA signatures' public API: key pairs, public keys, and the padding
//! schemes they sign and verify with.
//!
//! Neither half of an RSA key is bound to a scheme, as TLS signs with
//! whichever one each handshake negotiates: every call that pads takes the
//! algorithm.

use core::fmt;

use super::{Buffer, HashId, Pkcs8, Spki};
use crate::error::{Error, KeyFormatError};
use crate::high::rsa::{self, PssSalt};
use crate::low::{self, Zeroable};
use crate::mid::rsa_key_size::RsaKeySize;
use crate::mid::rsa_pub::MAX_PUBLIC_MODULUS_BYTES;

#[derive(Clone, Copy, Debug, PartialEq)]
enum RsaPadding {
    /// RSASSA-PKCS1-v1_5.
    Pkcs1,
    /// RSASSA-PSS, with MGF1 on the same hash and a salt of this length.
    Pss(PssSalt),
}

#[derive(Clone, Copy, Debug)]
struct RsaScheme {
    padding: RsaPadding,
    hash: HashId,
}

/// Signs with an RSA key, taking a PSS salt length that PKCS#1 v1.5
/// ignores: `(key, salt, output, message)`.
type RsaSign =
    for<'a> fn(&rsa::SigningKey, PssSalt, &'a mut [u8], &[u8]) -> Result<&'a [u8], Error>;

/// Verifies with an RSA key, taking a PSS salt length, or `None` for any,
/// that PKCS#1 v1.5 ignores: `(key, salt, signature, message)`.
type RsaVerify = fn(&rsa::VerifyingKey, Option<PssSalt>, &[u8], &[u8]) -> Result<(), Error>;

// Only constant functions call these, so a static names only its own
// scheme's code, as ECDSA's `with_ecdsa!` does.
impl RsaScheme {
    const fn pss(hash: HashId, salt: PssSalt) -> Self {
        Self {
            padding: RsaPadding::Pss(salt),
            hash,
        }
    }

    /// The PSS salt length, which PKCS#1 v1.5 ignores.
    const fn salt(self) -> PssSalt {
        match self.padding {
            RsaPadding::Pkcs1 => PssSalt::Hash,
            RsaPadding::Pss(salt) => salt,
        }
    }

    const fn signer(self) -> RsaSign {
        match (self.padding, self.hash) {
            (RsaPadding::Pkcs1, HashId::Sha256) => |key, _, out, m| key.sign_pkcs1_sha256(out, m),
            (RsaPadding::Pkcs1, HashId::Sha384) => |key, _, out, m| key.sign_pkcs1_sha384(out, m),
            (RsaPadding::Pkcs1, HashId::Sha512) => |key, _, out, m| key.sign_pkcs1_sha512(out, m),
            (RsaPadding::Pss(_), HashId::Sha256) => rsa::SigningKey::sign_pss_sha256,
            (RsaPadding::Pss(_), HashId::Sha384) => rsa::SigningKey::sign_pss_sha384,
            (RsaPadding::Pss(_), HashId::Sha512) => rsa::SigningKey::sign_pss_sha512,
        }
    }

    const fn verifier(self) -> RsaVerify {
        match (self.padding, self.hash) {
            (RsaPadding::Pkcs1, HashId::Sha256) => |key, _, s, m| key.verify_pkcs1_sha256(s, m),
            (RsaPadding::Pkcs1, HashId::Sha384) => |key, _, s, m| key.verify_pkcs1_sha384(s, m),
            (RsaPadding::Pkcs1, HashId::Sha512) => |key, _, s, m| key.verify_pkcs1_sha512(s, m),
            (RsaPadding::Pss(_), HashId::Sha256) => rsa::VerifyingKey::verify_pss_sha256,
            (RsaPadding::Pss(_), HashId::Sha384) => rsa::VerifyingKey::verify_pss_sha384,
            (RsaPadding::Pss(_), HashId::Sha512) => rsa::VerifyingKey::verify_pss_sha512,
        }
    }

    /// The smallest modulus whose PSS encoding fits the salt, if over
    /// `min_bits`: RFC 8017 section 9.1.1 needs `ceil((bits - 1) / 8)`
    /// bytes for the hash, the salt, and two more.
    const fn min_bits(self, min_bits: usize) -> usize {
        let salt = match self.padding {
            RsaPadding::Pkcs1 => return min_bits,
            RsaPadding::Pss(PssSalt::Hash) => self.hash.len(),
            RsaPadding::Pss(PssSalt::Max) => 0,
            RsaPadding::Pss(PssSalt::Len(len)) => len as usize,
        };
        let fits = 8 * (self.hash.len() + salt + 1) + 2;
        if fits > min_bits { fits } else { min_bits }
    }
}

/// How long an RSASSA-PSS salt is, beside the hash's length that the
/// `PSS_*` algorithms use.
///
/// A signature verifies only with the salt length it was made with.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum PssSaltLength {
    /// The longest the modulus allows: the encoded message's length, a byte
    /// shorter than the modulus when its bit length is one more than a
    /// multiple of eight, less the hash's length and two.
    Max,
    /// This many bytes. A modulus too short for them is refused when a key
    /// verifies or signs with it, not here.
    Custom(u16),
}

impl PssSaltLength {
    const fn salt(self) -> PssSalt {
        match self {
            Self::Max => PssSalt::Max,
            Self::Custom(len) => PssSalt::Len(len),
        }
    }
}

/// What an RSA verification algorithm verifies: a scheme rind also signs
/// with, or PKCS#1 v1.5 with SHA-1 or PSS with any salt length, which it
/// only verifies.
#[derive(Clone, Copy, Debug)]
enum RsaVerification {
    Scheme(RsaScheme),
    Pkcs1Sha1,
    PssAnySalt(HashId),
}

impl RsaVerification {
    const fn verifier(self) -> RsaVerify {
        match self {
            Self::Scheme(scheme) => scheme.verifier(),
            Self::Pkcs1Sha1 => |key, _, s, m| key.verify_pkcs1_sha1(s, m),
            Self::PssAnySalt(hash) => RsaScheme::pss(hash, PssSalt::Hash).verifier(),
        }
    }

    /// The PSS salt length to verify, `None` for any.
    fn salt(self) -> Option<PssSalt> {
        match self {
            Self::Scheme(scheme) => Some(scheme.salt()),
            Self::Pkcs1Sha1 | Self::PssAnySalt(_) => None,
        }
    }
}

/// An RSA verification algorithm: a padding, a hash, and the smallest
/// modulus it accepts, for [`PublicKey::verify`].
pub struct VerificationAlgorithm {
    verification: RsaVerification,
    min_bits: usize,
    // The only path to the scheme's code, as ECDSA's algorithms hold theirs.
    verify: RsaVerify,
}

impl fmt::Debug for VerificationAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VerificationAlgorithm")
            .field("verification", &self.verification)
            .field("min_bits", &self.min_bits)
            .finish()
    }
}

impl VerificationAlgorithm {
    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a salt of `salt_length`,
    /// for moduli of 2048 to 8192 bits long enough for it.
    pub const fn pss_sha256(salt_length: PssSaltLength) -> Self {
        verification(RsaScheme::pss(HashId::Sha256, salt_length.salt()), MIN_BITS)
    }

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a salt of `salt_length`,
    /// for moduli of 2048 to 8192 bits long enough for it.
    pub const fn pss_sha384(salt_length: PssSaltLength) -> Self {
        verification(RsaScheme::pss(HashId::Sha384, salt_length.salt()), MIN_BITS)
    }

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a salt of `salt_length`,
    /// for moduli of 2048 to 8192 bits long enough for it.
    pub const fn pss_sha512(salt_length: PssSaltLength) -> Self {
        verification(RsaScheme::pss(HashId::Sha512, salt_length.salt()), MIN_BITS)
    }
}

const fn verification(scheme: RsaScheme, min_bits: usize) -> VerificationAlgorithm {
    algorithm(RsaVerification::Scheme(scheme), scheme.min_bits(min_bits))
}

#[cfg_attr(coverage_nightly, coverage(off))] // const-evaluated only
const fn sha1_verification(min_bits: usize) -> VerificationAlgorithm {
    algorithm(RsaVerification::Pkcs1Sha1, min_bits)
}

const fn algorithm(verification: RsaVerification, min_bits: usize) -> VerificationAlgorithm {
    VerificationAlgorithm {
        verification,
        min_bits,
        verify: verification.verifier(),
    }
}

/// An RSA signing algorithm: a padding and a hash, for [`KeyPair::sign`].
pub struct SigningAlgorithm {
    scheme: RsaScheme,
    // The only path to the scheme's code, as `VerificationAlgorithm`'s.
    sign: RsaSign,
}

impl SigningAlgorithm {
    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a salt of `salt_length`.
    pub const fn pss_sha256(salt_length: PssSaltLength) -> Self {
        signing(RsaScheme::pss(HashId::Sha256, salt_length.salt()))
    }

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a salt of `salt_length`.
    pub const fn pss_sha384(salt_length: PssSaltLength) -> Self {
        signing(RsaScheme::pss(HashId::Sha384, salt_length.salt()))
    }

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a salt of `salt_length`.
    pub const fn pss_sha512(salt_length: PssSaltLength) -> Self {
        signing(RsaScheme::pss(HashId::Sha512, salt_length.salt()))
    }
}

impl fmt::Debug for SigningAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SigningAlgorithm")
            .field(&self.scheme)
            .finish()
    }
}

const fn signing(scheme: RsaScheme) -> SigningAlgorithm {
    SigningAlgorithm {
        scheme,
        sign: scheme.signer(),
    }
}

const PKCS1_SHA256_SCHEME: RsaScheme = RsaScheme {
    padding: RsaPadding::Pkcs1,
    hash: HashId::Sha256,
};
const PKCS1_SHA384_SCHEME: RsaScheme = RsaScheme {
    padding: RsaPadding::Pkcs1,
    hash: HashId::Sha384,
};
const PKCS1_SHA512_SCHEME: RsaScheme = RsaScheme {
    padding: RsaPadding::Pkcs1,
    hash: HashId::Sha512,
};
const PSS_SHA256_SCHEME: RsaScheme = RsaScheme::pss(HashId::Sha256, PssSalt::Hash);
const PSS_SHA384_SCHEME: RsaScheme = RsaScheme::pss(HashId::Sha384, PssSalt::Hash);
const PSS_SHA512_SCHEME: RsaScheme = RsaScheme::pss(HashId::Sha512, PssSalt::Hash);

/// The smallest modulus a verification algorithm accepts, unless it is
/// under [`verify::legacy`], and the smallest a key pair loads.
pub(crate) const MIN_BITS: usize = 2048;

/// An RSA public key as its big-endian modulus and exponent, as a JWK
/// carries it, rather than DER.
#[derive(Clone, Copy, Debug)]
pub struct PublicKeyComponents<B> {
    /// The modulus, without leading zero bytes.
    pub n: B,
    /// The public exponent, without leading zero bytes.
    pub e: B,
}

/// An RSA public key, with a modulus of 1024 to 8192 bits, which verifies
/// with any [`VerificationAlgorithm`] whose floor it meets.
///
/// Its bytes are its PKCS#1 `RSAPublicKey` DER, however it was loaded.
#[derive(Clone)]
pub struct PublicKey {
    key: rsa::VerifyingKey,
    encoding: RsaPublicKeyDer,
}

/// The public key's PKCS#1 DER.
// The empty array aligns it like the private key's `u64` words (to 8 bytes on
// armv7, 4 on i686), so a key pair's padding falls inside this value, which
// `KeyPair`'s drop wipes whole, rather than after it, where
// `tests/zeroing.rs` finds stale bytes.
#[derive(Clone, Copy)]
struct RsaPublicKeyDer(Buffer<{ rsa::MAX_PUBLIC_KEY_LEN }>, [u64; 0]);

// Words, bytes, and lengths, all valid at zero.
impl Zeroable for PublicKey {}

impl PublicKey {
    /// Parses a PKCS#1 `RSAPublicKey`, refusing a malformed key before any
    /// signature arrives.
    pub fn new(der: &[u8]) -> Result<Self, Error> {
        Self::from_key(rsa::VerifyingKey::from_pkcs1_der(der)?)
    }

    /// Parses a public key from its `SubjectPublicKeyInfo` DER, naming
    /// `rsaEncryption`, `id-RSAES-OAEP`, or `id-ea-rsa` with `NULL`
    /// parameters or none.
    pub fn from_spki(der: &[u8]) -> Result<Self, Error> {
        Self::from_key(rsa::VerifyingKey::from_spki_der(der)?)
    }

    /// Loads a public key from its big-endian modulus and exponent, as a
    /// JWK carries them.
    pub fn from_components(
        components: &PublicKeyComponents<impl AsRef<[u8]>>,
    ) -> Result<Self, Error> {
        let key = rsa::VerifyingKey::from_components(components.n.as_ref(), components.e.as_ref())?;
        Self::from_key(key)
    }

    fn from_key(key: rsa::VerifyingKey) -> Result<Self, Error> {
        Ok(Self {
            encoding: RsaPublicKeyDer(Buffer::write(|output| key.to_pkcs1_der(output))?, []),
            key,
        })
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo` naming
    /// `rsaEncryption`.
    pub fn to_spki(&self) -> Spki {
        Spki(Buffer::encode(|output| self.key.to_spki_der(output)))
    }

    /// The modulus's length in bytes, which is also its signatures' length,
    /// so a caller can refuse a small key before it verifies anything.
    pub fn modulus_len(&self) -> usize {
        self.key.modulus_len_bits().div_ceil(8)
    }

    /// Verifies `signature` over `message` with `algorithm`, refusing a
    /// malformed signature, and refusing the key if its modulus is below
    /// the algorithm's floor.
    pub fn verify(
        &self,
        algorithm: &VerificationAlgorithm,
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), Error> {
        if self.key.modulus_len_bits() < algorithm.min_bits {
            return Err(KeyFormatError::RsaModulus.into());
        }
        (algorithm.verify)(&self.key, algorithm.verification.salt(), signature, message)
    }
}

#[cfg(any(test, rind_fips))]
impl PublicKey {
    /// The modulus length in bits: what the FIPS module checks against
    /// FIPS 186-5's sizes.
    pub(crate) fn modulus_bits(&self) -> usize {
        self.key.modulus_len_bits()
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.encoding.0.as_ref()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicKey").field(&self.as_ref()).finish()
    }
}

/// An RSA signature, as long as the modulus.
#[derive(Clone, Copy)]
pub struct Signature(Buffer<MAX_PUBLIC_MODULUS_BYTES>);

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        self.0.as_ref()
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}

/// A two-prime RSA private key, with a modulus of 2048 to 8192 bits, and its
/// public key.
pub struct KeyPair {
    key: rsa::SigningKey,
    public: PublicKey,
}

impl KeyPair {
    /// Generates a key pair of `size` from the system random source.
    ///
    /// This is slow: about 30 milliseconds for 2048 bits, and 15 seconds or
    /// more for 8192 bits, with no upper bound. Its timing reveals only which
    /// candidate primes it discards.
    pub fn generate(size: RsaKeySize) -> Result<Self, Error> {
        Self::new(rsa::SigningKey::generate(size)?)
    }

    /// Loads a PKCS#8 v1 RSA private key, named `rsaEncryption`,
    /// `id-RSAES-OAEP`, or `id-ea-rsa`.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        Self::new(rsa::SigningKey::from_pkcs8_der(der)?)
    }

    /// Loads a PKCS#1 `RSAPrivateKey`.
    pub fn from_pkcs1(der: &[u8]) -> Result<Self, Error> {
        Self::new(rsa::SigningKey::from_pkcs1_der(der)?)
    }

    fn new(key: rsa::SigningKey) -> Result<Self, Error> {
        let public = PublicKey::from_key(key.public_key())?;
        Ok(Self { key, public })
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Signs `message` with `algorithm`, as long as the modulus.
    ///
    /// A PSS salt too long for the modulus is refused as the key's size.
    pub fn sign(&self, algorithm: &SigningAlgorithm, message: &[u8]) -> Result<Signature, Error> {
        Buffer::write(|output| {
            let output = output
                .get_mut(..self.key.modulus_len_bytes())
                .ok_or(Error::WrongLength)?;
            (algorithm.sign)(&self.key, algorithm.scheme.salt(), output, message)
        })
        .map(Signature)
    }

    /// Encodes the private key as PKCS#8.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        Pkcs8(Buffer::encode(|output| self.key.to_pkcs8_der(output)))
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("public_key", &self.public.as_ref())
            .finish_non_exhaustive()
    }
}

impl Drop for KeyPair {
    fn drop(&mut self) {
        // Not secret, but wiping it lets `tests/zeroing.rs` check every byte.
        low::zeroise_value(&mut self.public);
    }
}

/// Algorithms a key pair signs with.
pub(crate) mod sign {
    use super::*;

    /// RSASSA-PKCS1-v1_5 with SHA-256.
    pub static PKCS1_SHA256: SigningAlgorithm = signing(PKCS1_SHA256_SCHEME);

    /// RSASSA-PKCS1-v1_5 with SHA-384.
    pub static PKCS1_SHA384: SigningAlgorithm = signing(PKCS1_SHA384_SCHEME);

    /// RSASSA-PKCS1-v1_5 with SHA-512.
    pub static PKCS1_SHA512: SigningAlgorithm = signing(PKCS1_SHA512_SCHEME);

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a 32-byte salt.
    pub static PSS_SHA256: SigningAlgorithm = signing(PSS_SHA256_SCHEME);

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a 48-byte salt.
    pub static PSS_SHA384: SigningAlgorithm = signing(PSS_SHA384_SCHEME);

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a 64-byte salt.
    pub static PSS_SHA512: SigningAlgorithm = signing(PSS_SHA512_SCHEME);
}

/// Algorithms a public key verifies with.
pub(crate) mod verify {
    use super::*;

    /// RSASSA-PKCS1-v1_5 with SHA-256, for moduli of 2048 to 8192 bits.
    pub static PKCS1_SHA256: VerificationAlgorithm = verification(PKCS1_SHA256_SCHEME, MIN_BITS);

    /// RSASSA-PKCS1-v1_5 with SHA-384, for moduli of 2048 to 8192 bits.
    pub static PKCS1_SHA384: VerificationAlgorithm = verification(PKCS1_SHA384_SCHEME, MIN_BITS);

    /// RSASSA-PKCS1-v1_5 with SHA-512, for moduli of 2048 to 8192 bits.
    pub static PKCS1_SHA512: VerificationAlgorithm = verification(PKCS1_SHA512_SCHEME, MIN_BITS);

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a 32-byte salt, for moduli of 2048 to 8192 bits.
    pub static PSS_SHA256: VerificationAlgorithm = verification(PSS_SHA256_SCHEME, MIN_BITS);

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a 48-byte salt, for moduli of 2048 to 8192 bits.
    pub static PSS_SHA384: VerificationAlgorithm = verification(PSS_SHA384_SCHEME, MIN_BITS);

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a 64-byte salt, for moduli of 2048 to 8192 bits.
    pub static PSS_SHA512: VerificationAlgorithm = verification(PSS_SHA512_SCHEME, MIN_BITS);

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a salt of any length, for moduli of 2048 to 8192 bits.
    pub static PSS_SHA256_ANY_SALT: VerificationAlgorithm =
        algorithm(RsaVerification::PssAnySalt(HashId::Sha256), MIN_BITS);

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a salt of any length, for moduli of 2048 to 8192 bits.
    pub static PSS_SHA384_ANY_SALT: VerificationAlgorithm =
        algorithm(RsaVerification::PssAnySalt(HashId::Sha384), MIN_BITS);

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a salt of any length, for moduli of 2048 to 8192 bits.
    pub static PSS_SHA512_ANY_SALT: VerificationAlgorithm =
        algorithm(RsaVerification::PssAnySalt(HashId::Sha512), MIN_BITS);

    /// Verification algorithms with a modulus floor other than 2048 bits, or SHA-1.
    pub(crate) mod legacy {
        use super::super::*;

        /// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures only: SHA-1 collisions are practical.
        pub static PKCS1_SHA1: VerificationAlgorithm = sha1_verification(MIN_BITS);

        /// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures by keys with moduli down to 1024 bits.
        pub static PKCS1_1024_SHA1: VerificationAlgorithm = sha1_verification(1024);

        /// RSASSA-PKCS1-v1_5 with SHA-256, for old keys with moduli down to 1024 bits.
        pub static PKCS1_1024_SHA256: VerificationAlgorithm =
            verification(PKCS1_SHA256_SCHEME, 1024);

        /// RSASSA-PKCS1-v1_5 with SHA-512, for old keys with moduli down to 1024 bits.
        pub static PKCS1_1024_SHA512: VerificationAlgorithm =
            verification(PKCS1_SHA512_SCHEME, 1024);

        /// RSASSA-PKCS1-v1_5 with SHA-384, for moduli of 3072 to 8192 bits.
        pub static PKCS1_3072_SHA384: VerificationAlgorithm =
            verification(PKCS1_SHA384_SCHEME, 3072);
    }
}
