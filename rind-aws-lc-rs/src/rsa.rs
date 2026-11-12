//! RSA signatures and RSA-OAEP encryption.
//!
//! `KeyPair::from_components` and `KeyPairComponents` are not offered:
//! building a key from big-endian private components means encoding them as
//! DER here, which branches on their secret leading bytes. Load the key as
//! PKCS#1 or PKCS#8 instead. Nor is PKCS#1 v1.5 encryption
//! (`Pkcs1PublicEncryptingKey`, `Pkcs1PrivateDecryptingKey`), which invites
//! padding-oracle attacks and rind refuses, or `KeyPair::sign_digest`, since
//! rind signs only digests it computed.

use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt;
use core::ops::RangeInclusive;
use std::sync::OnceLock;

use signing::RsaEncoding;

use crate::digest::{self, Digest};
use crate::encoding::{AsDer, Pkcs8V1Der, PublicKeyX509Der};
use crate::error::{KeyRejected, Unspecified, unspecified};
#[cfg(feature = "ring-io")]
use crate::io;
use crate::signature::{self, ParsedPublicKey, private};
use crate::wipe::Wiped;
use crate::{der, rand, sealed};

/// An RSA key size.
#[non_exhaustive]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeySize {
    /// A 2048-bit modulus.
    Rsa2048,
    /// A 3072-bit modulus.
    Rsa3072,
    /// A 4096-bit modulus.
    Rsa4096,
    /// An 8192-bit modulus.
    Rsa8192,
}

impl KeySize {
    /// The modulus's length in bytes.
    #[must_use]
    pub fn len(self) -> usize {
        match self {
            Self::Rsa2048 => 256,
            Self::Rsa3072 => 384,
            Self::Rsa4096 => 512,
            Self::Rsa8192 => 1024,
        }
    }

    fn rind(self) -> rind::rsa::KeySize {
        match self {
            Self::Rsa2048 => rind::rsa::KeySize::Rsa2048,
            Self::Rsa3072 => rind::rsa::KeySize::Rsa3072,
            Self::Rsa4096 => rind::rsa::KeySize::Rsa4096,
            Self::Rsa8192 => rind::rsa::KeySize::Rsa8192,
        }
    }
}

/// Refuses a modulus outside 2048 to 8192 bits, as aws-lc-rs does.
fn check_bits(bits: usize) -> Result<(), KeyRejected> {
    match bits {
        2048..=8192 => Ok(()),
        0..=2047 => Err(KeyRejected::too_small()),
        _ => Err(KeyRejected::too_large()),
    }
}

/// An RSA private key and its public key, for signing.
#[derive(Clone)]
pub struct KeyPair {
    key: Arc<rind::signature::RsaKeyPair>,
    public: PublicKey,
}

impl sealed::Sealed for KeyPair {}

impl KeyPair {
    fn new(key: rind::signature::RsaKeyPair) -> Result<Self, KeyRejected> {
        let public = key.public_key(&rind::signature::sign::RSA_PKCS1_SHA256);
        let public =
            PublicKey::from_pkcs1(public.as_ref()).map_err(|_| KeyRejected::unexpected_error())?;
        check_bits(der::bits(&public.n))?;
        Ok(Self {
            key: Arc::new(key),
            public,
        })
    }

    /// Generates a key pair of `size` from the system random source.
    pub fn generate(size: KeySize) -> Result<Self, Unspecified> {
        let key = rind::signature::RsaKeyPair::generate(size.rind()).map_err(unspecified)?;
        Ok(Self::new(key)?)
    }

    /// Loads a PKCS#8 v1 RSA private key.
    pub fn from_pkcs8(pkcs8: &[u8]) -> Result<Self, KeyRejected> {
        rind::signature::RsaKeyPair::from_pkcs8(pkcs8)
            .map_err(KeyRejected::rind)
            .and_then(Self::new)
    }

    /// Loads a PKCS#1 `RSAPrivateKey`.
    pub fn from_der(input: &[u8]) -> Result<Self, KeyRejected> {
        rind::signature::RsaKeyPair::from_pkcs1(input)
            .map_err(KeyRejected::rind)
            .and_then(Self::new)
    }

    /// Signs `msg` with `padding_alg` into `signature`, which must be
    /// [`Self::public_modulus_len`] bytes.
    ///
    /// rind draws a PSS salt from the system random source itself, which
    /// `rng`, the only [`rand::SecureRandom`], also is.
    pub fn sign(
        &self,
        padding_alg: &'static dyn RsaEncoding,
        rng: &dyn rand::SecureRandom,
        msg: &[u8],
        signature: &mut [u8],
    ) -> Result<(), Unspecified> {
        let _ = rng;
        if signature.len() != self.public_modulus_len() {
            return Err(Unspecified);
        }
        let signed = padding_alg
            .encoding()
            .with_rind(|algorithm| self.key.sign(algorithm, msg))
            .map_err(unspecified)?;
        signature
            .get_mut(..signed.as_ref().len())
            .ok_or(Unspecified)?
            .copy_from_slice(signed.as_ref());
        Ok(())
    }

    /// The modulus's length in bytes, which every signature has.
    ///
    /// Reads the modulus bytes directly. `PublicKey::modulus_len` is
    /// `ring-io` only, as in aws-lc-rs, and this method is not.
    #[must_use]
    pub fn public_modulus_len(&self) -> usize {
        self.public.n.len()
    }
}

impl signature::KeyPair for KeyPair {
    type PublicKey = PublicKey;

    fn public_key(&self) -> &PublicKey {
        &self.public
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "RsaKeyPair {{ public_key: {:?} }}", self.public)
    }
}

impl AsDer<Pkcs8V1Der<'static>> for KeyPair {
    fn as_der(&self) -> Result<Pkcs8V1Der<'static>, Unspecified> {
        Ok(Pkcs8V1Der::new(self.key.to_pkcs8().as_ref().to_vec()))
    }
}

/// The verification algorithm with rind's widest modulus range, 1024 to 8192
/// bits, which loads RSA public keys outside any one algorithm.
const ANY_RSA: &rind::signature::RsaVerificationAlgorithm =
    &rind::signature::verify::legacy::RSA_PKCS1_1024_SHA1;

/// Loads a PKCS#1 `RSAPublicKey` or `SubjectPublicKeyInfo` as rind does,
/// refusing what AWS-LC's `RSA_check_key` does, such as an even modulus or an
/// exponent of 1. Its bytes are then always PKCS#1.
fn rind_public_key(der: &[u8]) -> Result<rind::signature::PublicKey, Unspecified> {
    rind::signature::PublicKey::new(ANY_RSA, der).map_err(|_| Unspecified)
}

/// The `rsaEncryption` `SubjectPublicKeyInfo` holding a PKCS#1 `RSAPublicKey`.
fn spki(pkcs1: &[u8]) -> Result<PublicKeyX509Der<'static>, Unspecified> {
    let spki = rind_public_key(pkcs1)?.to_spki();
    Ok(PublicKeyX509Der::new(spki.as_ref().to_vec()))
}

/// An RSA public key, whose bytes are its PKCS#1 `RSAPublicKey` DER.
#[derive(Clone)]
pub struct PublicKey {
    der: Box<[u8]>,
    n: Box<[u8]>,
    #[cfg_attr(not(feature = "ring-io"), allow(dead_code))]
    e: Box<[u8]>,
}

impl PublicKey {
    /// Wraps a PKCS#1 `RSAPublicKey` that rind has already parsed.
    fn from_pkcs1(der: &[u8]) -> Result<Self, Unspecified> {
        let (n, e) = der::rsa_public_key(der)?;
        Ok(Self {
            der: der.into(),
            n: n.into(),
            e: e.into(),
        })
    }

    /// Parses a PKCS#1 `RSAPublicKey` or an `rsaEncryption`
    /// `SubjectPublicKeyInfo`.
    pub fn from_der(input: &[u8]) -> Result<Self, KeyRejected> {
        rind_public_key(input)
            .and_then(|key| Self::from_pkcs1(key.as_ref()))
            .map_err(|_| KeyRejected::invalid_encoding())
    }

    /// The modulus.
    #[cfg(feature = "ring-io")]
    #[must_use]
    pub fn modulus(&self) -> io::Positive<'_> {
        io::Positive::new(&self.n)
    }

    /// The public exponent.
    #[cfg(feature = "ring-io")]
    #[must_use]
    pub fn exponent(&self) -> io::Positive<'_> {
        io::Positive::new(&self.e)
    }

    /// The modulus's length in bytes.
    #[cfg(feature = "ring-io")]
    #[must_use]
    pub fn modulus_len(&self) -> usize {
        self.n.len()
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        &self.der
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("RsaPublicKey(")?;
        fmt::Debug::fmt(&crate::Hex(&self.der), f)?;
        f.write_str(")")
    }
}

impl AsDer<PublicKeyX509Der<'static>> for PublicKey {
    fn as_der(&self) -> Result<PublicKeyX509Der<'static>, Unspecified> {
        spki(&self.der)
    }
}

/// An RSA public key as its big-endian modulus and exponent, without leading
/// zero bytes.
#[derive(Clone)]
pub struct PublicKeyComponents<B> {
    /// The modulus.
    pub n: B,
    /// The public exponent.
    pub e: B,
}

impl<B: fmt::Debug> fmt::Debug for PublicKeyComponents<B> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("RsaPublicKeyComponents")
            .field("n", &self.n)
            .field("e", &self.e)
            .finish()
    }
}

impl<B: Copy> Copy for PublicKeyComponents<B> {}

impl<B: AsRef<[u8]>> PublicKeyComponents<B> {
    fn rind(&self) -> Result<rind::rsa::PublicKeyComponents<&[u8]>, Unspecified> {
        let (n, e) = (self.n.as_ref(), self.e.as_ref());
        // aws-lc-rs refuses a leading zero byte.
        if n.first().is_none_or(|top| *top == 0) || e.first().is_none_or(|top| *top == 0) {
            return Err(Unspecified);
        }
        Ok(rind::rsa::PublicKeyComponents { n, e })
    }

    fn parse(&self, params: &RsaParameters) -> Result<rind::signature::PublicKey, Unspecified> {
        let components = self.rind()?;
        params
            .with_rind(|algorithm| {
                rind::signature::PublicKey::from_components(algorithm, &components)
            })
            .map_err(unspecified)
    }

    /// Verifies `signature` over `message` with this key and `params`.
    pub fn verify(
        &self,
        params: &RsaParameters,
        message: &[u8],
        signature: &[u8],
    ) -> Result<(), Unspecified> {
        self.parse(params)?
            .verify(message, signature)
            .map_err(unspecified)
    }

    /// Parses the key once, for `params`, to verify many signatures.
    pub fn to_parsed_public_key(
        &self,
        params: &'static RsaParameters,
    ) -> Result<ParsedPublicKey, KeyRejected> {
        let key = self
            .parse(params)
            .map_err(|_| KeyRejected::inconsistent_components())?;
        let spki = key.to_spki();
        Ok(ParsedPublicKey::from_parts(params, key, spki.as_ref()))
    }
}

#[cfg(feature = "ring-io")]
impl From<&PublicKey> for PublicKeyComponents<Vec<u8>> {
    fn from(public_key: &PublicKey) -> Self {
        Self {
            n: public_key.n.to_vec(),
            e: public_key.e.to_vec(),
        }
    }
}

// aws-lc-rs implements `TryInto` rather than `TryFrom`, so
// `PublicEncryptingKey::try_from(components)` does not build there either.
#[allow(clippy::from_over_into)]
impl<B: AsRef<[u8]>> TryInto<PublicEncryptingKey> for PublicKeyComponents<B> {
    type Error = Unspecified;

    fn try_into(self) -> Result<PublicEncryptingKey, Unspecified> {
        let components = self.rind()?;
        let key = rind::rsa::EncryptingKey::from_components(&rind::rsa::OAEP_SHA256, &components)
            .map_err(unspecified)?;
        Ok(PublicEncryptingKey::new(key.as_ref())?)
    }
}

impl<B: AsRef<[u8]>> AsDer<PublicKeyX509Der<'static>> for PublicKeyComponents<B> {
    fn as_der(&self) -> Result<PublicKeyX509Der<'static>, Unspecified> {
        let key = rind::signature::PublicKey::from_components(ANY_RSA, &self.rind()?)
            .map_err(unspecified)?;
        Ok(PublicKeyX509Der::new(key.to_spki().as_ref().to_vec()))
    }
}

/// An RSA-PSS salt length.
#[non_exhaustive]
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum RsaPssSaltLength {
    /// As long as the hash's output.
    #[default]
    Digest,
    /// The longest the modulus allows.
    Max,
    /// This many bytes.
    Custom(u16),
}

impl RsaPssSaltLength {
    /// rind's salt length, or `None` for the hash's length, which rind's
    /// `RSA_PSS_*` algorithms use.
    const fn rind(self) -> Option<rind::signature::RsaPssSaltLength> {
        match self {
            Self::Digest => None,
            Self::Max => Some(rind::signature::RsaPssSaltLength::Max),
            Self::Custom(len) => Some(rind::signature::RsaPssSaltLength::Custom(len)),
        }
    }
}

/// A PSS hash, which MGF1 also uses.
#[derive(Clone, Copy, PartialEq, Eq)]
enum PssHash {
    Sha256,
    Sha384,
    Sha512,
}

/// What an [`RsaParameters`] verifies.
#[derive(Clone, Copy)]
enum Verification {
    /// PKCS#1 v1.5, whose algorithm rind has as a static.
    Pkcs1(&'static rind::signature::RsaVerificationAlgorithm),
    /// PSS, with the salt length the parameters name.
    Pss(PssHash),
}

/// An RSA verification algorithm: a padding, a hash, a PSS salt length, and
/// the moduli it accepts, up to 8192 bits.
pub struct RsaParameters {
    verification: Verification,
    pss_salt_length: RsaPssSaltLength,
    range: RangeInclusive<u32>,
    id: &'static str,
}

impl RsaParameters {
    /// Sets the PSS salt length; PKCS#1 v1.5 has none.
    #[must_use]
    pub const fn with_pss_salt_length(mut self, saltlen: RsaPssSaltLength) -> Self {
        self.pss_salt_length = saltlen;
        self
    }

    /// The bit length of the modulus of a PKCS#1 `RSAPublicKey`.
    pub fn public_modulus_len(public_key: &[u8]) -> Result<u32, Unspecified> {
        // aws-lc-rs takes PKCS#1 alone here, which `der` checks.
        let (n, _) = der::rsa_public_key(public_key)?;
        rind_public_key(public_key)?;
        Ok(u32::try_from(der::bits(n))?)
    }

    /// The smallest modulus accepted, in bits.
    #[must_use]
    pub fn min_modulus_len(&self) -> u32 {
        *self.range.start()
    }

    /// The largest modulus accepted, in bits.
    #[must_use]
    pub fn max_modulus_len(&self) -> u32 {
        *self.range.end()
    }

    /// Calls `f` with rind's algorithm for these parameters.
    fn with_rind<R>(&self, f: impl FnOnce(&rind::signature::RsaVerificationAlgorithm) -> R) -> R {
        use rind::signature::{RsaVerificationAlgorithm as Alg, verify};
        match (self.verification, self.pss_salt_length.rind()) {
            (Verification::Pkcs1(algorithm), _) => f(algorithm),
            (Verification::Pss(PssHash::Sha256), None) => f(&verify::RSA_PSS_SHA256),
            (Verification::Pss(PssHash::Sha384), None) => f(&verify::RSA_PSS_SHA384),
            (Verification::Pss(PssHash::Sha512), None) => f(&verify::RSA_PSS_SHA512),
            (Verification::Pss(PssHash::Sha256), Some(salt)) => f(&Alg::pss_sha256(salt)),
            (Verification::Pss(PssHash::Sha384), Some(salt)) => f(&Alg::pss_sha384(salt)),
            (Verification::Pss(PssHash::Sha512), Some(salt)) => f(&Alg::pss_sha512(salt)),
        }
    }
}

impl PartialEq for RsaParameters {
    fn eq(&self, other: &Self) -> bool {
        self.id == other.id && self.pss_salt_length == other.pss_salt_length
    }
}

impl Eq for RsaParameters {}

impl fmt::Debug for RsaParameters {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{{ {}", self.id)?;
        if self.pss_salt_length != RsaPssSaltLength::Digest {
            write!(f, ", RSA-PSS salt length: {:?}", self.pss_salt_length)?;
        }
        f.write_str(" }")
    }
}

impl private::Verify for RsaParameters {
    fn parse(&self, public_key: &[u8]) -> Result<rind::signature::PublicKey, KeyRejected> {
        self.with_rind(|algorithm| rind::signature::PublicKey::new(algorithm, public_key))
            .map_err(KeyRejected::rind)
    }

    fn verify_parsed(
        &self,
        key: &rind::signature::PublicKey,
        msg: &[u8],
        signature: &[u8],
    ) -> Result<(), Unspecified> {
        key.verify(msg, signature).map_err(unspecified)
    }

    /// rind verifies RSA only over a message it hashes itself.
    fn verify_parsed_digest(
        &self,
        _: &rind::signature::PublicKey,
        _: &Digest,
        _: &[u8],
    ) -> Result<(), Unspecified> {
        Err(Unspecified)
    }
}

signature::verification_algorithm!(RsaParameters);

pub(crate) mod verification {
    use super::{PssHash, RsaParameters, RsaPssSaltLength, Verification};

    macro_rules! rsa_params {
        ($name:ident, $verification:expr, $range:expr, $doc:expr) => {
            #[doc = $doc]
            pub const $name: RsaParameters = RsaParameters {
                verification: $verification,
                pss_salt_length: RsaPssSaltLength::Digest,
                range: $range,
                id: stringify!($name),
            };
        };
    }

    use rind::signature::verify::{self, legacy};

    rsa_params!(
        RSA_PKCS1_1024_8192_SHA1_FOR_LEGACY_USE_ONLY,
        Verification::Pkcs1(&legacy::RSA_PKCS1_1024_SHA1),
        1024..=8192,
        "PKCS#1 v1.5 with SHA-1 and a modulus of 1024 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_1024_8192_SHA256_FOR_LEGACY_USE_ONLY,
        Verification::Pkcs1(&legacy::RSA_PKCS1_1024_SHA256),
        1024..=8192,
        "PKCS#1 v1.5 with SHA-256 and a modulus of 1024 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_1024_8192_SHA512_FOR_LEGACY_USE_ONLY,
        Verification::Pkcs1(&legacy::RSA_PKCS1_1024_SHA512),
        1024..=8192,
        "PKCS#1 v1.5 with SHA-512 and a modulus of 1024 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA1_FOR_LEGACY_USE_ONLY,
        Verification::Pkcs1(&legacy::RSA_PKCS1_SHA1),
        2048..=8192,
        "PKCS#1 v1.5 with SHA-1 and a modulus of 2048 to 8192 bits, for legacy protocols only."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA256,
        Verification::Pkcs1(&verify::RSA_PKCS1_SHA256),
        2048..=8192,
        "PKCS#1 v1.5 with SHA-256 and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA384,
        Verification::Pkcs1(&verify::RSA_PKCS1_SHA384),
        2048..=8192,
        "PKCS#1 v1.5 with SHA-384 and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PKCS1_2048_8192_SHA512,
        Verification::Pkcs1(&verify::RSA_PKCS1_SHA512),
        2048..=8192,
        "PKCS#1 v1.5 with SHA-512 and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PKCS1_3072_8192_SHA384,
        Verification::Pkcs1(&legacy::RSA_PKCS1_3072_SHA384),
        3072..=8192,
        "PKCS#1 v1.5 with SHA-384 and a modulus of 3072 to 8192 bits."
    );
    rsa_params!(
        RSA_PSS_2048_8192_SHA256,
        Verification::Pss(PssHash::Sha256),
        2048..=8192,
        "PSS with SHA-256, MGF1, and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PSS_2048_8192_SHA384,
        Verification::Pss(PssHash::Sha384),
        2048..=8192,
        "PSS with SHA-384, MGF1, and a modulus of 2048 to 8192 bits."
    );
    rsa_params!(
        RSA_PSS_2048_8192_SHA512,
        Verification::Pss(PssHash::Sha512),
        2048..=8192,
        "PSS with SHA-512, MGF1, and a modulus of 2048 to 8192 bits."
    );
}

pub(crate) mod signing {
    use core::fmt;

    use super::{PssHash, RsaPssSaltLength};
    use crate::sealed;

    /// What an [`RsaSignatureEncoding`] signs with.
    #[derive(Clone, Copy)]
    enum Scheme {
        Pkcs1(&'static rind::signature::RsaSigningAlgorithm),
        Pss(PssHash),
    }

    /// An RSA signature encoding: a padding, a hash, and a PSS salt length.
    pub struct RsaSignatureEncoding {
        scheme: Scheme,
        pss_salt_length: RsaPssSaltLength,
        id: &'static str,
    }

    impl RsaSignatureEncoding {
        /// Sets the PSS salt length; PKCS#1 v1.5 has none.
        #[must_use]
        pub const fn with_pss_salt_length(mut self, saltlen: RsaPssSaltLength) -> Self {
            self.pss_salt_length = saltlen;
            self
        }

        /// Calls `f` with rind's algorithm for this encoding.
        pub(crate) fn with_rind<R>(
            &self,
            f: impl FnOnce(&rind::signature::RsaSigningAlgorithm) -> R,
        ) -> R {
            use rind::signature::{RsaSigningAlgorithm as Alg, sign};
            match (self.scheme, self.pss_salt_length.rind()) {
                (Scheme::Pkcs1(algorithm), _) => f(algorithm),
                (Scheme::Pss(PssHash::Sha256), None) => f(&sign::RSA_PSS_SHA256),
                (Scheme::Pss(PssHash::Sha384), None) => f(&sign::RSA_PSS_SHA384),
                (Scheme::Pss(PssHash::Sha512), None) => f(&sign::RSA_PSS_SHA512),
                (Scheme::Pss(PssHash::Sha256), Some(salt)) => f(&Alg::pss_sha256(salt)),
                (Scheme::Pss(PssHash::Sha384), Some(salt)) => f(&Alg::pss_sha384(salt)),
                (Scheme::Pss(PssHash::Sha512), Some(salt)) => f(&Alg::pss_sha512(salt)),
            }
        }
    }

    impl sealed::Sealed for RsaSignatureEncoding {}

    /// An RSA signature encoding, for [`super::KeyPair::sign`].
    pub trait RsaEncoding: 'static + Sync + sealed::Sealed + fmt::Debug {
        /// The encoding.
        fn encoding(&'static self) -> &'static RsaSignatureEncoding;
    }

    impl RsaEncoding for RsaSignatureEncoding {
        fn encoding(&'static self) -> &'static RsaSignatureEncoding {
            self
        }
    }

    impl fmt::Debug for RsaSignatureEncoding {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, "{{ {}", self.id)?;
            if self.pss_salt_length != RsaPssSaltLength::Digest {
                write!(f, ", RSA-PSS salt length: {:?}", self.pss_salt_length)?;
            }
            f.write_str(" }")
        }
    }

    macro_rules! encoding {
        ($name:ident, $scheme:expr, $doc:expr) => {
            #[doc = $doc]
            pub const $name: RsaSignatureEncoding = RsaSignatureEncoding {
                scheme: $scheme,
                pss_salt_length: RsaPssSaltLength::Digest,
                id: stringify!($name),
            };
        };
    }

    use rind::signature::sign;

    encoding!(
        RSA_PKCS1_SHA256,
        Scheme::Pkcs1(&sign::RSA_PKCS1_SHA256),
        "PKCS#1 v1.5 signatures with SHA-256."
    );
    encoding!(
        RSA_PKCS1_SHA384,
        Scheme::Pkcs1(&sign::RSA_PKCS1_SHA384),
        "PKCS#1 v1.5 signatures with SHA-384."
    );
    encoding!(
        RSA_PKCS1_SHA512,
        Scheme::Pkcs1(&sign::RSA_PKCS1_SHA512),
        "PKCS#1 v1.5 signatures with SHA-512."
    );
    encoding!(
        RSA_PSS_SHA256,
        Scheme::Pss(PssHash::Sha256),
        "PSS signatures with SHA-256, MGF1, and a random salt."
    );
    encoding!(
        RSA_PSS_SHA384,
        Scheme::Pss(PssHash::Sha384),
        "PSS signatures with SHA-384, MGF1, and a random salt."
    );
    encoding!(
        RSA_PSS_SHA512,
        Scheme::Pss(PssHash::Sha512),
        "PSS signatures with SHA-512, MGF1, and a random salt."
    );
}

/// An RSA encryption algorithm's identifier.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum EncryptionAlgorithmId {
    /// RSA-OAEP with SHA-1 and MGF1 with SHA-1.
    OaepSha1Mgf1sha1,
    /// RSA-OAEP with SHA-256 and MGF1 with SHA-256.
    OaepSha256Mgf1sha256,
    /// RSA-OAEP with SHA-384 and MGF1 with SHA-384.
    OaepSha384Mgf1sha384,
    /// RSA-OAEP with SHA-512 and MGF1 with SHA-512.
    OaepSha512Mgf1sha512,
}

/// An RSA-OAEP algorithm: a hash, which MGF1 also uses.
pub struct OaepAlgorithm {
    id: EncryptionAlgorithmId,
    hash: &'static digest::Algorithm,
}

impl OaepAlgorithm {
    /// The algorithm's identifier.
    #[must_use]
    pub fn id(&self) -> EncryptionAlgorithmId {
        self.id
    }

    fn rind(&self) -> &'static rind::rsa::OaepAlgorithm {
        match self.id {
            EncryptionAlgorithmId::OaepSha1Mgf1sha1 => &rind::rsa::legacy::OAEP_SHA1,
            EncryptionAlgorithmId::OaepSha256Mgf1sha256 => &rind::rsa::OAEP_SHA256,
            EncryptionAlgorithmId::OaepSha384Mgf1sha384 => &rind::rsa::OAEP_SHA384,
            EncryptionAlgorithmId::OaepSha512Mgf1sha512 => &rind::rsa::OAEP_SHA512,
        }
    }

    /// The algorithm's slot in a key's per-algorithm cache.
    fn index(&self) -> usize {
        match self.id {
            EncryptionAlgorithmId::OaepSha1Mgf1sha1 => 0,
            EncryptionAlgorithmId::OaepSha256Mgf1sha256 => 1,
            EncryptionAlgorithmId::OaepSha384Mgf1sha384 => 2,
            EncryptionAlgorithmId::OaepSha512Mgf1sha512 => 3,
        }
    }
}

impl fmt::Debug for OaepAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(&self.id, f)
    }
}

/// RSA-OAEP with SHA-1 and MGF1 with SHA-1.
pub const OAEP_SHA1_MGF1SHA1: OaepAlgorithm = OaepAlgorithm {
    id: EncryptionAlgorithmId::OaepSha1Mgf1sha1,
    hash: &digest::SHA1_FOR_LEGACY_USE_ONLY,
};

/// RSA-OAEP with SHA-256 and MGF1 with SHA-256.
pub const OAEP_SHA256_MGF1SHA256: OaepAlgorithm = OaepAlgorithm {
    id: EncryptionAlgorithmId::OaepSha256Mgf1sha256,
    hash: &digest::SHA256,
};

/// RSA-OAEP with SHA-384 and MGF1 with SHA-384.
pub const OAEP_SHA384_MGF1SHA384: OaepAlgorithm = OaepAlgorithm {
    id: EncryptionAlgorithmId::OaepSha384Mgf1sha384,
    hash: &digest::SHA384,
};

/// RSA-OAEP with SHA-512 and MGF1 with SHA-512.
pub const OAEP_SHA512_MGF1SHA512: OaepAlgorithm = OaepAlgorithm {
    id: EncryptionAlgorithmId::OaepSha512Mgf1sha512,
    hash: &digest::SHA512,
};

/// Fills `cell` with `load`'s key once, returning it.
fn cached<K>(
    cell: &OnceLock<K>,
    load: impl FnOnce() -> Result<K, rind::Error>,
) -> Result<&K, Unspecified> {
    if let Some(key) = cell.get() {
        return Ok(key);
    }
    let _ = cell.set(load().map_err(unspecified)?);
    cell.get().ok_or(Unspecified)
}

struct DecryptingInner {
    /// The key as PKCS#8, from which each algorithm's key is loaded.
    pkcs8: Wiped<Vec<u8>>,
    /// The key loaded for each algorithm, by [`OaepAlgorithm::index`].
    keys: [OnceLock<rind::rsa::DecryptingKey>; 4],
    public: PublicEncryptingKey,
}

/// An RSA private key for decryption, with a modulus of 2048 to 8192 bits.
///
/// rind binds a key to one RSA-OAEP algorithm, so this loads the key for
/// each algorithm it first decrypts with, and keeps it.
#[derive(Clone)]
pub struct PrivateDecryptingKey(Arc<DecryptingInner>);

impl PrivateDecryptingKey {
    fn new(key: rind::rsa::DecryptingKey) -> Result<Self, KeyRejected> {
        let public = PublicEncryptingKey::new(key.public_key().as_ref())?;
        let keys = [const { OnceLock::new() }; 4];
        let pkcs8 = Wiped::new(key.to_pkcs8().as_ref().to_vec());
        let _ = keys[OAEP_SHA256_MGF1SHA256.index()].set(key);
        Ok(Self(Arc::new(DecryptingInner {
            pkcs8,
            keys,
            public,
        })))
    }

    /// Generates a key of `size` from the system random source.
    pub fn generate(size: KeySize) -> Result<Self, Unspecified> {
        let key = rind::rsa::DecryptingKey::generate(&rind::rsa::OAEP_SHA256, size.rind())
            .map_err(unspecified)?;
        Ok(Self::new(key)?)
    }

    /// Loads a PKCS#8 v1 RSA private key.
    pub fn from_pkcs8(pkcs8: &[u8]) -> Result<Self, KeyRejected> {
        rind::rsa::DecryptingKey::from_pkcs8(&rind::rsa::OAEP_SHA256, pkcs8)
            .map_err(KeyRejected::rind)
            .and_then(Self::new)
    }

    /// The modulus's length in bytes.
    #[must_use]
    pub fn key_size_bytes(&self) -> usize {
        self.0.public.key_size_bytes()
    }

    /// The modulus's length in bits.
    #[must_use]
    pub fn key_size_bits(&self) -> usize {
        self.0.public.key_size_bits()
    }

    /// The public key.
    #[must_use]
    pub fn public_key(&self) -> PublicEncryptingKey {
        self.0.public.clone()
    }

    fn key(&self, algorithm: &OaepAlgorithm) -> Result<&rind::rsa::DecryptingKey, Unspecified> {
        cached(&self.0.keys[algorithm.index()], || {
            rind::rsa::DecryptingKey::from_pkcs8(algorithm.rind(), &self.0.pkcs8)
        })
    }
}

impl fmt::Debug for PrivateDecryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PrivateDecryptingKey").finish()
    }
}

impl AsDer<Pkcs8V1Der<'static>> for PrivateDecryptingKey {
    fn as_der(&self) -> Result<Pkcs8V1Der<'static>, Unspecified> {
        Ok(Pkcs8V1Der::new(self.0.pkcs8.to_vec()))
    }
}

struct EncryptingInner {
    /// The key's PKCS#1 `RSAPublicKey` DER.
    der: Box<[u8]>,
    bits: usize,
    /// The key parsed for each algorithm, by [`OaepAlgorithm::index`].
    keys: [OnceLock<rind::rsa::EncryptingKey>; 4],
}

/// An RSA public key for encryption, with a modulus of 2048 to 8192 bits.
#[derive(Clone)]
pub struct PublicEncryptingKey(Arc<EncryptingInner>);

impl PublicEncryptingKey {
    /// Wraps a PKCS#1 `RSAPublicKey` that rind has already parsed.
    fn new(pkcs1: &[u8]) -> Result<Self, KeyRejected> {
        let (n, _) = der::rsa_public_key(pkcs1).map_err(|_| KeyRejected::invalid_encoding())?;
        let bits = der::bits(n);
        check_bits(bits)?;
        Ok(Self(Arc::new(EncryptingInner {
            der: pkcs1.into(),
            bits,
            keys: [const { OnceLock::new() }; 4],
        })))
    }

    /// Parses an `rsaEncryption` `SubjectPublicKeyInfo`.
    pub fn from_der(value: &[u8]) -> Result<Self, KeyRejected> {
        if !der::is_spki(value) {
            return Err(KeyRejected::invalid_encoding());
        }
        let key = rind::rsa::EncryptingKey::new(&rind::rsa::OAEP_SHA256, value)
            .map_err(KeyRejected::rind)?;
        Self::new(key.as_ref())
    }

    /// The modulus's length in bytes.
    #[must_use]
    pub fn key_size_bytes(&self) -> usize {
        self.0.bits.div_ceil(8)
    }

    /// The modulus's length in bits.
    #[must_use]
    pub fn key_size_bits(&self) -> usize {
        self.0.bits
    }

    fn key(&self, algorithm: &OaepAlgorithm) -> Result<&rind::rsa::EncryptingKey, Unspecified> {
        cached(&self.0.keys[algorithm.index()], || {
            rind::rsa::EncryptingKey::new(algorithm.rind(), &self.0.der)
        })
    }
}

impl fmt::Debug for PublicEncryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicEncryptingKey").finish()
    }
}

impl AsDer<PublicKeyX509Der<'static>> for PublicEncryptingKey {
    fn as_der(&self) -> Result<PublicKeyX509Der<'static>, Unspecified> {
        spki(&self.0.der)
    }
}

/// An RSA-OAEP public key, which encrypts with any [`OaepAlgorithm`].
pub struct OaepPublicEncryptingKey {
    public_key: PublicEncryptingKey,
}

impl OaepPublicEncryptingKey {
    /// Wraps `public_key` for RSA-OAEP.
    pub fn new(public_key: PublicEncryptingKey) -> Result<Self, Unspecified> {
        Ok(Self { public_key })
    }

    /// Encrypts `plaintext` with `algorithm` and `label` into the start of
    /// `ciphertext`, which must hold [`Self::ciphertext_size`] bytes,
    /// returning the ciphertext.
    pub fn encrypt<'ciphertext>(
        &self,
        algorithm: &'static OaepAlgorithm,
        plaintext: &[u8],
        ciphertext: &'ciphertext mut [u8],
        label: Option<&[u8]>,
    ) -> Result<&'ciphertext mut [u8], Unspecified> {
        let encrypted = self
            .public_key
            .key(algorithm)?
            .encrypt(plaintext, label.unwrap_or_default())
            .map_err(unspecified)?;
        let output = ciphertext
            .get_mut(..encrypted.as_ref().len())
            .ok_or(Unspecified)?;
        output.copy_from_slice(encrypted.as_ref());
        Ok(output)
    }

    /// The modulus's length in bytes.
    #[must_use]
    pub fn key_size_bytes(&self) -> usize {
        self.public_key.key_size_bytes()
    }

    /// The modulus's length in bits.
    #[must_use]
    pub fn key_size_bits(&self) -> usize {
        self.public_key.key_size_bits()
    }

    /// The longest plaintext `algorithm` encrypts with this key.
    #[must_use]
    pub fn max_plaintext_size(&self, algorithm: &'static OaepAlgorithm) -> usize {
        self.key_size_bytes()
            .saturating_sub(2 * algorithm.hash.output_len())
            .saturating_sub(2)
    }

    /// The ciphertext's length, the modulus's.
    #[must_use]
    pub fn ciphertext_size(&self) -> usize {
        self.key_size_bytes()
    }
}

impl fmt::Debug for OaepPublicEncryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OaepPublicEncryptingKey")
            .finish_non_exhaustive()
    }
}

/// An RSA-OAEP private key, which decrypts with any [`OaepAlgorithm`].
pub struct OaepPrivateDecryptingKey {
    private_key: PrivateDecryptingKey,
}

impl OaepPrivateDecryptingKey {
    /// Wraps `private_key` for RSA-OAEP.
    pub fn new(private_key: PrivateDecryptingKey) -> Result<Self, Unspecified> {
        Ok(Self { private_key })
    }

    /// Decrypts `ciphertext` with `algorithm` and `label` into the start of
    /// `plaintext`, which must hold [`Self::min_output_size`] bytes,
    /// returning the plaintext.
    ///
    /// A wrong key, label, or padding fails alike, and bad padding takes as
    /// long to find as good.
    pub fn decrypt<'plaintext>(
        &self,
        algorithm: &'static OaepAlgorithm,
        ciphertext: &[u8],
        plaintext: &'plaintext mut [u8],
        label: Option<&[u8]>,
    ) -> Result<&'plaintext mut [u8], Unspecified> {
        if plaintext.len() < self.min_output_size() {
            return Err(Unspecified);
        }
        let decrypted = self
            .private_key
            .key(algorithm)?
            .decrypt(ciphertext, label.unwrap_or_default())
            .map_err(unspecified)?;
        let output = &mut plaintext[..decrypted.as_ref().len()];
        output.copy_from_slice(decrypted.as_ref());
        Ok(output)
    }

    /// The modulus's length in bytes.
    #[must_use]
    pub fn key_size_bytes(&self) -> usize {
        self.private_key.key_size_bytes()
    }

    /// The modulus's length in bits.
    #[must_use]
    pub fn key_size_bits(&self) -> usize {
        self.private_key.key_size_bits()
    }

    /// The shortest `plaintext` buffer [`Self::decrypt`] takes: the
    /// modulus's length.
    #[must_use]
    pub fn min_output_size(&self) -> usize {
        self.key_size_bytes()
    }
}

impl fmt::Debug for OaepPrivateDecryptingKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("OaepPrivateDecryptingKey")
            .finish_non_exhaustive()
    }
}
