// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

use core::fmt;

use super::{Buffer, HashId, Key, PublicKeyHandle, load, pkcs8};
use crate::Error;
use crate::encoding::{Pkcs8, Spki};
use crate::ffi::{self, Handle, Status, ids, opaque};

opaque! {
    RsaHandle => rind_fips_rsa_free,
}

unsafe extern "C" {
    fn rind_fips_rsa_public_key_new(
        der: *const u8,
        len: usize,
        out: *mut *mut PublicKeyHandle,
    ) -> Status;
    fn rind_fips_rsa_public_key_from_spki(
        der: *const u8,
        len: usize,
        out: *mut *mut PublicKeyHandle,
    ) -> Status;
    fn rind_fips_rsa_public_key_from_components(
        n: *const u8,
        n_len: usize,
        e: *const u8,
        e_len: usize,
        out: *mut *mut PublicKeyHandle,
    ) -> Status;
    fn rind_fips_rsa_public_key_modulus_len(key: *const PublicKeyHandle) -> usize;
    fn rind_fips_rsa_public_key_verify(
        key: *const PublicKeyHandle,
        id: u32,
        message: *const u8,
        len: usize,
        signature: *const u8,
        signature_len: usize,
    ) -> Status;
    fn rind_fips_rsa_generate(size: u32, out: *mut *mut RsaHandle) -> Status;
    fn rind_fips_rsa_from_pkcs8(der: *const u8, len: usize, out: *mut *mut RsaHandle) -> Status;
    fn rind_fips_rsa_from_pkcs1(der: *const u8, len: usize, out: *mut *mut RsaHandle) -> Status;
    fn rind_fips_rsa_public_key(key: *const RsaHandle) -> *mut PublicKeyHandle;
    fn rind_fips_rsa_sign(
        key: *const RsaHandle,
        id: u32,
        message: *const u8,
        len: usize,
        out: *mut u8,
        cap: usize,
        out_len: *mut usize,
    ) -> Status;
    fn rind_fips_rsa_to_pkcs8(key: *const RsaHandle) -> *mut ffi::Encoded;
}

/// The modulus size of an RSA key pair to generate.
#[derive(Clone, Copy, Debug, PartialEq)]
#[non_exhaustive]
pub enum KeySize {
    /// A 2048-bit modulus.
    Rsa2048,
    /// A 3072-bit modulus.
    Rsa3072,
    /// A 4096-bit modulus.
    Rsa4096,
    /// A 6144-bit modulus.
    Rsa6144,
    /// An 8192-bit modulus.
    Rsa8192,
}

impl KeySize {
    fn id(self) -> u32 {
        use ids::rsa_size::*;
        match self {
            Self::Rsa2048 => RSA_2048,
            Self::Rsa3072 => RSA_3072,
            Self::Rsa4096 => RSA_4096,
            Self::Rsa6144 => RSA_6144,
            Self::Rsa8192 => RSA_8192,
        }
    }
}

/// An RSA public key as its big-endian modulus and exponent, as a JWK
/// carries it, rather than DER.
#[derive(Clone, Copy, Debug)]
pub struct PublicKeyComponents<B> {
    /// The modulus, without leading zero bytes.
    pub n: B,
    /// The public exponent, without leading zero bytes.
    pub e: B,
}

// What the algorithms are, as rind's `Debug` shows them.

/// How long an RSASSA-PSS salt is: always the hash's length here.
#[derive(Clone, Copy, Debug, PartialEq)]
enum PssSalt {
    Hash,
}

#[derive(Clone, Copy, Debug, PartialEq)]
enum RsaPadding {
    /// RSASSA-PKCS1-v1_5.
    Pkcs1,
    /// RSASSA-PSS, with MGF1 on the same hash and a salt of this length.
    Pss(PssSalt),
}

#[derive(Clone, Copy, Debug)]
#[allow(dead_code, reason = "only `Debug` reads it, as rind's")]
struct RsaScheme {
    padding: RsaPadding,
    hash: HashId,
}

impl RsaScheme {
    const fn pkcs1(hash: HashId) -> Self {
        Self {
            padding: RsaPadding::Pkcs1,
            hash,
        }
    }

    const fn pss(hash: HashId) -> Self {
        Self {
            padding: RsaPadding::Pss(PssSalt::Hash),
            hash,
        }
    }
}

/// What an RSA verification algorithm verifies: a scheme rind-fips also
/// signs with, or PKCS#1 v1.5 with SHA-1, which it only verifies.
#[derive(Clone, Copy, Debug)]
#[allow(dead_code, reason = "only `Debug` reads it, as rind's")]
enum RsaVerification {
    Scheme(RsaScheme),
    Pkcs1Sha1,
}

/// An RSA verification algorithm: a padding, a hash, and the smallest
/// modulus it accepts, for [`PublicKey::verify`].
pub struct VerificationAlgorithm {
    id: u32,
    verification: RsaVerification,
    min_bits: usize,
}

impl fmt::Debug for VerificationAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("VerificationAlgorithm")
            .field("verification", &self.verification)
            .field("min_bits", &self.min_bits)
            .finish()
    }
}

/// An RSA signing algorithm: a padding and a hash, for [`KeyPair::sign`].
pub struct SigningAlgorithm {
    id: u32,
    scheme: RsaScheme,
}

impl fmt::Debug for SigningAlgorithm {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("SigningAlgorithm")
            .field(&self.scheme)
            .finish()
    }
}

/// An RSA public key, with a modulus of an even number of bits from 2048 to
/// 8192, or of 1024 bits, which verifies with any [`VerificationAlgorithm`]
/// whose floor it meets.
///
/// Its bytes are its PKCS#1 `RSAPublicKey` DER, however it was loaded.
#[derive(Clone)]
pub struct PublicKey(Key);

impl PublicKey {
    /// Parses a PKCS#1 `RSAPublicKey`, refusing a malformed key before any
    /// signature arrives, and one whose modulus FIPS 186-5 approves for no
    /// algorithm: of an odd number of bits, or under 2048 bits but for the
    /// [`verify::legacy`] algorithms' 1024.
    ///
    /// [`verify::legacy`]: crate::rsa::verify::legacy
    pub fn new(der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        Key::parse(|out| unsafe { rind_fips_rsa_public_key_new(der.as_ptr(), der.len(), out) })
            .map(Self)
    }

    /// Parses a public key from its `SubjectPublicKeyInfo` DER, naming
    /// `rsaEncryption`, `id-RSAES-OAEP`, or `id-ea-rsa` with `NULL`
    /// parameters or none, refusing a modulus as [`Self::new`] does.
    pub fn from_spki(der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        Key::parse(|out| unsafe {
            rind_fips_rsa_public_key_from_spki(der.as_ptr(), der.len(), out)
        })
        .map(Self)
    }

    /// Loads a public key from its big-endian modulus and exponent, as a
    /// JWK carries them, refusing a modulus as [`Self::new`] does.
    pub fn from_components(
        components: &PublicKeyComponents<impl AsRef<[u8]>>,
    ) -> Result<Self, Error> {
        let (n, e) = (components.n.as_ref(), components.e.as_ref());
        Key::parse(|out| {
            // SAFETY: `n` and `e` are readable, and `out` writable.
            unsafe {
                rind_fips_rsa_public_key_from_components(
                    n.as_ptr(),
                    n.len(),
                    e.as_ptr(),
                    e.len(),
                    out,
                )
            }
        })
        .map(Self)
    }

    /// Encodes the public key as a `SubjectPublicKeyInfo` naming
    /// `rsaEncryption`.
    pub fn to_spki(&self) -> Spki {
        self.0.to_spki()
    }

    /// The modulus's length in bytes, which is also its signatures' length,
    /// so a caller can refuse a small key before it verifies anything.
    pub fn modulus_len(&self) -> usize {
        // SAFETY: the handle is live.
        unsafe { rind_fips_rsa_public_key_modulus_len(self.0.ptr()) }
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
        // SAFETY: the handle is live, and `message` and `signature`
        // readable.
        ffi::check(unsafe {
            rind_fips_rsa_public_key_verify(
                self.0.ptr(),
                algorithm.id,
                message.as_ptr(),
                message.len(),
                signature.as_ptr(),
                signature.len(),
            )
        })
    }
}

impl AsRef<[u8]> for PublicKey {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for PublicKey {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("PublicKey").field(&self.as_ref()).finish()
    }
}

/// An RSA signature, as long as the modulus.
#[derive(Clone, Copy)]
pub struct Signature(Buffer<SIGNATURE_MAX_LEN>);

/// The largest modulus's length, 8192 bits.
const SIGNATURE_MAX_LEN: usize = 1024;

impl AsRef<[u8]> for Signature {
    fn as_ref(&self) -> &[u8] {
        self.0.bytes()
    }
}

impl fmt::Debug for Signature {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("Signature").field(&self.as_ref()).finish()
    }
}

/// A two-prime RSA private key, with a modulus of an even number of bits
/// from 2048 to 8192, and its public key; held in the module, which wipes
/// it on drop.
pub struct KeyPair {
    handle: Handle<RsaHandle>,
    public: PublicKey,
}

impl KeyPair {
    fn load(load_with: impl FnOnce(*mut *mut RsaHandle) -> Status) -> Result<Self, Error> {
        let handle = load(load_with)?;
        // SAFETY: the handle is live.
        let public = unsafe { rind_fips_rsa_public_key(handle.ptr()) };
        Ok(Self {
            handle,
            public: PublicKey(Key::from_handle(public)),
        })
    }

    /// Generates a key pair of `size` from the module's random generator,
    /// then checks that it signs what its public key verifies.
    ///
    /// This is slow: about 30 milliseconds for 2048 bits, and 15 seconds or
    /// more for 8192 bits, with no upper bound. Its timing reveals only which
    /// candidate primes it discards.
    pub fn generate(size: KeySize) -> Result<Self, Error> {
        // SAFETY: `out` is writable.
        Self::load(|out| unsafe { rind_fips_rsa_generate(size.id(), out) })
    }

    /// Loads a PKCS#8 v1 RSA private key, named `rsaEncryption`,
    /// `id-RSAES-OAEP`, or `id-ea-rsa`.
    pub fn from_pkcs8(der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        Self::load(|out| unsafe { rind_fips_rsa_from_pkcs8(der.as_ptr(), der.len(), out) })
    }

    /// Loads a PKCS#1 `RSAPrivateKey`.
    pub fn from_pkcs1(der: &[u8]) -> Result<Self, Error> {
        // SAFETY: `der` is readable, and `out` writable.
        Self::load(|out| unsafe { rind_fips_rsa_from_pkcs1(der.as_ptr(), der.len(), out) })
    }

    /// Returns the public key, which verifies what this key pair signs.
    pub fn public_key(&self) -> &PublicKey {
        &self.public
    }

    /// Signs `message` with `algorithm`, as long as the modulus.
    pub fn sign(&self, algorithm: &SigningAlgorithm, message: &[u8]) -> Result<Signature, Error> {
        Buffer::write(|out, cap, len| {
            // SAFETY: the handle is live, `message` readable, `out` writable
            // for `cap`, and `len` writable.
            unsafe {
                rind_fips_rsa_sign(
                    self.handle.ptr(),
                    algorithm.id,
                    message.as_ptr(),
                    message.len(),
                    out,
                    cap,
                    len,
                )
            }
        })
        .map(Signature)
    }

    /// Encodes the private key as PKCS#8.
    pub fn to_pkcs8(&self) -> Pkcs8 {
        // SAFETY: the handle is live.
        pkcs8(unsafe { rind_fips_rsa_to_pkcs8(self.handle.ptr()) })
    }
}

impl fmt::Debug for KeyPair {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("KeyPair")
            .field("public_key", &self.public.as_ref())
            .finish_non_exhaustive()
    }
}

/// Algorithms a key pair signs with.
pub(crate) mod sign {
    use super::{HashId, RsaScheme, SigningAlgorithm};
    use crate::ffi::ids::signature as id;

    const fn signing(id: u32, scheme: RsaScheme) -> SigningAlgorithm {
        SigningAlgorithm { id, scheme }
    }

    /// RSASSA-PKCS1-v1_5 with SHA-256.
    pub static PKCS1_SHA256: SigningAlgorithm =
        signing(id::RSA_PKCS1_SHA256, RsaScheme::pkcs1(HashId::Sha256));

    /// RSASSA-PKCS1-v1_5 with SHA-384.
    pub static PKCS1_SHA384: SigningAlgorithm =
        signing(id::RSA_PKCS1_SHA384, RsaScheme::pkcs1(HashId::Sha384));

    /// RSASSA-PKCS1-v1_5 with SHA-512.
    pub static PKCS1_SHA512: SigningAlgorithm =
        signing(id::RSA_PKCS1_SHA512, RsaScheme::pkcs1(HashId::Sha512));

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a 32-byte salt.
    pub static PSS_SHA256: SigningAlgorithm =
        signing(id::RSA_PSS_SHA256, RsaScheme::pss(HashId::Sha256));

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a 48-byte salt.
    pub static PSS_SHA384: SigningAlgorithm =
        signing(id::RSA_PSS_SHA384, RsaScheme::pss(HashId::Sha384));

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a 64-byte salt.
    pub static PSS_SHA512: SigningAlgorithm =
        signing(id::RSA_PSS_SHA512, RsaScheme::pss(HashId::Sha512));
}

/// Algorithms a public key verifies with.
pub(crate) mod verify {
    use super::{HashId, RsaScheme, RsaVerification, VerificationAlgorithm};
    use crate::ffi::ids::signature as id;

    const fn verification(id: u32, scheme: RsaScheme, min_bits: usize) -> VerificationAlgorithm {
        VerificationAlgorithm {
            id,
            verification: RsaVerification::Scheme(scheme),
            min_bits,
        }
    }

    /// RSASSA-PKCS1-v1_5 with SHA-256, for moduli of 2048 to 8192 bits.
    pub static PKCS1_SHA256: VerificationAlgorithm =
        verification(id::RSA_PKCS1_SHA256, RsaScheme::pkcs1(HashId::Sha256), 2048);

    /// RSASSA-PKCS1-v1_5 with SHA-384, for moduli of 2048 to 8192 bits.
    pub static PKCS1_SHA384: VerificationAlgorithm =
        verification(id::RSA_PKCS1_SHA384, RsaScheme::pkcs1(HashId::Sha384), 2048);

    /// RSASSA-PKCS1-v1_5 with SHA-512, for moduli of 2048 to 8192 bits.
    pub static PKCS1_SHA512: VerificationAlgorithm =
        verification(id::RSA_PKCS1_SHA512, RsaScheme::pkcs1(HashId::Sha512), 2048);

    /// RSASSA-PSS with SHA-256, MGF1-SHA-256, and a 32-byte salt, for moduli of 2048 to 8192 bits.
    pub static PSS_SHA256: VerificationAlgorithm =
        verification(id::RSA_PSS_SHA256, RsaScheme::pss(HashId::Sha256), 2048);

    /// RSASSA-PSS with SHA-384, MGF1-SHA-384, and a 48-byte salt, for moduli of 2048 to 8192 bits.
    pub static PSS_SHA384: VerificationAlgorithm =
        verification(id::RSA_PSS_SHA384, RsaScheme::pss(HashId::Sha384), 2048);

    /// RSASSA-PSS with SHA-512, MGF1-SHA-512, and a 64-byte salt, for moduli of 2048 to 8192 bits.
    pub static PSS_SHA512: VerificationAlgorithm =
        verification(id::RSA_PSS_SHA512, RsaScheme::pss(HashId::Sha512), 2048);

    /// Algorithms with another modulus floor, or SHA-1, for old keys and
    /// signatures.
    pub(crate) mod legacy {
        use super::super::RsaVerification;
        use super::{HashId, RsaScheme, VerificationAlgorithm, id, verification};

        const fn sha1(id: u32, min_bits: usize) -> VerificationAlgorithm {
            VerificationAlgorithm {
                id,
                verification: RsaVerification::Pkcs1Sha1,
                min_bits,
            }
        }

        /// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures only: SHA-1 collisions are practical.
        pub static PKCS1_SHA1: VerificationAlgorithm = sha1(id::RSA_PKCS1_SHA1, 2048);

        /// RSASSA-PKCS1-v1_5 with SHA-1, for old signatures by keys with 1024-bit moduli too.
        pub static PKCS1_1024_SHA1: VerificationAlgorithm = sha1(id::RSA_PKCS1_1024_SHA1, 1024);

        /// RSASSA-PKCS1-v1_5 with SHA-256, for old keys with 1024-bit moduli too.
        pub static PKCS1_1024_SHA256: VerificationAlgorithm = verification(
            id::RSA_PKCS1_1024_SHA256,
            RsaScheme::pkcs1(HashId::Sha256),
            1024,
        );

        /// RSASSA-PKCS1-v1_5 with SHA-512, for old keys with 1024-bit moduli too.
        pub static PKCS1_1024_SHA512: VerificationAlgorithm = verification(
            id::RSA_PKCS1_1024_SHA512,
            RsaScheme::pkcs1(HashId::Sha512),
            1024,
        );

        /// RSASSA-PKCS1-v1_5 with SHA-384, for moduli of 3072 to 8192 bits.
        pub static PKCS1_3072_SHA384: VerificationAlgorithm = verification(
            id::RSA_PKCS1_3072_SHA384,
            RsaScheme::pkcs1(HashId::Sha384),
            3072,
        );
    }
}
