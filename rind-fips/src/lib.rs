// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
// The module builds only for glibc Linux on x86_64 and aarch64; elsewhere
// the crate is empty, and its build script says so.
#![cfg(rind_fips_module)]
#![doc = include_str!("../README.md")]
#![warn(
    clippy::undocumented_unsafe_blocks,
    elided_lifetimes_in_paths,
    missing_docs,
    unreachable_pub,
    unused_qualifications
)]

mod error;
mod ffi;

#[cfg(feature = "__acvp")]
#[doc(hidden)]
pub mod acvp;

pub use error::{Error, KeyRejected};

/// The module's name and version, as its security policy names it.
///
/// ```
/// assert!(rind_fips::version().starts_with("rind-fips "));
/// ```
pub fn version() -> &'static str {
    let mut len = 0;
    // SAFETY: `len` is writable; the string lives as long as the module,
    // which is never unloaded.
    let bytes = unsafe { core::slice::from_raw_parts(ffi::rind_fips_version(&mut len), len) };
    core::str::from_utf8(bytes).expect("the module's version is UTF-8")
}

/// Runs the module's self-tests now: the integrity test, then every
/// algorithm's known-answer test, whether it has run or not.
///
/// Each runs before its algorithm's first use anyway; this is the on-demand
/// test FIPS 140-3 asks a module to offer. A failure aborts the process,
/// naming the test, as the module's error state.
pub fn self_test() {
    // SAFETY: no arguments.
    unsafe { ffi::rind_fips_self_test() }
}

/// Cryptographic hash functions: SHA-2 and SHA-3.
///
/// ```
/// use rind_fips::digest;
///
/// let mut ctx = digest::Context::new(&digest::SHA256);
/// ctx.update(b"hello, ");
/// ctx.update(b"world");
/// assert_eq!(
///     ctx.finish().as_ref(),
///     digest::digest(&digest::SHA256, b"hello, world").as_ref(),
/// );
/// ```
pub mod digest;

/// Message authentication with HMAC.
///
/// A [`hmac::Key`] precomputes its keyed hash states once; each message then
/// signs through a [`hmac::Context`] started from it, or the one-shot
/// [`hmac::sign`] and [`hmac::verify`].
///
/// ```
/// use rind_fips::hmac;
///
/// let key = hmac::Key::new(&hmac::HMAC_SHA256, b"secret");
///
/// let mut ctx = hmac::Context::with_key(&key);
/// ctx.update(b"hello, ");
/// ctx.update(b"world");
/// let tag = ctx.sign();
///
/// hmac::verify(&key, b"hello, world", tag.as_ref()).unwrap();
/// ```
pub mod hmac;

/// Constant-time comparison, for checking a secret such as a MAC or token.
///
/// ```
/// use rind_fips::constant_time;
///
/// constant_time::verify(b"expected", b"expected").unwrap();
/// assert_eq!(
///     constant_time::verify(b"expected", b"presented"),
///     Err(rind_fips::Error::WrongLength)
/// );
/// assert_eq!(
///     constant_time::verify(b"expected", b"Expected"),
///     Err(rind_fips::Error::NotEqual)
/// );
/// ```
pub mod constant_time {
    use crate::{Error, ffi};

    /// Checks that `a` and `b` are equal in constant time, failing with
    /// [`Error::WrongLength`] if their lengths differ and
    /// [`Error::NotEqual`] if their contents do.
    pub fn verify(a: &[u8], b: &[u8]) -> Result<(), Error> {
        // SAFETY: both are readable for their lengths.
        ffi::check(unsafe {
            ffi::rind_fips_constant_time_verify(a.as_ptr(), a.len(), b.as_ptr(), b.len())
        })
    }
}

/// Key derivation with HKDF.
///
/// A [`hkdf::Salt`] extracts a [`hkdf::Prk`] from a secret, which then expands
/// into any number of keys, each exactly as long as what it becomes.
///
/// ```
/// # fn main() -> Result<(), rind_fips::Error> {
/// use rind_fips::{aead, hkdf, hmac};
///
/// let prk = hkdf::Salt::new(&hkdf::HKDF_SHA256, b"salt").extract(b"input key material")?;
///
/// let aead_key = aead::Key::from(prk.expand(&[b"aead"], &aead::AES_256_GCM)?);
/// let hmac_key = hmac::Key::from(prk.expand(&[b"hmac"], &hmac::HMAC_SHA256)?);
///
/// let info: [&[u8]; 2] = [b"label", b"context"];
/// let mut bytes = [0u8; 16];
/// prk.fill(&info, &mut bytes)?;
/// # Ok(())
/// # }
/// ```
pub mod hkdf;

/// Password-based key derivation with PBKDF2.
///
/// A [`pbkdf2::Secret`] keys HMAC with a password once, then derives a key
/// for a salt and iteration count, or checks one derived before. Only what
/// SP 800-132 approves derives: a password of at least 14 bytes, a salt of
/// at least 16, at least 1000 iterations, and a key of at least 14 bytes.
/// This example takes the iteration count OWASP suggests for SHA-256, so it
/// is not run as a test.
///
/// ```no_run
/// use std::num::NonZeroU32;
///
/// use rind_fips::pbkdf2;
///
/// let iterations = NonZeroU32::new(600_000).unwrap();
/// let secret = pbkdf2::Secret::new(&pbkdf2::PBKDF2_HMAC_SHA256, b"correct horse battery");
///
/// let mut stored = [0u8; 32];
/// secret
///     .derive(iterations, b"a per-user salt!", &mut stored)
///     .unwrap();
///
/// secret
///     .verify(iterations, b"a per-user salt!", &stored)
///     .unwrap();
/// ```
pub mod pbkdf2;

/// Authenticated encryption with AES-GCM.
///
/// FIPS 140-3 approves AES-GCM encryption only under an IV the module
/// generates, so the caller never picks a nonce to seal under. A
/// [`aead::RandomizedNonceKey`] draws each from the module's DRBG, and a
/// [`aead::TlsRecordSealingKey`] seals TLS 1.3 records, whose sequence
/// numbers it checks. An [`aead::Key`] opens what a peer sealed under its
/// nonces, TLS 1.3 records included: opening one checks nothing more, so
/// there is no `TlsRecordOpeningKey`.
///
/// ```
/// use rind_fips::aead::*;
///
/// let key = RandomizedNonceKey::new(&AES_256_GCM, &[0x42; 32]).unwrap();
/// let mut in_out = b"hello".to_vec();
/// let nonce = key
///     .seal_in_place_append_tag(b"header", &mut in_out)
///     .unwrap();
/// let plaintext = key.open_in_place(nonce, b"header", &mut in_out).unwrap();
/// assert_eq!(plaintext, b"hello");
///
/// let key = Key::new(&AES_128_GCM, &[0; 16]).unwrap();
///
/// // A block of zeros, sealed elsewhere: McGrew and Viega's test case 2.
/// let mut in_out = [
///     0x03, 0x88, 0xda, 0xce, 0x60, 0xb6, 0xa3, 0x92, 0xf3, 0x28, 0xc2, 0xb9, 0x71, 0xb2, 0xfe,
///     0x78, 0xab, 0x6e, 0x47, 0xd4, 0x2c, 0xec, 0x13, 0xbd, 0xf5, 0x3a, 0x67, 0xb2, 0x12, 0x57,
///     0xbd, 0xdf,
/// ];
/// let nonce = Nonce::assume_unique_for_key([0; 12]);
/// let plaintext = key.open_in_place(nonce, b"", &mut in_out).unwrap();
/// assert_eq!(plaintext, [0; 16]);
/// ```
pub mod aead;

/// Unauthenticated ciphers, for protocols that specify one alongside their own integrity protection.
///
/// Prefer [`aead`] unless a protocol requires one of these. Decrypting
/// AES-CBC before verifying a MAC over its ciphertext is a padding oracle.
pub mod cipher;

mod aes_kw;

/// Key wrapping with AES-KW, RFC 3394, as WebCrypto's `AES-KW` and JWE's
/// `A128KW`, `A192KW`, and `A256KW` use it, and with AES-KWP, RFC 5649,
/// which pads keys of any length.
///
/// A key-encryption key wraps in either [`Mode`](key_wrap::Mode), chosen
/// per call.
///
/// ```
/// use rind_fips::key_wrap::{AES_256, AesKek, Mode};
///
/// let kek = AesKek::new(&AES_256, &[0x42; 32]).unwrap();
/// let key = [0x24; 16];
/// let mut wrapped = [0u8; 24];
/// kek.wrap_key(Mode::Kw, &key, &mut wrapped).unwrap();
/// let mut unwrapped = [0u8; 16];
/// assert_eq!(
///     kek.unwrap_key(Mode::Kw, &wrapped, &mut unwrapped).unwrap(),
///     key
/// );
///
/// let key = [0x24; 20];
/// let mut wrapped = [0u8; 32];
/// kek.wrap_key(Mode::Kwp, &key, &mut wrapped).unwrap();
/// let mut unwrapped = [0u8; 24];
/// assert_eq!(
///     kek.unwrap_key(Mode::Kwp, &wrapped, &mut unwrapped).unwrap(),
///     key
/// );
/// ```
pub mod key_wrap {
    pub use crate::aes_kw::{AesKek, Mode};
    pub use crate::cipher::{AES_128, AES_192, AES_256};
}

mod signature;

/// ECDSA signatures on P-256, P-384, and P-521.
///
/// A key pair signs with an [`ecdsa::sign`] algorithm, and its public key,
/// or a peer's parsed for an [`ecdsa::verify`] algorithm, verifies:
///
/// ```
/// # fn main() -> Result<(), rind_fips::Error> {
/// use rind_fips::ecdsa::{KeyPair, PublicKey, sign, verify};
///
/// let key_pair = KeyPair::generate(&sign::P256_SHA256_ASN1)?;
/// let signature = key_pair.sign(b"hello")?;
///
/// let encoded = key_pair.public_key().as_ref();
/// let public_key = PublicKey::new(&verify::P256_SHA256_ASN1, encoded)?;
/// public_key.verify(b"hello", signature.as_ref())?;
/// # Ok(())
/// # }
/// ```
pub mod ecdsa {
    pub use crate::signature::ecdsa::{
        KeyPair, PublicKey, Scalar, Signature, SigningAlgorithm, VerificationAlgorithm,
    };

    /// Algorithms a key pair signs with.
    ///
    /// Each signs as the [`verify`] algorithm of the same name verifies.
    pub mod sign {
        pub use crate::signature::ecdsa::sign::{
            P256_SHA256_ASN1, P256_SHA256_FIXED, P384_SHA384_ASN1, P384_SHA384_FIXED,
            P521_SHA512_ASN1, P521_SHA512_FIXED,
        };
    }

    /// Algorithms a public key verifies with.
    pub mod verify {
        pub use crate::signature::ecdsa::verify::{
            P256_SHA256_ASN1, P256_SHA256_FIXED, P256_SHA384_ASN1, P256_SHA512_ASN1,
            P384_SHA256_ASN1, P384_SHA384_ASN1, P384_SHA384_FIXED, P384_SHA512_ASN1,
            P521_SHA256_ASN1, P521_SHA384_ASN1, P521_SHA512_ASN1, P521_SHA512_FIXED,
        };
    }
}

/// Ed25519 signatures ([RFC 8032]).
///
/// ```
/// # fn main() -> Result<(), rind_fips::Error> {
/// use rind_fips::ed25519::{KeyPair, PublicKey};
///
/// let key_pair = KeyPair::generate()?;
/// let signature = key_pair.sign(b"hello");
///
/// let public_key = PublicKey::new(key_pair.public_key().as_ref())?;
/// public_key.verify(b"hello", signature.as_ref())?;
/// # Ok(())
/// # }
/// ```
///
/// [RFC 8032]: https://www.rfc-editor.org/rfc/rfc8032.html
pub mod ed25519 {
    pub use crate::signature::ed25519::{KeyPair, PublicKey, Seed, Signature};
}

/// ML-DSA signatures (FIPS 204): ML-DSA-44, ML-DSA-65, and ML-DSA-87, pure
/// with the empty context.
///
/// The parameter set is a type, so a key of one set fails to compile where
/// another's is expected, and a signature is a fixed-size array.
///
/// ```
/// # fn main() -> Result<(), rind_fips::Error> {
/// use rind_fips::ml_dsa::{KeyPair, MlDsa65, PublicKey};
///
/// let key_pair = KeyPair::<MlDsa65>::generate()?;
/// let signature = key_pair.sign(b"hello")?;
///
/// let public_key = PublicKey::<MlDsa65>::new(key_pair.public_key().as_ref())?;
/// public_key.verify(b"hello", signature.as_ref())?;
/// # Ok(())
/// # }
/// ```
pub mod ml_dsa {
    pub use crate::signature::ml_dsa::{
        KeyPair, MlDsa44, MlDsa65, MlDsa87, ParameterSet, PublicKey, Seed, Signature,
    };
}

/// RSA signatures: PKCS#1 v1.5 and PSS.
///
/// A [`KeyPair`](rsa::KeyPair) signs with any [`rsa::sign`] algorithm, and
/// a [`PublicKey`](rsa::PublicKey) verifies with any [`rsa::verify`]
/// algorithm whose floor its modulus meets: neither is bound to a padding,
/// as TLS picks one per handshake.
///
/// ```
/// # fn main() -> Result<(), rind_fips::Error> {
/// use rind_fips::rsa::{KeyPair, KeySize, PublicKey, sign, verify};
///
/// let key_pair = KeyPair::generate(KeySize::Rsa2048)?;
/// let signature = key_pair.sign(&sign::PSS_SHA256, b"hello")?;
///
/// let public_key = PublicKey::new(key_pair.public_key().as_ref())?;
/// public_key.verify(&verify::PSS_SHA256, b"hello", signature.as_ref())?;
/// # Ok(())
/// # }
/// ```
///
/// RSA-OAEP is in `rind` alone, outside the module. RSA-PSS takes only a
/// salt as long as its hash, which is all FIPS 140-3's tested
/// configurations approve, so neither a custom salt length nor any-salt
/// verification is here:
///
/// ```compile_fail
/// use rind_fips::rsa::verify::PSS_SHA256_ANY_SALT;
/// ```
///
/// ```compile_fail
/// use rind_fips::rsa::PssSaltLength;
/// ```
pub mod rsa {
    pub use crate::signature::rsa::{
        KeyPair, KeySize, PublicKey, PublicKeyComponents, Signature, SigningAlgorithm,
        VerificationAlgorithm,
    };

    /// Algorithms a key pair signs with.
    ///
    /// They sign with moduli of an even number of bits from 2048 to 8192,
    /// and RSA-PSS with a salt as long as its hash, the length aws-lc's
    /// module approves.
    pub mod sign {
        pub use crate::signature::rsa::sign::{
            PKCS1_SHA256, PKCS1_SHA384, PKCS1_SHA512, PSS_SHA256, PSS_SHA384, PSS_SHA512,
        };
    }

    /// Algorithms a public key verifies with, for moduli of an even number
    /// of bits from 2048 to 8192.
    pub mod verify {
        pub use crate::signature::rsa::verify::{
            PKCS1_SHA256, PKCS1_SHA384, PKCS1_SHA512, PSS_SHA256, PSS_SHA384, PSS_SHA512,
        };

        /// Algorithms with another modulus floor, or SHA-1, for old keys
        /// and signatures, as SP 800-131A approves them for verifying only:
        /// a 1024-bit modulus, but none between it and 2048 bits.
        pub mod legacy {
            pub use crate::signature::rsa::verify::legacy::{
                PKCS1_1024_SHA1, PKCS1_1024_SHA256, PKCS1_1024_SHA512, PKCS1_3072_SHA384,
                PKCS1_SHA1,
            };
        }
    }
}

/// Encoded keys: PKCS#8 and SEC1 private keys, and `SubjectPublicKeyInfo`
/// public keys.
///
/// Every key type that exports itself returns these, whatever its module.
pub mod encoding;

/// Key agreement: ECDH on P-256, P-384, and P-521.
///
/// A shared secret is not uniformly random, so derive keys from it with a KDF
/// such as [`hkdf`] rather than using its bytes directly.
///
/// ```
/// use rind_fips::agreement::*;
/// use rind_fips::hkdf;
///
/// let alice = PrivateKey::generate(&ECDH_P256).unwrap();
/// let bob = PrivateKey::generate(&ECDH_P256).unwrap();
///
/// let alice_pub = alice.public_key();
/// let bob_pub = bob.public_key();
///
/// let alice_secret = alice
///     .agree(bob_pub.as_ref())
///     .expect("bob gave an invalid public key");
/// let bob_secret = bob
///     .agree(alice_pub.as_ref())
///     .expect("alice gave an invalid public key");
///
/// // Each side derives the same key from its secret and the handshake's salt.
/// let salt = hkdf::Salt::new(&hkdf::HKDF_SHA256, b"handshake salt");
/// let mut alice_key = [0u8; 32];
/// let mut bob_key = [0u8; 32];
/// salt.extract(alice_secret.as_ref())
///     .and_then(|prk| prk.fill(&[b"key"], &mut alice_key))
///     .unwrap();
/// salt.extract(bob_secret.as_ref())
///     .and_then(|prk| prk.fill(&[b"key"], &mut bob_key))
///     .unwrap();
/// assert_eq!(alice_key, bob_key);
/// ```
pub mod agreement;

/// Key encapsulation: ML-KEM-512, ML-KEM-768, and ML-KEM-1024.
///
/// Each type names its parameter set, so a ciphertext of one set fails to
/// compile against a key of another.
///
/// ```
/// # fn main() -> Result<(), rind_fips::Error> {
/// use rind_fips::kem::*;
///
/// // The recipient generates a key pair, and sends the encapsulation key to
/// // the sender.
/// let decapsulation_key = DecapsulationKey::<MlKem768>::generate()?;
/// let encapsulation_key = decapsulation_key.public_key();
///
/// // The sender parses the encapsulation key, encapsulates a fresh secret,
/// // and sends the ciphertext back to the recipient.
/// let peer_key = EncapsulationKey::<MlKem768>::new(encapsulation_key.as_ref())?;
/// let (ciphertext, sender_secret) = peer_key.encapsulate()?;
///
/// // The recipient parses the ciphertext and decapsulates it, recovering the
/// // same secret.
/// let ciphertext = Ciphertext::<MlKem768>::new(ciphertext.as_ref())?;
/// let recipient_secret = decapsulation_key.decapsulate(&ciphertext);
///
/// // Each side derives its keys from the secret with a KDF.
/// let salt = rind_fips::hkdf::Salt::new(&rind_fips::hkdf::HKDF_SHA256, b"session salt");
/// let mut sender_key = [0u8; 32];
/// let mut recipient_key = [0u8; 32];
/// salt.extract(sender_secret.as_ref())?
///     .fill(&[b"key"], &mut sender_key)?;
/// salt.extract(recipient_secret.as_ref())?
///     .fill(&[b"key"], &mut recipient_key)?;
/// assert_eq!(sender_key, recipient_key);
/// # Ok(())
/// # }
/// ```
pub mod kem;

/// Random bytes from the module's SP 800-90A DRBG, seeded from the system.
///
/// ```
/// let mut nonce = [0u8; 16];
/// rind_fips::rand::fill(&mut nonce).unwrap();
/// ```
pub mod rand {
    use crate::{Error, ffi};

    /// Fills the entirety of `out` with random bytes.
    pub fn fill(out: &mut [u8]) -> Result<(), Error> {
        // SAFETY: `out` is writable for its length.
        ffi::check(unsafe { ffi::rind_fips_rand_fill(out.as_mut_ptr(), out.len()) })
    }
}

/// CPU support.
///
/// The module requires AES, carry-less multiplication, and, on x86_64, the
/// AVX2 generation's integer instructions, and refuses to load on a CPU
/// without them, naming the first one missing.
pub mod cpu;
