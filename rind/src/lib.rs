// Written for Graviola by Joe Birr-Pixton, 2024.
// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
#![doc = include_str!("../README.md")]
#![allow(
    clippy::new_without_default,
    clippy::result_unit_err,
    clippy::too_many_arguments
)]
#![forbid(unused_must_use)]
#![warn(
    clippy::alloc_instead_of_core,
    clippy::let_underscore_must_use,
    clippy::ptr_as_ptr,
    clippy::ptr_cast_constness,
    clippy::std_instead_of_core,
    clippy::undocumented_unsafe_blocks,
    clippy::upper_case_acronyms,
    clippy::use_self,
    elided_lifetimes_in_paths,
    missing_docs,
    trivial_numeric_casts,
    unreachable_pub,
    unused_import_braces,
    unused_extern_crates,
    unused_qualifications
)]
#![cfg_attr(coverage_nightly, feature(coverage_attribute))]

/// Low level operations.
///
/// `unsafe` is allowed only here.
///
/// Examples: elliptic curve field operations,
/// bignum arithmetic.
mod low;

/// Mid-level APIs.
///
/// Examples: elliptic curve group operations.
mod mid;

/// High-level APIs.
///
/// Examples: key encodings, high-level constructions.
mod high;

/// Errors.  Common to all layers.
mod error;

/// The FIPS module's random generator, which [`mid::rng`] draws from in the
/// module's build.
#[cfg(any(test, rind_fips))]
mod fips_rng;

/// Test infrastructure.
#[cfg(test)]
#[cfg_attr(coverage_nightly, coverage(off))]
mod test;

// vvv Public API
pub use error::{Error, KeyRejected};

/// Non-API documentation
#[cfg(doc)]
pub mod doc {
    pub use super::low::inline_assembly_safety;
}

/// Key agreement: X25519, and ECDH on P-256, P-384, and P-521.
///
/// A shared secret is not uniformly random, so derive keys from it with a KDF
/// such as [`hkdf`] rather than using its bytes directly.
///
/// ```
/// use rind::agreement::*;
/// use rind::hkdf;
///
/// let alice = PrivateKey::generate(&X25519).unwrap();
/// let bob = PrivateKey::generate(&X25519).unwrap();
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
///     .expand(&[b"key"], alice_key.len())
///     .fill(&mut alice_key)
///     .unwrap();
/// salt.extract(bob_secret.as_ref())
///     .expand(&[b"key"], bob_key.len())
///     .fill(&mut bob_key)
///     .unwrap();
/// assert_eq!(alice_key, bob_key);
/// ```
pub mod agreement {
    pub use crate::high::agreement::{
        Algorithm, ECDH_P256, ECDH_P384, ECDH_P521, PrivateKey, PublicKey, Scalar, SharedSecret,
        X25519,
    };
}

/// Key encapsulation: ML-KEM-768.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::kem::*;
///
/// // The recipient generates a key pair, and sends the encapsulation key to
/// // the sender.
/// let decapsulation_key = DecapsulationKey::generate(&ML_KEM_768)?;
/// let encapsulation_key = decapsulation_key.public_key();
///
/// // The sender parses the encapsulation key, encapsulates a fresh secret,
/// // and sends the ciphertext back to the recipient.
/// let peer_key = EncapsulationKey::new(&ML_KEM_768, encapsulation_key.as_ref())?;
/// let (ciphertext, sender_secret) = peer_key.encapsulate()?;
///
/// // The recipient decapsulates the ciphertext, recovering the same secret.
/// let recipient_secret = decapsulation_key.decapsulate(ciphertext.as_ref())?;
///
/// // Each side derives its keys from the secret with a KDF.
/// let salt = rind::hkdf::Salt::new(&rind::hkdf::HKDF_SHA256, b"");
/// let mut sender_key = [0u8; 32];
/// let mut recipient_key = [0u8; 32];
/// salt.extract(sender_secret.as_ref())
///     .expand(&[b"key"], sender_key.len())
///     .fill(&mut sender_key)?;
/// salt.extract(recipient_secret.as_ref())
///     .expand(&[b"key"], recipient_key.len())
///     .fill(&mut recipient_key)?;
/// assert_eq!(sender_key, recipient_key);
/// # Ok(())
/// # }
/// ```
pub mod kem {
    pub use crate::high::kem::{
        Algorithm, Ciphertext, DecapsulationKey, EncapsulationKey, ML_KEM_768, SharedSecret,
    };
}

/// Hybrid public key encryption: [RFC 9180]'s base mode and secret export,
/// over DHKEM with X25519, P-256, P-384, and P-521.
///
/// A [`hpke::Sender`] encapsulates a fresh secret to a recipient's public
/// key and seals messages in order; the [`hpke::Recipient`] holding the
/// private key opens them in the same order. Both export secrets from the
/// shared context, as an [`hpke::Exporter`], which seals nothing, does
/// alone. Every pairing of a KEM, a KDF, and an AEAD is valid; the KEM is
/// the key's.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::hpke::*;
///
/// let private_key = PrivateKey::generate(&DHKEM_X25519_HKDF_SHA256)?;
/// let public_key = private_key.public_key();
/// let suite = Suite {
///     kdf: &HKDF_SHA256,
///     aead: &AES_128_GCM,
/// };
///
/// // The sender sends the encapsulated key with its messages.
/// let (enc, mut sender) = Sender::new(suite, &public_key, b"info")?;
/// let mut message = b"hello".to_vec();
/// sender.seal_in_place_append_tag(b"header", &mut message)?;
///
/// let mut recipient = Recipient::new(suite, &private_key, enc.as_ref(), b"info")?;
/// let plaintext = recipient.open_in_place(b"header", &mut message)?;
/// assert_eq!(plaintext, b"hello");
///
/// // Both sides export the same secrets.
/// let mut ours = [0u8; 32];
/// let mut theirs = [0u8; 32];
/// sender.export(b"context", &mut ours)?;
/// recipient.export(b"context", &mut theirs)?;
/// assert_eq!(ours, theirs);
/// # Ok(())
/// # }
/// ```
///
/// [RFC 9180]: https://www.rfc-editor.org/rfc/rfc9180.html
pub mod hpke {
    pub use crate::high::hpke::{
        AES_128_GCM, AES_256_GCM, Aead, CHACHA20_POLY1305, DHKEM_P256_HKDF_SHA256,
        DHKEM_P384_HKDF_SHA384, DHKEM_P521_HKDF_SHA512, DHKEM_X25519_HKDF_SHA256, EncapsulatedKey,
        Exporter, HKDF_SHA256, HKDF_SHA384, HKDF_SHA512, Kdf, Kem, PrivateKey, PublicKey,
        Recipient, Sender, Suite,
    };
}

/// RSA encryption: RSA-OAEP with SHA-256, SHA-384, or SHA-512, and SHA-1
/// under [`rsa::legacy`].
///
/// RSA signatures are under [`signature`], and take this module's
/// [`KeySize`](rsa::KeySize) and [`PublicKeyComponents`](rsa::PublicKeyComponents)
/// too. PKCS#1 v1.5 encryption, which invites padding-oracle attacks, is
/// refused.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::rsa::*;
///
/// // The recipient generates a key, and sends its public key to the sender.
/// let decrypting_key = DecryptingKey::generate(&OAEP_SHA256, KeySize::Rsa2048)?;
/// let public_key = decrypting_key.to_spki();
///
/// // The sender parses the public key for the same algorithm, and encrypts
/// // a message to it.
/// let encrypting_key = EncryptingKey::new(&OAEP_SHA256, public_key.as_ref())?;
/// let ciphertext = encrypting_key.encrypt(b"hello", b"")?;
///
/// // The recipient decrypts it with the same label.
/// let plaintext = decrypting_key.decrypt(ciphertext.as_ref(), b"")?;
/// assert_eq!(plaintext.as_ref(), b"hello");
/// # Ok(())
/// # }
/// ```
pub mod rsa {
    pub use crate::high::oaep::{
        Ciphertext, DecryptingKey, EncryptingKey, OAEP_SHA256, OAEP_SHA384, OAEP_SHA512,
        OaepAlgorithm, Plaintext,
    };
    pub use crate::high::signature::PublicKeyComponents;
    pub use crate::mid::rsa_key_size::RsaKeySize as KeySize;

    /// RSA-OAEP with SHA-1, for protocols that still require it.
    pub mod legacy {
        pub use crate::high::oaep::OAEP_SHA1;
    }
}

/// RSA blind signatures ([RFC 9474]): a server signs a message a client
/// blinded, learning nothing of it, and the client unblinds the reply into an
/// RSASSA-PSS signature that anyone verifies with the server's public key.
///
/// Each of the four RSABSSA-SHA384 variants is an [`Algorithm`](blind_rsa::Algorithm).
/// Privacy Pass's publicly verifiable tokens ([RFC 9578], type `0x0002`) use
/// [`RSABSSA_SHA384_PSS_DETERMINISTIC`](blind_rsa::RSABSSA_SHA384_PSS_DETERMINISTIC)
/// with 2048-bit keys.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::blind_rsa::*;
/// use rind::rsa::KeySize;
///
/// // The server generates a key, and publishes its public key.
/// let key_pair = KeyPair::generate(&RSABSSA_SHA384_PSS_RANDOMIZED, KeySize::Rsa2048)?;
/// let spki = key_pair.public_key().to_spki();
///
/// // The client blinds a message to it, and sends the server the blinded
/// // message, keeping its blinding.
/// let public_key = PublicKey::new(&RSABSSA_SHA384_PSS_RANDOMIZED, spki.as_ref())?;
/// let (blinded_message, blinding) = public_key.blind(b"hello")?;
///
/// // The server signs it, and the client unblinds the reply.
/// let blind_signature = key_pair.blind_sign(blinded_message.as_ref())?;
/// let signature = blinding.finalize(blind_signature.as_ref())?;
///
/// // Anyone with the public key verifies the signature.
/// public_key.verify(b"hello", signature.as_ref())?;
/// # Ok(())
/// # }
/// ```
///
/// [RFC 9474]: https://www.rfc-editor.org/rfc/rfc9474.html
/// [RFC 9578]: https://www.rfc-editor.org/rfc/rfc9578.html
pub mod blind_rsa {
    pub use crate::high::blind_rsa::{
        Algorithm, BlindSignature, BlindedMessage, Blinding, KeyPair, PublicKey,
        RSABSSA_SHA384_PSS_DETERMINISTIC, RSABSSA_SHA384_PSS_RANDOMIZED,
        RSABSSA_SHA384_PSSZERO_DETERMINISTIC, RSABSSA_SHA384_PSSZERO_RANDOMIZED, Signature,
    };
}

/// Oblivious pseudorandom functions ([RFC 9497]) over ristretto255, P-256,
/// P-384, and P-521.
///
/// A client learns the server's PRF of an input without the server learning
/// the input or the client learning the server's key. The client blinds the
/// input, the server evaluates the blinded element, and the client finalizes
/// the evaluated element into the output. The [`voprf`](oprf::voprf) mode
/// adds a proof that the server used the key it published, for one input or
/// a batch; Privacy Pass's privately verifiable tokens run it on
/// [`P384_SHA384`](oprf::P384_SHA384) and their batched ones on
/// [`RISTRETTO255_SHA512`](oprf::RISTRETTO255_SHA512). The POPRF mode is not
/// offered.
///
/// Everything holding the input, the blind, or the server's key runs in
/// constant time.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::oprf::{RISTRETTO255_SHA512, voprf};
///
/// let server = voprf::ServerKey::generate(&RISTRETTO255_SHA512)?;
/// let public_key = voprf::PublicKey::new(&RISTRETTO255_SHA512, server.public_key().as_ref())?;
///
/// let (blind, blinded_element) = voprf::Blind::new(&RISTRETTO255_SHA512, b"password")?;
/// let (evaluated, proof) = server.blind_evaluate(blinded_element.as_ref())?;
/// let output = blind.finalize(evaluated.as_ref(), proof.as_ref(), &public_key)?;
///
/// // The server, holding the input, computes the same output directly.
/// assert_eq!(output.as_ref(), server.evaluate(b"password")?.as_ref());
/// # Ok(())
/// # }
/// ```
///
/// [RFC 9497]: https://www.rfc-editor.org/rfc/rfc9497.html
pub mod oprf {
    pub use crate::high::oprf::{
        Blind, BlindedElement, EvaluatedElement, Output, P256_SHA256, P384_SHA384, P521_SHA512,
        RISTRETTO255_SHA512, ServerKey, ServerKeyBytes, Suite,
    };

    /// RFC 9497's VOPRF mode: the OPRF, with a proof that the server
    /// evaluated every blinded element in a batch with the key it published.
    pub mod voprf {
        pub use crate::high::oprf::voprf::{Blind, EvaluatedElements, Proof, PublicKey, ServerKey};
    }
}

/// Verifiable random functions: ECVRF ([RFC 9381]) on edwards25519 and P-256.
///
/// The holder of a secret key proves an output for any input; anyone with
/// the public key verifies the proof and recovers the same output, which is
/// pseudorandom to anyone without the secret key. Key transparency uses them
/// to map identities to positions in its tree.
///
/// Each suite encodes its input to the curve by try-and-increment, whose
/// running time depends on the input, so an input that must stay secret
/// from an observer of timing needs another suite (RFC 9381 section 5.4.1.1).
/// P-256's nonce is RFC 6979's: a candidate not from 1 to n - 1 draws
/// another block, with probability about 2^-32, and that retry is not
/// constant time. An Edwards25519 seed is an RFC 8032 seed dedicated to
/// the VRF. Signing with it reuses the nonce and reveals the scalar; see
/// [`SecretKey`](vrf::SecretKey).
/// [`PublicKey::verify`](vrf::PublicKey::verify) always validates the key
/// (`validate_key = TRUE`).
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::vrf::*;
///
/// let secret_key = SecretKey::generate(&ECVRF_EDWARDS25519_SHA512_TAI)?;
/// let (proof, output) = secret_key.prove(b"alice@example.com")?;
///
/// // A verifier parses the public key and recovers the same output.
/// let encoded = secret_key.public_key().as_ref();
/// let public_key = PublicKey::new(&ECVRF_EDWARDS25519_SHA512_TAI, encoded)?;
/// let verified = public_key.verify(b"alice@example.com", proof.as_ref())?;
/// assert_eq!(verified.as_ref(), output.as_ref());
/// # Ok(())
/// # }
/// ```
///
/// [RFC 9381]: https://www.rfc-editor.org/rfc/rfc9381.html
pub mod vrf {
    pub use crate::high::vrf::{
        Algorithm, ECVRF_EDWARDS25519_SHA512_TAI, ECVRF_P256_SHA256_TAI, Output, Proof, PublicKey,
        SecretKey, SecretKeyBytes,
    };
}

/// Public key signatures: ECDSA on P-256, P-384, and P-521, RSA, and Ed25519.
///
/// A key pair signs with a [`signature::sign`] algorithm, and a peer's
/// public key is parsed for a [`signature::verify`] algorithm:
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::signature::{EcdsaKeyPair, PublicKey, sign, verify};
///
/// let key_pair = EcdsaKeyPair::generate(&sign::ECDSA_P256_SHA256_ASN1)?;
/// let signature = key_pair.sign(b"hello")?;
///
/// let encoded = key_pair.public_key();
/// let public_key = PublicKey::new(&verify::ECDSA_P256_SHA256_ASN1, encoded.as_ref())?;
/// public_key.verify(b"hello", signature.as_ref())?;
/// # Ok(())
/// # }
/// ```
pub mod signature {
    pub use crate::high::signature::{
        EcdsaKeyPair, EcdsaScalar, EcdsaSigningAlgorithm, Ed25519KeyPair, Ed25519Seed, PublicKey,
        RsaKeyPair, RsaPssSaltLength, RsaSigningAlgorithm, RsaVerificationAlgorithm, Signature,
        VerificationAlgorithm,
    };

    /// Algorithms a key pair signs with, and ML-DSA's key pair, whose
    /// parameter set is a type.
    ///
    /// Each signs as the [`verify`] algorithm of the same name verifies:
    /// [`MlDsaKeyPair<MlDsa65>`] as [`verify::ML_DSA_65`].
    ///
    /// ```
    /// use rind::signature::sign::{MlDsa65, MlDsaKeyPair};
    /// use rind::signature::{PublicKey, verify};
    ///
    /// let key = MlDsaKeyPair::<MlDsa65>::generate().unwrap();
    /// let signature = key.sign(b"hello").unwrap();
    ///
    /// let public_key = PublicKey::new(&verify::ML_DSA_65, key.public_key().as_ref()).unwrap();
    /// public_key.verify(b"hello", signature.as_ref()).unwrap();
    /// ```
    pub mod sign {
        pub use crate::high::signature::sign::{
            ECDSA_P256_SHA256_ASN1, ECDSA_P256_SHA256_FIXED, ECDSA_P384_SHA384_ASN1,
            ECDSA_P384_SHA384_FIXED, ECDSA_P521_SHA512_ASN1, ECDSA_P521_SHA512_FIXED,
            RSA_PKCS1_SHA256, RSA_PKCS1_SHA384, RSA_PKCS1_SHA512, RSA_PSS_SHA256, RSA_PSS_SHA384,
            RSA_PSS_SHA512,
        };
        pub use crate::high::signature::{
            MlDsaKeyPair, MlDsaParameterSet, MlDsaSeed, MlDsaSignature,
        };
        pub use crate::mid::mldsa::{MlDsa44, MlDsa65, MlDsa87};
    }

    /// Algorithms a public key verifies with.
    ///
    /// RSA algorithms accept moduli of 2048 to 8192 bits.
    pub mod verify {
        pub use crate::high::signature::verify::{
            ECDSA_P256_SHA256_ASN1, ECDSA_P256_SHA256_FIXED, ECDSA_P256_SHA384_ASN1,
            ECDSA_P256_SHA512_ASN1, ECDSA_P384_SHA256_ASN1, ECDSA_P384_SHA384_ASN1,
            ECDSA_P384_SHA384_FIXED, ECDSA_P384_SHA512_ASN1, ECDSA_P521_SHA256_ASN1,
            ECDSA_P521_SHA384_ASN1, ECDSA_P521_SHA512_ASN1, ECDSA_P521_SHA512_FIXED, ED25519,
            ML_DSA_44, ML_DSA_65, ML_DSA_87, RSA_PKCS1_SHA256, RSA_PKCS1_SHA384, RSA_PKCS1_SHA512,
            RSA_PSS_SHA256, RSA_PSS_SHA256_ANY_SALT, RSA_PSS_SHA384, RSA_PSS_SHA384_ANY_SALT,
            RSA_PSS_SHA512, RSA_PSS_SHA512_ANY_SALT,
        };

        /// RSA algorithms with another modulus floor, or SHA-1, for old keys
        /// and signatures.
        pub mod legacy {
            pub use crate::high::signature::verify::legacy::{
                RSA_PKCS1_1024_SHA1, RSA_PKCS1_1024_SHA256, RSA_PKCS1_1024_SHA512,
                RSA_PKCS1_3072_SHA384, RSA_PKCS1_SHA1,
            };
        }
    }
}

/// Cryptographic hash functions.
///
/// ```
/// use rind::digest;
///
/// let mut ctx = digest::Context::new(&digest::SHA256);
/// ctx.update(b"hello, ");
/// ctx.update(b"world");
/// assert_eq!(
///     ctx.finish().as_ref(),
///     digest::digest(&digest::SHA256, b"hello, world").as_ref(),
/// );
/// ```
pub mod digest {
    pub use super::high::digest::{
        Algorithm, Context, Digest, SHA3_256, SHA3_384, SHA3_512, SHA256, SHA384, SHA512,
        SHA512_256, digest,
    };

    /// Hash functions only legacy protocols should use.
    pub mod legacy {
        pub use crate::high::digest::{MD5, SHA1};
    }
}

/// Message authentication with HMAC.
///
/// A [`hmac::Key`] precomputes its keyed hash states once; each message then
/// signs through a [`hmac::Context`] started from it, or the one-shot
/// [`hmac::sign`] and [`hmac::verify`].
///
/// ```
/// use rind::hmac;
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
pub mod hmac {
    pub use super::high::hmac::{
        Algorithm, Context, HMAC_SHA256, HMAC_SHA384, HMAC_SHA512, Key, Tag, sign, verify,
    };

    /// HMAC algorithms only legacy protocols should use.
    pub mod legacy {
        pub use crate::high::hmac::HMAC_SHA1;
    }
}

/// Constant-time comparison, for checking a secret such as a MAC or token.
///
/// ```
/// use rind::constant_time;
///
/// constant_time::verify(b"expected", b"expected").unwrap();
/// assert_eq!(
///     constant_time::verify(b"expected", b"presented"),
///     Err(rind::Error::WrongLength)
/// );
/// assert_eq!(
///     constant_time::verify(b"expected", b"Expected"),
///     Err(rind::Error::NotEqual)
/// );
/// ```
pub mod constant_time {
    pub use crate::high::constant_time::verify;
}

/// Key derivation with HKDF.
///
/// A [`hkdf::Salt`] extracts a [`hkdf::Prk`] from a secret, which then expands
/// into any number of keys, each exactly as long as what it becomes.
///
/// ```
/// use rind::{aead, hkdf, hmac};
///
/// let prk = hkdf::Salt::new(&hkdf::HKDF_SHA256, b"salt").extract(b"input key material");
///
/// let aead_key = aead::Key::from(prk.expand(&[b"aead"], &aead::AES_256_GCM));
/// let hmac_key = hmac::Key::from(prk.expand(&[b"hmac"], &hmac::HMAC_SHA256));
///
/// let info: [&[u8]; 2] = [b"label", b"context"];
/// let mut bytes = [0u8; 16];
/// prk.expand(&info, bytes.len()).fill(&mut bytes).unwrap();
/// ```
pub mod hkdf {
    pub use super::high::hkdf::{
        Algorithm, HKDF_SHA256, HKDF_SHA384, HKDF_SHA512, KeyType, Okm, Prk, Salt,
    };

    /// HKDF algorithms only legacy protocols should use.
    pub mod legacy {
        pub use crate::high::hkdf::HKDF_SHA1;
    }
}

/// SPAKE2+ on P-256 with SHA-256, HKDF, and HMAC.
///
/// [`RFC9383`](spake2plus::RFC9383) is RFC 9383. [`MATTER_PASE`](spake2plus::MATTER_PASE)
/// is draft-bar-cfrg-spake2plus-01, the key schedule Matter's commissioning uses.
/// The group, the points M and N, and the transcript are the same. The suites
/// are different types, so a share from one does not type-check as the other's.
/// The caller stretches the password and passes `w0` and `w1`. A verifier
/// stores `w0` and `L = w1 * G`, not `w1`.
///
/// ```
/// use rind::spake2plus::{ProverSecrets, RFC9383, VerifierRecord};
///
/// let w0 = [0x11; 40];
/// let w1 = [0x22; 40];
/// let prover = ProverSecrets::new(&w0, &w1).unwrap();
/// let verifier = VerifierRecord::from_w1(&w0, &w1).unwrap();
///
/// let (share_p, prover) = prover
///     .start(&RFC9383, b"app", b"client", b"server")
///     .unwrap();
/// let (share_v, confirm_v, verifier) = verifier
///     .start(&RFC9383, b"app", b"client", b"server", &share_p)
///     .unwrap();
/// let (confirm_p, prover_key) = prover.finish(&share_v, &confirm_v).unwrap();
/// let verifier_key = verifier.finish(&confirm_p).unwrap();
/// assert_eq!(prover_key.as_ref(), verifier_key.as_ref());
/// ```
pub mod spake2plus {
    pub use super::high::spake2plus::{
        Confirm, MATTER_PASE, MatterPase, ProverAwaiting, ProverSecrets, RFC9383, Rfc9383, Share,
        SharedKey, Suite, VerifierAwaiting, VerifierRecord,
    };
}

/// Password-based key derivation with PBKDF2.
///
/// A [`pbkdf2::Secret`] keys HMAC with a password once, then derives a key
/// for a salt and iteration count, or checks one derived before. This
/// example takes the iteration count OWASP suggests for SHA-256, so it is
/// not run as a test.
///
/// ```no_run
/// use std::num::NonZeroU32;
///
/// use rind::pbkdf2;
///
/// let iterations = NonZeroU32::new(600_000).unwrap();
/// let secret = pbkdf2::Secret::new(&pbkdf2::PBKDF2_HMAC_SHA256, b"password");
///
/// let mut stored = [0u8; 32];
/// secret
///     .derive(iterations, b"per-user salt", &mut stored)
///     .unwrap();
///
/// secret
///     .verify(iterations, b"per-user salt", &stored)
///     .unwrap();
/// ```
pub mod pbkdf2 {
    pub use super::high::pbkdf2::{
        Algorithm, PBKDF2_HMAC_SHA256, PBKDF2_HMAC_SHA384, PBKDF2_HMAC_SHA512, Secret,
    };

    /// PBKDF2 algorithms only legacy formats should use.
    pub mod legacy {
        pub use crate::high::pbkdf2::PBKDF2_HMAC_SHA1;
    }
}

/// Authenticated encryption.
///
/// An [`aead::Key`] is built from an algorithm constant and key bytes, and
/// seals with the caller's nonces, which must never repeat under one key. An
/// [`aead::RandomizedNonceKey`] picks its own.
///
/// ```
/// use rind::aead::*;
///
/// let key = Key::new(&AES_128_GCM, &[0x42; 16]).unwrap();
///
/// let mut in_out = b"hello".to_vec();
/// let nonce = || Nonce::assume_unique_for_key([0; 12]);
/// key.seal_in_place_append_tag(nonce(), b"header", &mut in_out)
///     .unwrap();
///
/// let plaintext = key.open_in_place(nonce(), b"header", &mut in_out).unwrap();
/// assert_eq!(plaintext, b"hello");
/// ```
pub mod aead;

/// Encoded keys: PKCS#8 and SEC1 private keys, and `SubjectPublicKeyInfo`
/// public keys.
///
/// Every key type that exports itself returns these, whatever its module.
pub mod encoding {
    pub use crate::high::signature::{Pkcs8, Sec1, Spki};
}

/// Unauthenticated ciphers, for protocols that specify one alongside their own integrity protection.
///
/// Prefer [`aead`] unless a protocol requires one of these. Decrypting
/// AES-CBC before verifying a MAC over its ciphertext is a padding oracle.
pub mod cipher;

/// Key wrapping with AES-KW, RFC 3394, as WebCrypto's `AES-KW` and JWE's
/// `A128KW`, `A192KW`, and `A256KW` use it, and with AES-KWP, RFC 5649,
/// which pads keys of any length.
///
/// ```
/// use rind::key_wrap::{AES_256, AesKek};
///
/// let kek = AesKek::new(&AES_256, &[0x42; 32]).unwrap();
///
/// let key = [0x24; 16];
/// let mut wrapped = [0u8; 24];
/// kek.wrap(&key, &mut wrapped).unwrap();
///
/// let mut unwrapped = [0u8; 16];
/// kek.unwrap(&wrapped, &mut unwrapped).unwrap();
/// assert_eq!(unwrapped, key);
///
/// let key = [0x24; 20];
/// let mut wrapped = [0u8; 32];
/// kek.wrap_padded(&key, &mut wrapped).unwrap();
///
/// let mut unwrapped = [0u8; 24];
/// assert_eq!(kek.unwrap_padded(&wrapped, &mut unwrapped).unwrap(), key);
/// ```
pub mod key_wrap {
    pub use crate::cipher::{AES_128, AES_192, AES_256};
    pub use crate::mid::aes_kw::AesKek;
}

/// CPU support.
///
/// Every operation panics on a CPU missing a feature rind requires. Check at
/// startup to refuse cleanly instead:
///
/// ```
/// if let Err(missing) = rind::cpu::check() {
///     eprintln!("{missing}");
///     std::process::exit(1);
/// }
/// ```
pub mod cpu {
    pub use crate::low::cpu::{Dit, MissingFeature, check, has_aes_hardware, wide_multiplier};
}

/// Random bytes from the system's secure random source.
///
/// No rind API takes a random source, so [`rand::fill`] is all a caller
/// needs.
///
/// ```
/// let mut nonce = [0u8; 16];
/// rind::rand::fill(&mut nonce).unwrap();
/// ```
pub mod rand {
    /// Fills the entirety of `out` with random bytes.
    pub fn fill(out: &mut [u8]) -> Result<(), super::Error> {
        use crate::mid::rng::{RandomSource, SystemRandom};
        SystemRandom.fill(out)
    }
}
