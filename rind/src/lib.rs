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
// Unit tests run on hosted targets and keep `std`'s prelude.
#![cfg_attr(not(test), no_std)]

extern crate alloc;

// Only where a build needs an operating system: the FIPS module, aarch64's
// run-time CPU detection, and the `RIND_CPU_DISABLE_*` switches of debug
// builds. `rind_std` (build.rs) marks the targets that have it.
#[cfg(all(
    not(test),
    any(
        rind_fips,
        all(
            rind_std,
            any(debug_assertions, rind_cpu_disable, rind_backend = "aarch64")
        )
    )
))]
extern crate std;

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

/// What the FIPS module (`rind-fips`) needs beyond the public API: its
/// self-tests, its error state, and its errors' codes. Only the module's own
/// build compiles it.
#[cfg(any(test, rind_fips))]
#[doc(hidden)]
pub mod fips;

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
///     .and_then(|prk| prk.fill(&[b"key"], &mut alice_key))
///     .unwrap();
/// salt.extract(bob_secret.as_ref())
///     .and_then(|prk| prk.fill(&[b"key"], &mut bob_key))
///     .unwrap();
/// assert_eq!(alice_key, bob_key);
/// ```
pub mod agreement {
    pub use crate::high::agreement::{
        Algorithm, ECDH_P256, ECDH_P384, ECDH_P521, PrivateKey, PublicKey, Scalar, SharedSecret,
        X25519,
    };
}

/// Key encapsulation: ML-KEM-512, ML-KEM-768, ML-KEM-1024, and X-Wing.
///
/// Each type names its parameter set, so a ciphertext of one set fails to
/// compile against a key of another. [`XWing`](kem::XWing) is the hybrid of X25519 and
/// ML-KEM-768 that draft-connolly-cfrg-xwing-kem specifies (HPKE's
/// MLKEM768-X25519, KEM 0x647A), and its keys work as ML-KEM's do. Its
/// private key is a 32-byte [`Seed`](kem::Seed), which `DecapsulationKey::<XWing>`
/// exports with `to_seed` and loads with `from_seed`.
///
/// X-Wing takes the draft's text on an all-zero X25519 secret, from an
/// encapsulation key or a ciphertext whose X25519 half has a small order:
/// the combiner hashes it as any other, and decapsulation cannot fail. The
/// CFRG has not settled whether implementations should refuse it instead.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::kem::*;
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
/// let salt = rind::hkdf::Salt::new(&rind::hkdf::HKDF_SHA256, b"session salt");
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
pub mod kem {
    pub use crate::high::kem::{
        Algorithm, Ciphertext, DecapsulationKey, EncapsulationKey, MlKem512, MlKem768, MlKem1024,
        Seed, SharedSecret, XWing,
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

/// RSA: PKCS#1 v1.5 and PSS signatures, and RSA-OAEP encryption.
///
/// A [`KeyPair`](rsa::KeyPair) signs with any [`rsa::sign`] algorithm, and
/// a [`PublicKey`](rsa::PublicKey) verifies with any [`rsa::verify`]
/// algorithm whose floor its modulus meets: neither is bound to a padding,
/// as TLS picks one per handshake.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::rsa::{KeyPair, KeySize, PublicKey, sign, verify};
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
/// An RSA-OAEP key is bound to its algorithm. PKCS#1 v1.5 encryption,
/// which invites padding-oracle attacks, is refused.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::rsa::*;
///
/// // The recipient generates a key, and sends its public key to the sender.
/// let decrypting_key = DecryptingKey::generate(&OAEP_SHA256, KeySize::Rsa2048)?;
/// let public_key = decrypting_key.public_key().to_spki();
///
/// // The sender parses the public key for the same algorithm, and encrypts
/// // a message to it.
/// let encrypting_key = EncryptingKey::from_spki(&OAEP_SHA256, public_key.as_ref())?;
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
    pub use crate::high::signature::rsa::{
        KeyPair, PssSaltLength, PublicKey, PublicKeyComponents, Signature, SigningAlgorithm,
        VerificationAlgorithm,
    };
    pub use crate::mid::rsa_key_size::RsaKeySize as KeySize;

    /// Algorithms a key pair signs with.
    pub mod sign {
        pub use crate::high::signature::rsa::sign::{
            PKCS1_SHA256, PKCS1_SHA384, PKCS1_SHA512, PSS_SHA256, PSS_SHA384, PSS_SHA512,
        };
    }

    /// Algorithms a public key verifies with, for moduli of 2048 to 8192
    /// bits.
    pub mod verify {
        pub use crate::high::signature::rsa::verify::{
            PKCS1_SHA256, PKCS1_SHA384, PKCS1_SHA512, PSS_SHA256, PSS_SHA256_ANY_SALT, PSS_SHA384,
            PSS_SHA384_ANY_SALT, PSS_SHA512, PSS_SHA512_ANY_SALT,
        };

        /// Algorithms with another modulus floor, or SHA-1, for old keys
        /// and signatures.
        pub mod legacy {
            pub use crate::high::signature::rsa::verify::legacy::{
                PKCS1_1024_SHA1, PKCS1_1024_SHA256, PKCS1_1024_SHA512, PKCS1_3072_SHA384,
                PKCS1_SHA1,
            };
        }
    }

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
/// let public_key = PublicKey::from_spki(&RSABSSA_SHA384_PSS_RANDOMIZED, spki.as_ref())?;
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

/// FROST threshold Schnorr signatures ([RFC 9591]) over Ed25519,
/// ristretto255, and P-256.
///
/// A trusted dealer splits a signing key into shares, any threshold of
/// which sign together. Each signer commits to fresh nonces, the
/// coordinator gathers the commitments and the message into a
/// [`SigningPackage`](frost::SigningPackage) every signer builds the same
/// way, each signer returns its signature share, and the coordinator sums
/// them into one signature under the group's key, verifying each share to
/// name a participant whose share is bad. A
/// [`FROST(Ed25519, SHA-512)`](frost::ED25519_SHA512) signature is an
/// Ed25519 signature.
///
/// Dealing and signing run in constant time. Distributed key generation is
/// not offered.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::frost::*;
///
/// // The dealer gives each of three participants a share, any two of which
/// // sign, and publishes its commitment.
/// let (shares, commitment) = deal(&ED25519_SHA512, 2, 3)?;
///
/// // Two participants commit to nonces and send the coordinator their
/// // commitments.
/// let (nonces_1, commitments_1) = SigningNonces::commit(&shares[0])?;
/// let (nonces_3, commitments_3) = SigningNonces::commit(&shares[2])?;
///
/// // The coordinator sends the commitments and the message to both, and
/// // each builds the same package and signs it.
/// let public_key = commitment.public_key();
/// let package = SigningPackage::new(public_key, &[commitments_1, commitments_3], b"hello")?;
/// let share_1 = nonces_1.sign(&shares[0], &package)?;
/// let share_3 = nonces_3.sign(&shares[2], &package)?;
///
/// // The coordinator checks each share and sums them into the signature.
/// package.verify_share(&share_1, &commitment)?;
/// package.verify_share(&share_3, &commitment)?;
/// let signature = package.aggregate(&[share_1, share_3])?;
/// public_key.verify(b"hello", signature.as_ref())?;
/// # Ok(())
/// # }
/// ```
///
/// [RFC 9591]: https://www.rfc-editor.org/rfc/rfc9591.html
pub mod frost {
    pub use crate::high::frost::{
        Commitments, ED25519_SHA512, Identifier, P256_SHA256, PublicKey, RISTRETTO255_SHA512,
        Scalar, Signature, SignatureShare, SigningNonces, SigningPackage, SigningShare, Suite,
        VssCommitment, deal,
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
        RISTRETTO255_SHA512, Scalar, ServerKey, Suite,
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
/// [`KeyPair`](vrf::KeyPair).
/// [`PublicKey::verify`](vrf::PublicKey::verify) always validates the key
/// (`validate_key = TRUE`).
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::vrf::*;
///
/// let key_pair = KeyPair::generate(&ECVRF_EDWARDS25519_SHA512_TAI)?;
/// let (proof, output) = key_pair.prove(b"alice@example.com")?;
///
/// // A verifier parses the public key and recovers the same output.
/// let encoded = key_pair.public_key().as_ref();
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
        Algorithm, ECVRF_EDWARDS25519_SHA512_TAI, ECVRF_P256_SHA256_TAI, KeyPair, Output, Proof,
        PublicKey, Seed,
    };
}

/// ECDSA signatures on P-256, P-384, and P-521.
///
/// A key pair signs with an [`ecdsa::sign`] algorithm, and its public key,
/// or a peer's parsed for an [`ecdsa::verify`] algorithm, verifies:
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::ecdsa::{KeyPair, PublicKey, sign, verify};
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
    pub use crate::high::signature::ecdsa::{
        KeyPair, PublicKey, Scalar, Signature, SigningAlgorithm, VerificationAlgorithm,
    };

    /// Algorithms a key pair signs with.
    ///
    /// Each signs as the [`verify`] algorithm of the same name verifies.
    pub mod sign {
        pub use crate::high::signature::ecdsa::sign::{
            P256_SHA256_ASN1, P256_SHA256_FIXED, P384_SHA384_ASN1, P384_SHA384_FIXED,
            P521_SHA512_ASN1, P521_SHA512_FIXED,
        };
    }

    /// Algorithms a public key verifies with.
    pub mod verify {
        pub use crate::high::signature::ecdsa::verify::{
            P256_SHA256_ASN1, P256_SHA256_FIXED, P256_SHA384_ASN1, P256_SHA512_ASN1,
            P384_SHA256_ASN1, P384_SHA384_ASN1, P384_SHA384_FIXED, P384_SHA512_ASN1,
            P521_SHA256_ASN1, P521_SHA384_ASN1, P521_SHA512_ASN1, P521_SHA512_FIXED,
        };
    }
}

/// Ed25519 signatures ([RFC 8032]).
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::ed25519::{KeyPair, PublicKey};
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
    pub use crate::high::signature::ed25519::{KeyPair, PublicKey, Seed, Signature};
}

/// ML-DSA signatures (FIPS 204): ML-DSA-44, ML-DSA-65, and ML-DSA-87, pure
/// with the empty context.
///
/// The parameter set is a type, so a key of one set fails to compile where
/// another's is expected, and a signature is a fixed-size array.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::ml_dsa::{KeyPair, MlDsa65, PublicKey};
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
    pub use crate::high::signature::ml_dsa::{KeyPair, ParameterSet, PublicKey, Seed, Signature};
    pub use crate::mid::mldsa::{MlDsa44, MlDsa65, MlDsa87};
}

/// SLH-DSA signatures (FIPS 205): all twelve parameter sets, pure with the
/// empty context, as X.509 signs (RFC 9909).
///
/// The parameter set is a type, so a key of one set fails to compile where
/// another's is expected. A signature, up to 49,856 bytes, lives on the
/// heap.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::slh_dsa::{KeyPair, PublicKey, SlhDsaSha2_128f};
///
/// let key_pair = KeyPair::<SlhDsaSha2_128f>::generate()?;
/// let signature = key_pair.sign(b"hello")?;
///
/// let public_key = PublicKey::<SlhDsaSha2_128f>::new(key_pair.public_key().as_ref())?;
/// public_key.verify(b"hello", signature.as_ref())?;
/// # Ok(())
/// # }
/// ```
pub mod slh_dsa {
    pub use crate::high::signature::slh_dsa::{KeyPair, ParameterSet, PublicKey, Signature};
    pub use crate::mid::slhdsa::{
        SlhDsaSha2_128f, SlhDsaSha2_128s, SlhDsaSha2_192f, SlhDsaSha2_192s, SlhDsaSha2_256f,
        SlhDsaSha2_256s, SlhDsaShake128f, SlhDsaShake128s, SlhDsaShake192f, SlhDsaShake192s,
        SlhDsaShake256f, SlhDsaShake256s,
    };
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
/// A [`hkdf::Salt`] extracts a [`hkdf::Prk`] from a secret, or
/// [`hkdf::Prk::new`] takes one a protocol already holds. It then expands
/// into any number of keys, each exactly as long as what it becomes, or fills
/// a buffer.
///
/// ```
/// # fn main() -> Result<(), rind::Error> {
/// use rind::{aead, hkdf, hmac};
///
/// let prk = hkdf::Salt::new(&hkdf::HKDF_SHA256, b"salt").extract(b"input key material")?;
///
/// let aead_key = aead::Key::from(prk.expand(&[b"aead"], &aead::AES_256_GCM)?);
/// let hmac_key = hmac::Key::from(prk.expand(&[b"hmac"], &hmac::HMAC_SHA256)?);
///
/// let info: [&[u8]; 2] = [b"label", b"context"];
/// let mut bytes = [0u8; 16];
/// prk.fill(&info, &mut bytes)?;
///
/// let loaded = hkdf::Prk::new(&hkdf::HKDF_SHA256, &[0x0b; 32]);
/// loaded.fill(&info, &mut bytes)?;
/// # Ok(())
/// # }
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
/// use rind::spake2plus::{ProverSecrets, RFC9383, Session, VerifierRecord};
///
/// let w0 = [0x11; 40];
/// let w1 = [0x22; 40];
/// let prover = ProverSecrets::new(&w0, &w1).unwrap();
/// let verifier = VerifierRecord::from_w1(&w0, &w1).unwrap();
/// let session = Session {
///     context: b"app",
///     id_prover: b"client",
///     id_verifier: b"server",
/// };
///
/// let (share_p, prover) = prover.start(&RFC9383, &session).unwrap();
/// let (share_v, confirm_v, verifier) = verifier.start(&RFC9383, &session, &share_p).unwrap();
/// let (confirm_p, prover_key) = prover.finish(&share_v, &confirm_v).unwrap();
/// let verifier_key = verifier.finish(&confirm_p).unwrap();
/// assert_eq!(prover_key.as_ref(), verifier_key.as_ref());
/// ```
pub mod spake2plus {
    pub use super::high::spake2plus::{
        Confirm, MATTER_PASE, MatterPase, ProverAwaiting, ProverSecrets, RFC9383, Rfc9383, Session,
        Share, SharedKey, Suite, VerifierAwaiting, VerifierRecord,
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

/// Password hashing and key derivation with Argon2id.
///
/// An [`argon2::Secret`] holds a password, whose
/// [`derive`](argon2::Secret::derive) derives a key from a salt at the memory
/// and time [`argon2::Params`] sets, and whose
/// [`verify`](argon2::Secret::verify) checks one derived before, as
/// [`pbkdf2::Secret`]'s do. This example takes RFC 9106's second
/// recommendation, 64 MiB over three passes, so it is not run as a test.
///
/// ```no_run
/// use rind::argon2;
///
/// let params = argon2::Params::SECOND_RECOMMENDED;
/// let secret = argon2::Secret::new(b"password");
/// let mut stored = [0u8; 32];
/// // Each account's salt is its own, stored beside its key.
/// secret
///     .derive(params, b"per-user salt", &mut stored)
///     .unwrap();
///
/// secret.verify(params, b"per-user salt", &stored).unwrap();
/// ```
///
/// After the first half of its first pass, Argon2id reads memory at offsets
/// that depend on the password, so an attacker who can watch the cache learns
/// something about the password. That is the price of its resistance to
/// trading memory for time, which RFC 9106 accepts.
pub mod argon2 {
    pub use super::high::argon2::{Params, Secret};
}

/// Authenticated encryption.
///
/// An [`aead::Key`] is built from an algorithm constant and key bytes, and
/// seals with the caller's nonces, which must never repeat under one key.
/// [`aead::Nonce::from_sequence`] builds TLS 1.3's, QUIC's, and HPKE's from an
/// IV and a sequence number. An [`aead::RandomizedNonceKey`] picks its own.
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
/// A key-encryption key wraps in either [`Mode`](key_wrap::Mode), chosen
/// per call.
///
/// ```
/// use rind::key_wrap::{AES_256, AesKek, Mode};
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
    pub use crate::cipher::{AES_128, AES_192, AES_256};
    pub use crate::mid::aes_kw::{AesKek, Mode};
}

/// CPU support.
pub mod cpu {
    pub use crate::low::cpu::{Dit, has_aes_hardware};
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
