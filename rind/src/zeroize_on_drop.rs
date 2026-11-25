// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! zeroize's `ZeroizeOnDrop` on every public type that wipes itself on drop.
//!
//! `tests/zeroing.rs` checks each of these, and with the `zeroize` feature
//! requires the trait of every type it checks, so a key type it gains must
//! gain its line here too.

use zeroize::ZeroizeOnDrop;

macro_rules! wipes {
    ($($ty:ty),* $(,)?) => {
        $(impl ZeroizeOnDrop for $ty {})*
    };
}

wipes!(
    // Its variants wipe their whole values, leaving only the tag that names
    // the algorithm.
    crate::KeyPair,
    crate::aead::Key,
    crate::aead::RandomizedNonceKey,
    crate::aead::gcm::Key,
    crate::aead::quic::HeaderProtectionKey,
    crate::agreement::PrivateKey,
    crate::agreement::Scalar,
    crate::agreement::SharedSecret,
    crate::argon2::Secret,
    crate::blind_rsa::Blinding,
    crate::blind_rsa::KeyPair,
    crate::cipher::Aes,
    crate::cipher::AesCbcDecryptingKey,
    crate::cipher::AesCbcEncryptingKey,
    crate::cipher::AesCtr,
    crate::cipher::ChaCha20,
    crate::ecdsa::KeyPair,
    crate::ecdsa::Scalar,
    crate::ed25519::KeyPair,
    crate::ed25519::Seed,
    crate::encoding::Pkcs8,
    crate::encoding::Sec1,
    crate::frost::Scalar,
    crate::frost::SigningNonces,
    crate::frost::SigningShare,
    crate::hkdf::Prk,
    crate::hkdf::Salt,
    crate::hmac::Context,
    crate::hmac::Key,
    crate::hpke::Exporter,
    crate::hpke::PrivateKey,
    crate::hpke::Recipient,
    crate::hpke::Sender,
    crate::key_wrap::AesKek,
    crate::oprf::Blind,
    crate::oprf::Output,
    crate::oprf::Scalar,
    crate::oprf::ServerKey,
    crate::oprf::voprf::Blind,
    crate::oprf::voprf::ServerKey,
    crate::pbkdf2::Secret,
    crate::rsa::DecryptingKey,
    crate::rsa::KeyPair,
    crate::spake2plus::ProverSecrets,
    crate::spake2plus::SharedKey,
    crate::spake2plus::VerifierRecord,
    crate::vrf::KeyPair,
    crate::vrf::Seed,
);

impl<A: crate::kem::Algorithm> ZeroizeOnDrop for crate::kem::DecapsulationKey<A> {}
impl<A: crate::kem::Algorithm> ZeroizeOnDrop for crate::kem::SharedSecret<A> {}
#[cfg(feature = "ml-dsa")]
impl ZeroizeOnDrop for crate::ml_dsa::Seed {}
#[cfg(feature = "ml-dsa")]
impl<P: crate::ml_dsa::ParameterSet> ZeroizeOnDrop for crate::ml_dsa::KeyPair<P> {}
#[cfg(feature = "slh-dsa")]
impl<P: crate::slh_dsa::ParameterSet> ZeroizeOnDrop for crate::slh_dsa::KeyPair<P> {}
impl<S> ZeroizeOnDrop for crate::spake2plus::ProverAwaiting<S> {}
impl<S> ZeroizeOnDrop for crate::spake2plus::VerifierAwaiting<S> {}
