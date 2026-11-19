//! Each key, context, and digest names the algorithm it was made with, as
//! ring's do, and the conversions and generators ring offers work.

use rind_ring::{aead, agreement, digest, error, hmac, rand};

struct Counter(u64);

impl aead::NonceSequence for Counter {
    fn advance(&mut self) -> Result<aead::Nonce, error::Unspecified> {
        self.0 += 1;
        let mut nonce = [0; 12];
        nonce[4..].copy_from_slice(&self.0.to_be_bytes());
        Ok(aead::Nonce::assume_unique_for_key(nonce))
    }
}

#[test]
fn aead_keys_name_their_algorithm() {
    use aead::BoundKey;

    for algorithm in [
        &aead::AES_128_GCM,
        &aead::AES_256_GCM,
        &aead::CHACHA20_POLY1305,
    ] {
        let key = vec![7; algorithm.key_len()];
        let unbound = || aead::UnboundKey::new(algorithm, &key).unwrap();
        assert_eq!(unbound().algorithm(), algorithm);
        assert_eq!(aead::LessSafeKey::new(unbound()).algorithm(), algorithm);
        assert_eq!(
            aead::SealingKey::new(unbound(), Counter(0)).algorithm(),
            algorithm
        );
        assert_eq!(
            aead::OpeningKey::new(unbound(), Counter(0)).algorithm(),
            algorithm
        );
    }

    for algorithm in [
        &aead::quic::AES_128,
        &aead::quic::AES_256,
        &aead::quic::CHACHA20,
    ] {
        let key = vec![7; algorithm.key_len()];
        let key = aead::quic::HeaderProtectionKey::new(algorithm, &key).unwrap();
        assert_eq!(key.algorithm(), algorithm);
    }
}

#[test]
fn agreement_keys_name_their_algorithm() {
    let rng = rand::SystemRandom::new();
    for algorithm in [
        &agreement::X25519,
        &agreement::ECDH_P256,
        &agreement::ECDH_P384,
    ] {
        let private = agreement::EphemeralPrivateKey::generate(algorithm, &rng).unwrap();
        let public = private.compute_public_key().unwrap();
        assert_eq!(public.algorithm(), algorithm);
        let unparsed = agreement::UnparsedPublicKey::new(algorithm, public.as_ref().to_vec());
        assert_eq!(unparsed.algorithm(), algorithm);
        assert_eq!(unparsed.bytes(), &public.as_ref().to_vec());
    }
}

#[test]
fn digests_name_their_algorithm() {
    for algorithm in [
        &digest::SHA1_FOR_LEGACY_USE_ONLY,
        &digest::SHA256,
        &digest::SHA384,
        &digest::SHA512,
        &digest::SHA512_256,
    ] {
        let context = digest::Context::new(algorithm);
        assert_eq!(context.algorithm(), algorithm);
        assert_eq!(context.finish().algorithm(), algorithm);
    }
}

/// ring turns a rejected key into `Unspecified`, so `?` takes either.
#[test]
fn key_rejected_converts_to_unspecified() {
    fn load(pkcs8: &[u8]) -> Result<(), error::Unspecified> {
        rind_ring::signature::Ed25519KeyPair::from_pkcs8(pkcs8)?;
        Ok(())
    }
    assert_eq!(load(&[0x30, 0x00]), Err(error::Unspecified));
}

/// A generated HMAC key is as long as the hash's output, and so is fresh.
#[test]
fn hmac_keys_generate() {
    let rng = rand::SystemRandom::new();
    for algorithm in [
        hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
        hmac::HMAC_SHA256,
        hmac::HMAC_SHA384,
        hmac::HMAC_SHA512,
    ] {
        let first = hmac::Key::generate(algorithm, &rng).unwrap();
        let second = hmac::Key::generate(algorithm, &rng).unwrap();
        assert_eq!(first.algorithm(), algorithm);
        let tag = hmac::sign(&first, b"message");
        assert_eq!(
            tag.as_ref().len(),
            algorithm.digest_algorithm().output_len()
        );
        hmac::verify(&first, b"message", tag.as_ref()).unwrap();
        assert!(hmac::verify(&second, b"message", tag.as_ref()).is_err());
    }
}

/// A caller bounded by `RsaEncoding` reads its hash, as ring's `Padding`
/// gives it.
#[cfg(feature = "alloc")]
#[test]
fn rsa_encodings_name_their_digest() {
    use rind_ring::signature::{self, RsaEncoding};

    fn digest_of<E: RsaEncoding>(encoding: &E) -> &'static digest::Algorithm {
        encoding.digest_alg()
    }
    assert_eq!(digest_of(&signature::RSA_PKCS1_SHA256), &digest::SHA256);
    assert_eq!(digest_of(&signature::RSA_PKCS1_SHA384), &digest::SHA384);
    assert_eq!(digest_of(&signature::RSA_PKCS1_SHA512), &digest::SHA512);
    assert_eq!(digest_of(&signature::RSA_PSS_SHA256), &digest::SHA256);
    assert_eq!(digest_of(&signature::RSA_PSS_SHA384), &digest::SHA384);
    assert_eq!(digest_of(&signature::RSA_PSS_SHA512), &digest::SHA512);
}
