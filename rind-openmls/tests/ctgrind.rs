//! Constant-time checks for each secret path, run under valgrind by
//! `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. rind itself marks the private keys it
//! generates or parses.

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use openmls_traits::crypto::OpenMlsCrypto;
use openmls_traits::types::{
    AeadType, HashType, HpkeAeadType, HpkeConfig, HpkeKdfType, HpkeKemType, SignatureScheme,
};
use rind_openmls::RustCrypto;

/// Marks `value` secret: memcheck flags any branch or index that depends on it.
fn secret<T: ?Sized>(value: &T) {
    mark(value, MemState::Undefined);
}

/// Marks `value` public, so the test may branch on it.
fn public<T: ?Sized>(value: &T) {
    mark(value, MemState::Defined);
}

fn mark<T: ?Sized>(value: &T, state: MemState) {
    if let RunningMode::Valgrind = valgrind::running_mode() {
        memcheck::mark_memory((value as *const T).cast(), size_of_val(value), state).unwrap();
    }
}

fn hex(s: &str) -> Vec<u8> {
    (0..s.len())
        .step_by(2)
        .map(|i| u8::from_str_radix(&s[i..i + 2], 16).unwrap())
        .collect()
}

#[test]
fn hkdf() {
    // RFC 5869's test case 1.
    let ikm = [0x0b; 22];
    secret(&ikm);
    let prk = RustCrypto::default()
        .hkdf_extract(HashType::Sha2_256, &hex("000102030405060708090a0b0c"), &ikm)
        .unwrap();
    let okm = RustCrypto::default()
        .hkdf_expand(
            HashType::Sha2_256,
            prk.as_slice(),
            &hex("f0f1f2f3f4f5f6f7f8f9"),
            42,
        )
        .unwrap();
    public(prk.as_slice());
    public(okm.as_slice());
    assert_eq!(
        prk.as_slice(),
        hex("077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5")
    );
    assert_eq!(
        okm.as_slice(),
        hex("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865")
    );
}

#[test]
fn aead() {
    for (alg, len) in [
        (AeadType::Aes128Gcm, 16),
        (AeadType::Aes256Gcm, 32),
        (AeadType::ChaCha20Poly1305, 32),
    ] {
        let key = vec![0x42; len];
        secret(key.as_slice());
        let sealed = RustCrypto::default()
            .aead_encrypt(alg, &key, b"plaintext", &[0x24; 12], b"aad")
            .unwrap();
        public(sealed.as_slice());
        let opened = RustCrypto::default()
            .aead_decrypt(alg, &key, &sealed, &[0x24; 12], b"aad")
            .unwrap();
        public(opened.as_slice());
        assert_eq!(opened, b"plaintext");
    }
}

#[test]
fn signatures() {
    for scheme in [
        SignatureScheme::ED25519,
        SignatureScheme::ECDSA_SECP256R1_SHA256,
        SignatureScheme::ECDSA_SECP384R1_SHA384,
    ] {
        let crypto = RustCrypto::default();
        let (private, public_key) = crypto.signature_key_gen(scheme).unwrap();
        secret(private.as_slice());
        let signature = crypto.sign(scheme, b"data", &private).unwrap();
        public(signature.as_slice());
        crypto
            .verify_signature(scheme, b"data", &public_key, &signature)
            .unwrap();
    }
}

#[test]
fn hpke() {
    for kem in [
        HpkeKemType::DhKem25519,
        HpkeKemType::DhKemP256,
        HpkeKemType::DhKemP384,
    ] {
        let config = || HpkeConfig(kem, HpkeKdfType::HkdfSha256, HpkeAeadType::AesGcm128);
        let crypto = RustCrypto::default();
        let ikm = [0x42; 66];
        secret(&ikm);
        let key = crypto.derive_hpke_keypair(config(), &ikm).unwrap();
        public(key.public.as_slice());

        let sealed = crypto
            .hpke_seal(config(), &key.public, b"info", b"aad", b"plaintext")
            .unwrap();
        public(sealed.kem_output.as_slice());
        public(sealed.ciphertext.as_slice());
        let opened = crypto
            .hpke_open(config(), &sealed, &key.private, b"info", b"aad")
            .unwrap();
        public(opened.as_slice());
        assert_eq!(opened, b"plaintext");

        let (enc, ours) = crypto
            .hpke_setup_sender_and_export(config(), &key.public, b"info", b"context", 32)
            .unwrap();
        let theirs = crypto
            .hpke_setup_receiver_and_export(config(), &enc, &key.private, b"info", b"context", 32)
            .unwrap();
        public(&*ours);
        public(&*theirs);
        assert_eq!(&*ours, &*theirs);
    }
}
