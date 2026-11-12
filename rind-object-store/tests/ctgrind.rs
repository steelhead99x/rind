//! Constant-time checks for each secret path, run under valgrind by
//! `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. rind itself marks the private keys it
//! parses.

use aws_lc_rs::{hmac, rand, signature};
use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use object_store::client::{DigestAlgorithm, SigningAlgorithm};
use rustls_pki_types::PrivateKeyDer;
use rustls_pki_types::pem::PemObject;

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

#[test]
fn hmac() {
    let key = *b"AWS4wJalrXUtnFEMI/K7MDENG/bPxRfiCYEXAMPLEKEY";
    let expected = hmac::sign(&hmac::Key::new(hmac::HMAC_SHA256, &key), b"20260101");

    secret(&key);
    let mut context = rind_object_store::default_provider()
        .hmac(DigestAlgorithm::Sha256, &key)
        .unwrap();
    context.update(b"2026");
    context.update(b"0101");
    let tag = context.finish().unwrap();

    public(tag);
    assert_eq!(tag, expected.as_ref());
}

#[test]
fn rs256() {
    for pem in [
        &include_bytes!("data/rsa2048.pkcs8.pem")[..],
        &include_bytes!("data/rsa2048.pkcs1.pem")[..],
    ] {
        let signer = rind_object_store::default_provider()
            .sign(SigningAlgorithm::RS256, pem)
            .unwrap();
        let signature = signer.sign(b"message").unwrap();
        public(&signature[..]);

        // RSASSA-PKCS1-v1_5 is deterministic, so the signatures must match exactly.
        let reference = match PrivateKeyDer::from_pem_slice(pem).unwrap() {
            PrivateKeyDer::Pkcs8(key) => {
                signature::RsaKeyPair::from_pkcs8(key.secret_pkcs8_der()).unwrap()
            }
            PrivateKeyDer::Pkcs1(key) => {
                signature::RsaKeyPair::from_der(key.secret_pkcs1_der()).unwrap()
            }
            _ => unreachable!(),
        };
        let mut expected = vec![0; reference.public_modulus_len()];
        reference
            .sign(
                &signature::RSA_PKCS1_SHA256,
                &rand::SystemRandom::new(),
                b"message",
                &mut expected,
            )
            .unwrap();
        assert_eq!(signature, expected);
    }
}
