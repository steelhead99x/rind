//! Constant-time checks for each secret path, run under valgrind by
//! `admin/ctgrind`.
//!
//! Secret inputs are marked undefined, so memcheck flags any branch or memory
//! index that depends on them. Outputs that are public by design are marked
//! defined before the test checks them. rind itself marks the private keys it
//! parses.

mod common;

use crabgrind::memcheck::{self, MemState};
use crabgrind::valgrind::{self, RunningMode};
use jsonwebtoken::Algorithm;
use jsonwebtoken::jwk::EllipticCurve;

const MESSAGE: &[u8] = b"eyJhbGciOiJub25lIn0.eyJzdWIiOiJyaW5kIn0";

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
fn sign_and_verify() {
    let provider = &rind_jsonwebtoken::DEFAULT_PROVIDER;
    for key in common::all() {
        if common::HMAC.contains(&key.algorithm) {
            secret(key.encoding.as_bytes());
            secret(key.decoding.try_get_as_bytes().unwrap());
        }

        let signature = (provider.signer_factory)(&key.algorithm, &key.encoding)
            .unwrap()
            .try_sign(MESSAGE)
            .unwrap();
        public(&signature[..]);

        (provider.verifier_factory)(&key.algorithm, &key.decoding)
            .unwrap()
            .verify(MESSAGE, &signature)
            .unwrap_or_else(|e| panic!("{}: {e}", key.label()));
    }
}

#[test]
fn public_components() {
    let provider = &rind_jsonwebtoken::DEFAULT_PROVIDER;
    let utils = &provider.key_utils;
    for key in common::all() {
        let der = key.encoding.as_bytes();
        match key.algorithm {
            Algorithm::ES256 | Algorithm::ES384 => {
                let (_, x, y) = (utils.ec_pub_components_from_private_key)(der, key.algorithm)
                    .unwrap_or_else(|e| panic!("{}: {e}", key.label()));
                public(&x[..]);
                public(&y[..]);
                assert_eq!(x.len(), y.len(), "{}", key.label());
            }
            Algorithm::EdDSA => {
                let x = (utils.ed_pub_components_from_private_key)(der, &EllipticCurve::Ed25519)
                    .unwrap_or_else(|e| panic!("{}: {e}", key.label()));
                public(&x[..]);
                assert_eq!(x.len(), 32, "{}", key.label());
            }
            Algorithm::RS256 => {
                let (n, e) = (utils.rsa_pub_components_from_private_key)(der)
                    .unwrap_or_else(|e| panic!("{}: {e}", key.label()));
                public(&n[..]);
                public(&e[..]);
                assert_eq!(n.len(), 256, "{}", key.label());
            }
            _ => {}
        }
    }
}
