//! Calls rind's provider and jsonwebtoken's aws-lc-rs provider side by side,
//! since only one provider can be installed per process.

mod common;

use common::Key;
use jsonwebtoken::crypto::{CryptoProvider, aws_lc};
use jsonwebtoken::errors::ErrorKind;
use jsonwebtoken::jwk::{EllipticCurve, ThumbprintHash};
use jsonwebtoken::{Algorithm, DecodingKey, EncodingKey};

const AWS_LC: &CryptoProvider = &aws_lc::DEFAULT_PROVIDER;

fn rind() -> &'static CryptoProvider {
    &rind_jsonwebtoken::DEFAULT_PROVIDER
}

const MESSAGE: &[u8] = b"eyJhbGciOiJub25lIn0.eyJzdWIiOiJyaW5kIn0";

fn sign(provider: &CryptoProvider, key: &Key, message: &[u8]) -> Vec<u8> {
    (provider.signer_factory)(&key.algorithm, &key.encoding)
        .unwrap_or_else(|e| panic!("{}: {e}", key.label()))
        .try_sign(message)
        .unwrap_or_else(|e| panic!("{}: {e}", key.label()))
}

fn verifies(provider: &CryptoProvider, key: &Key, message: &[u8], signature: &[u8]) -> bool {
    (provider.verifier_factory)(&key.algorithm, &key.decoding)
        .unwrap_or_else(|e| panic!("{}: {e}", key.label()))
        .verify(message, &signature.to_vec())
        .is_ok()
}

#[test]
fn signatures_verify_across_providers() {
    for key in common::all() {
        for (signer, verifier, direction) in [
            (rind(), AWS_LC, "rind to aws-lc-rs"),
            (AWS_LC, rind(), "aws-lc-rs to rind"),
            (rind(), rind(), "rind to rind"),
        ] {
            let label = format!("{} ({direction})", key.label());
            let signature = sign(signer, &key, MESSAGE);
            assert!(verifies(verifier, &key, MESSAGE, &signature), "{label}");
            assert!(!verifies(verifier, &key, b"other", &signature), "{label}");
        }
    }
}

#[test]
fn altered_signatures_fail_on_both_providers() {
    for key in common::all() {
        let signature = sign(rind(), &key, MESSAGE);

        let mut flipped = signature.clone();
        *flipped.last_mut().unwrap() ^= 1;
        let mut prepended = vec![0];
        prepended.extend_from_slice(&signature);
        let mut appended = signature.clone();
        appended.push(0);

        for (altered, how) in [
            (&flipped[..], "flipped bit"),
            (&prepended[..], "prepended zero"),
            (&appended[..], "appended zero"),
            (&signature[1..], "first byte removed"),
            (&signature[..signature.len() - 1], "last byte removed"),
            (&[][..], "empty"),
        ] {
            for (provider, name) in [(rind(), "rind"), (AWS_LC, "aws-lc-rs")] {
                assert!(
                    !verifies(provider, &key, MESSAGE, altered),
                    "{} accepted with a {how} by {name}",
                    key.label()
                );
            }
        }
    }
}

#[test]
fn key_of_another_family_is_refused() {
    let keys = common::all();
    for algorithm in keys.iter().map(|key| key.algorithm) {
        for key in keys
            .iter()
            .filter(|key| key.encoding.family() != algorithm.family())
        {
            let signer = (rind().signer_factory)(&algorithm, &key.encoding);
            assert_eq!(
                signer.err().map(|e| e.into_kind()),
                Some(ErrorKind::InvalidKeyFormat),
                "{algorithm:?} signer with {}",
                key.label()
            );
            let verifier = (rind().verifier_factory)(&algorithm, &key.decoding);
            assert_eq!(
                verifier.err().map(|e| e.into_kind()),
                Some(ErrorKind::InvalidKeyFormat),
                "{algorithm:?} verifier with {}",
                key.label()
            );
        }
    }
}

#[test]
fn malformed_keys_are_errors() {
    let (private, public) = common::rsa_key();
    let truncated = |der: &[u8]| der[..der.len() - 1].to_vec();
    let garbage = [0x30, 0x03, 0x02, 0x01, 0x00];

    let signers = [
        (Algorithm::ES256, EncodingKey::from_ec_der(&garbage)),
        (Algorithm::ES384, EncodingKey::from_ec_der(&garbage)),
        (Algorithm::EdDSA, EncodingKey::from_ed_der(&garbage)),
        (Algorithm::RS256, EncodingKey::from_rsa_der(&garbage)),
        (
            Algorithm::RS256,
            EncodingKey::from_rsa_der(&truncated(private)),
        ),
    ];
    for (algorithm, key) in signers {
        assert!(
            (rind().signer_factory)(&algorithm, &key).is_err(),
            "{algorithm:?}"
        );
    }

    let verifiers = [
        (Algorithm::ES256, DecodingKey::from_ec_der(&garbage)),
        // A P-384 point is the wrong size for P-256, and the reverse.
        (Algorithm::ES256, common_point(Algorithm::ES384)),
        (Algorithm::ES384, common_point(Algorithm::ES256)),
        (Algorithm::EdDSA, DecodingKey::from_ed_der(&garbage)),
        (Algorithm::RS256, DecodingKey::from_rsa_der(&garbage)),
        (
            Algorithm::RS256,
            DecodingKey::from_rsa_der(&truncated(public)),
        ),
        (
            Algorithm::RS256,
            DecodingKey::from_rsa_raw_components(&[], &[1, 0, 1]),
        ),
        // rind refuses moduli under 2048 bits.
        (
            Algorithm::RS256,
            DecodingKey::from_rsa_raw_components(&[0xff; 128], &[1, 0, 1]),
        ),
    ];
    for (algorithm, key) in verifiers {
        assert!(
            (rind().verifier_factory)(&algorithm, &key).is_err(),
            "{algorithm:?}"
        );
    }
}

fn common_point(algorithm: Algorithm) -> DecodingKey {
    common::all()
        .into_iter()
        .find(|key| key.algorithm == algorithm)
        .unwrap()
        .decoding
}

#[test]
fn key_utils_match_aws_lc() {
    let (private, public) = common::rsa_key();
    assert_eq!(
        (rind().key_utils.rsa_pub_components_from_private_key)(private).unwrap(),
        (AWS_LC.key_utils.rsa_pub_components_from_private_key)(private).unwrap(),
    );
    assert_eq!(
        (rind().key_utils.rsa_pub_components_from_public_key)(public).unwrap(),
        (AWS_LC.key_utils.rsa_pub_components_from_public_key)(public).unwrap(),
    );

    for key in common::all() {
        let der = key.encoding.as_bytes();
        match key.algorithm {
            Algorithm::ES256 | Algorithm::ES384 => assert_eq!(
                (rind().key_utils.ec_pub_components_from_private_key)(der, key.algorithm).unwrap(),
                (AWS_LC.key_utils.ec_pub_components_from_private_key)(der, key.algorithm).unwrap(),
                "{}",
                key.label()
            ),
            Algorithm::EdDSA => assert_eq!(
                (rind().key_utils.ed_pub_components_from_private_key)(der, &EllipticCurve::Ed25519)
                    .unwrap(),
                (AWS_LC.key_utils.ed_pub_components_from_private_key)(der, &EllipticCurve::Ed25519)
                    .unwrap(),
                "{}",
                key.label()
            ),
            _ => {}
        }
    }

    for hash in [
        ThumbprintHash::SHA256,
        ThumbprintHash::SHA384,
        ThumbprintHash::SHA512,
    ] {
        assert_eq!(
            (rind().key_utils.compute_digest)(MESSAGE, hash.clone()).unwrap(),
            (AWS_LC.key_utils.compute_digest)(MESSAGE, hash).unwrap(),
        );
    }
}
