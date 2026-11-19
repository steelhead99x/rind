// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::encoding::AsDer;
use aws_lc_rs::signature::{
    KeyPair, ML_DSA_44, ML_DSA_44_SIGNING, ML_DSA_65, ML_DSA_65_SIGNING, ML_DSA_87,
    ML_DSA_87_SIGNING, PqdsaKeyPair, PqdsaSigningAlgorithm, PqdsaVerificationAlgorithm,
    UnparsedPublicKey,
};

// rind-aws-lc-rs: each signing algorithm is paired with its verification
// algorithm, which aws-lc-rs reads from a private field. The tests of
// `PqdsaPrivateKey::as_raw_bytes`, which is not offered, are left out.
const TEST_ALGORITHMS: &[(&PqdsaSigningAlgorithm, &PqdsaVerificationAlgorithm)] = &[
    (&ML_DSA_44_SIGNING, &ML_DSA_44),
    (&ML_DSA_65_SIGNING, &ML_DSA_65),
    (&ML_DSA_87_SIGNING, &ML_DSA_87),
];

#[test]
fn test_public_key_serialization() {
    for &(alg, verify_alg) in TEST_ALGORITHMS {
        // Generate a new key pair
        let keypair = PqdsaKeyPair::generate(alg).unwrap();
        let message = b"Test message";
        let different_message = b"Different message";
        let mut signature = vec![0; alg.signature_len()];
        assert!(
            keypair
                .sign(message, &mut signature[0..(alg.signature_len() - 1)])
                .is_err()
        );
        let sig_len = keypair.sign(message, &mut signature).unwrap();
        assert_eq!(sig_len, alg.signature_len());
        let invalid_signature = vec![0u8; alg.signature_len()];

        let original_public_key = keypair.public_key();

        let x509_der = original_public_key.as_der().unwrap();
        let x509_public_key = UnparsedPublicKey::new(verify_alg, x509_der.as_ref());
        assert!(x509_public_key.verify(message, signature.as_ref()).is_ok());
        assert!(
            x509_public_key
                .verify(different_message, signature.as_ref())
                .is_err()
        );
        assert!(x509_public_key.verify(message, &invalid_signature).is_err());

        let raw = original_public_key.as_ref();
        let raw_public_key = UnparsedPublicKey::new(verify_alg, raw);
        assert!(raw_public_key.verify(message, signature.as_ref()).is_ok());
        assert!(
            raw_public_key
                .verify(different_message, signature.as_ref())
                .is_err()
        );
        assert!(
            raw_public_key
                .verify(different_message, &invalid_signature)
                .is_err()
        );

        #[cfg(feature = "ring-sig-verify")]
        #[allow(deprecated)]
        {
            use aws_lc_rs::signature::VerificationAlgorithm;
            assert!(
                verify_alg
                    .verify(
                        raw.into(),
                        message.as_ref().into(),
                        signature.as_slice().into()
                    )
                    .is_ok()
            );
        }
    }
}

#[test]
fn test_from_seed() {
    for &(alg, verify_alg) in TEST_ALGORITHMS {
        let seed = [1u8; 32];
        let kp = PqdsaKeyPair::from_seed(alg, &seed).unwrap();
        assert_eq!(kp.algorithm(), alg);
        // Verify key works for signing
        let msg = b"seed test";
        let mut sig = vec![0u8; alg.signature_len()];
        let sig_len = kp.sign(msg, &mut sig).unwrap();
        assert_eq!(sig_len, alg.signature_len());
        let public_key = UnparsedPublicKey::new(verify_alg, kp.public_key().as_ref());
        public_key.verify(msg, &sig).unwrap();
    }
}

#[test]
fn test_from_seed_deterministic() {
    for &(alg, _) in TEST_ALGORITHMS {
        let seed = [42u8; 32];
        let kp1 = PqdsaKeyPair::from_seed(alg, &seed).unwrap();
        let kp2 = PqdsaKeyPair::from_seed(alg, &seed).unwrap();
        assert_eq!(kp1.public_key().as_ref(), kp2.public_key().as_ref());
    }
}

#[test]
fn test_from_seed_wrong_size() {
    // rind-aws-lc-rs: `KeyRejected::too_small` and `too_large` are private, so
    // the reasons are compared through `description_`.
    for &(alg, _) in TEST_ALGORITHMS {
        let reason = |seed: &[u8]| {
            PqdsaKeyPair::from_seed(alg, seed)
                .err()
                .map(|e| e.description_())
        };
        assert_eq!(reason(&[0u8; 31]), Some("TooSmall"));
        assert_eq!(reason(&[0u8; 33]), Some("TooLarge"));
        assert_eq!(reason(&[]), Some("TooSmall"));
    }
}

#[test]
fn test_from_seed_different_seeds_different_keys() {
    for &(alg, _) in TEST_ALGORITHMS {
        let kp1 = PqdsaKeyPair::from_seed(alg, &[1u8; 32]).unwrap();
        let kp2 = PqdsaKeyPair::from_seed(alg, &[2u8; 32]).unwrap();
        assert_ne!(kp1.public_key().as_ref(), kp2.public_key().as_ref());
    }
}

#[test]
fn test_from_seed_pkcs8_roundtrip() {
    for &(alg, _) in TEST_ALGORITHMS {
        let seed = [77u8; 32];
        let kp = PqdsaKeyPair::from_seed(alg, &seed).unwrap();
        let pkcs8 = kp.to_pkcs8v1().unwrap();
        let kp2 = PqdsaKeyPair::from_pkcs8(alg, pkcs8.as_ref()).unwrap();
        assert_eq!(kp.public_key().as_ref(), kp2.public_key().as_ref());
    }
}

#[test]
fn test_from_seed_same_seed_different_algorithms() {
    // Same seed with different algorithms should produce different keys
    let seed = [42u8; 32];
    let kp_44 = PqdsaKeyPair::from_seed(&ML_DSA_44_SIGNING, &seed).unwrap();
    let kp_65 = PqdsaKeyPair::from_seed(&ML_DSA_65_SIGNING, &seed).unwrap();
    let kp_87 = PqdsaKeyPair::from_seed(&ML_DSA_87_SIGNING, &seed).unwrap();
    // Public keys have different sizes across algorithms, so they must differ
    assert_ne!(
        kp_44.public_key().as_ref().len(),
        kp_65.public_key().as_ref().len()
    );
    assert_ne!(
        kp_65.public_key().as_ref().len(),
        kp_87.public_key().as_ref().len()
    );
}

// `from_raw_private_key` documents that it expects the *expanded* form of the
// raw private key bytes, not the 32-byte seed. Feeding it a seed-sized input
// must be rejected rather than silently misinterpreted.
#[test]
fn test_from_raw_private_key_rejects_seed() {
    for &(alg, _) in TEST_ALGORITHMS {
        // A 32-byte seed is far smaller than any expanded private key, so it
        // must not be accepted as an expanded key.
        assert!(PqdsaKeyPair::from_raw_private_key(alg, &[7u8; 32]).is_err());
    }
}

// `from_pkcs8` documents that it accepts the seed encoding, and `to_pkcs8v1`
// documents that it prefers the seed. A seed -> PKCS#8 -> key pair -> PKCS#8
// round-trip must therefore preserve the seed form byte-for-byte.
#[test]
fn test_from_seed_pkcs8_roundtrip_preserves_seed_form() {
    for &(alg, _) in TEST_ALGORITHMS {
        let kp = PqdsaKeyPair::from_seed(alg, &[8u8; 32]).unwrap();
        let pkcs8 = kp.to_pkcs8v1().unwrap();
        let reparsed = PqdsaKeyPair::from_pkcs8(alg, pkcs8.as_ref()).unwrap();
        let pkcs8_again = reparsed.to_pkcs8v1().unwrap();
        // Seed is retained through parsing, so re-serialization is identical.
        assert_eq!(pkcs8.as_ref(), pkcs8_again.as_ref());
        // And the reconstructed key pair is the same key.
        assert_eq!(kp.public_key().as_ref(), reparsed.public_key().as_ref());
    }
}

// `PqdsaPrivateKey::as_der` documents that it uses the representation chosen by
// `to_pkcs8v1`. For a seed-derived key that representation is the seed form, so
// `as_der` and `to_pkcs8v1` must agree.
#[test]
fn test_from_seed_as_der_matches_to_pkcs8v1() {
    for &(alg, _) in TEST_ALGORITHMS {
        let kp = PqdsaKeyPair::from_seed(alg, &[11u8; 32]).unwrap();
        let pkcs8 = kp.to_pkcs8v1().unwrap();
        let der = kp.private_key().as_der().unwrap();
        assert_eq!(pkcs8.as_ref(), der.as_ref());
    }
}

// Additional test for the algorithm getter
#[test]
fn test_algorithm_getter() {
    for &(alg, _) in TEST_ALGORITHMS {
        let keypair = PqdsaKeyPair::generate(alg).unwrap();
        assert_eq!(keypair.algorithm(), alg);
    }
}

#[test]
fn test_algorithm_lengths() {
    for (alg, signature_len, public_key_len) in [
        (&ML_DSA_44_SIGNING, 2420, 1312),
        (&ML_DSA_65_SIGNING, 3309, 1952),
        (&ML_DSA_87_SIGNING, 4627, 2592),
    ] {
        assert_eq!(alg.signature_len(), signature_len);
        assert_eq!(alg.public_key_len(), public_key_len);
        assert_eq!(alg.seed_len(), 32);
    }
}

// The deprecated `to_pkcs8` alias is retained for consumers of the `unstable`
// feature; it must produce the same encoding as `to_pkcs8v1`.
#[cfg(feature = "unstable")]
#[allow(deprecated)]
#[test]
fn test_to_pkcs8_deprecated_alias() {
    for &(alg, _) in TEST_ALGORITHMS {
        let kp = PqdsaKeyPair::from_seed(alg, &[9u8; 32]).unwrap();
        assert_eq!(
            kp.to_pkcs8().unwrap().as_ref(),
            kp.to_pkcs8v1().unwrap().as_ref()
        );
    }
}

#[test]
fn test_debug() {
    for &(alg, _) in TEST_ALGORITHMS {
        let keypair = PqdsaKeyPair::generate(alg).unwrap();
        assert!(
            format!("{keypair:?}").starts_with(
                "PqdsaKeyPair { algorithm: PqdsaSigningAlgorithm(PqdsaVerificationAlgorithm { id:"
            ),
            "{keypair:?}"
        );
        let pubkey = keypair.public_key();
        assert!(
            format!("{pubkey:?}").starts_with("PqdsaPublicKey("),
            "{pubkey:?}"
        );
        let privkey = keypair.private_key();
        assert!(
            format!("{privkey:?}").starts_with("PqdsaPrivateKey("),
            "{privkey:?}"
        );
    }
}
