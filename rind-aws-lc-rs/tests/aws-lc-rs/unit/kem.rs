// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::kem::{
    Algorithm, Ciphertext, DecapsulationKey, EncapsulationKey, ML_KEM_512, ML_KEM_768, ML_KEM_1024,
};

// rind-aws-lc-rs: `Ciphertext::new`, `SharedSecret::new`, `KeyRejected::too_small`
// and `too_large`, and the algorithms' key and secret sizes are private, so
// `shared_secret` is left out, `ciphertext` builds its second ciphertext with
// `From`, the refusals compare their descriptions, and `sizes` gives the sizes.

/// An algorithm's `(decapsulation key, encapsulation key, shared secret)` sizes.
fn sizes(algorithm: &Algorithm) -> (usize, usize, usize) {
    if algorithm == &ML_KEM_512 {
        (1632, 800, 32)
    } else if algorithm == &ML_KEM_768 {
        (2400, 1184, 32)
    } else {
        (3168, 1568, 32)
    }
}

#[test]
fn ciphertext() {
    let ciphertext_bytes = vec![42u8; 4];
    let ciphertext = Ciphertext::from(ciphertext_bytes.as_ref());
    assert_eq!(ciphertext.as_ref(), &[42, 42, 42, 42]);
    drop(ciphertext);
}

#[test]
fn test_kem_serialize() {
    for algorithm in [&ML_KEM_512, &ML_KEM_768, &ML_KEM_1024] {
        let priv_key = DecapsulationKey::generate(algorithm).unwrap();
        assert_eq!(priv_key.algorithm(), algorithm);

        // Test DecapsulationKey serialization
        let priv_key_raw_bytes = priv_key.key_bytes().unwrap();
        assert_eq!(priv_key_raw_bytes.as_ref().len(), sizes(algorithm).0);
        let priv_key_from_bytes =
            DecapsulationKey::new(algorithm, priv_key_raw_bytes.as_ref()).unwrap();

        assert_eq!(
            priv_key.key_bytes().unwrap().as_ref(),
            priv_key_from_bytes.key_bytes().unwrap().as_ref()
        );
        assert_eq!(priv_key.algorithm(), priv_key_from_bytes.algorithm());

        // Test EncapsulationKey serialization
        let pub_key = priv_key.encapsulation_key().unwrap();
        let pubkey_raw_bytes = pub_key.key_bytes().unwrap();
        let pub_key_from_bytes =
            EncapsulationKey::new(algorithm, pubkey_raw_bytes.as_ref()).unwrap();

        assert_eq!(
            pub_key.key_bytes().unwrap().as_ref(),
            pub_key_from_bytes.key_bytes().unwrap().as_ref()
        );
        assert_eq!(pub_key.algorithm(), pub_key_from_bytes.algorithm());
    }
}

#[test]
fn test_kem_wrong_sizes() {
    for algorithm in [&ML_KEM_512, &ML_KEM_768, &ML_KEM_1024] {
        // Test EncapsulationKey size validation
        let too_long_bytes = vec![0u8; sizes(algorithm).1 + 1];
        let long_pub_key_from_bytes = EncapsulationKey::new(algorithm, &too_long_bytes);
        assert_eq!(
            long_pub_key_from_bytes.err().map(|e| e.description_()),
            Some("TooLarge")
        );

        let too_short_bytes = vec![0u8; sizes(algorithm).1 - 1];
        let short_pub_key_from_bytes = EncapsulationKey::new(algorithm, &too_short_bytes);
        assert_eq!(
            short_pub_key_from_bytes.err().map(|e| e.description_()),
            Some("TooSmall")
        );

        // Test DecapsulationKey size validation
        let too_long_bytes = vec![0u8; sizes(algorithm).0 + 1];
        let long_priv_key_from_bytes = DecapsulationKey::new(algorithm, &too_long_bytes);
        assert_eq!(
            long_priv_key_from_bytes.err().map(|e| e.description_()),
            Some("TooLarge")
        );

        let too_short_bytes = vec![0u8; sizes(algorithm).0 - 1];
        let short_priv_key_from_bytes = DecapsulationKey::new(algorithm, &too_short_bytes);
        assert_eq!(
            short_priv_key_from_bytes.err().map(|e| e.description_()),
            Some("TooSmall")
        );
    }
}

#[test]
fn test_kem_e2e() {
    for algorithm in [&ML_KEM_512, &ML_KEM_768, &ML_KEM_1024] {
        let priv_key = DecapsulationKey::generate(algorithm).unwrap();
        assert_eq!(priv_key.algorithm(), algorithm);

        // Serialize and reconstruct the decapsulation key
        let priv_key_bytes = priv_key.key_bytes().unwrap();
        let priv_key_from_bytes =
            DecapsulationKey::new(algorithm, priv_key_bytes.as_ref()).unwrap();

        // rind-aws-lc-rs: a key reconstructed from bytes does provide
        // encapsulation_key(), since the expanded form holds it.
        assert_eq!(
            priv_key_from_bytes
                .encapsulation_key()
                .unwrap()
                .key_bytes()
                .unwrap()
                .as_ref(),
            priv_key
                .encapsulation_key()
                .unwrap()
                .key_bytes()
                .unwrap()
                .as_ref()
        );

        let pub_key = priv_key.encapsulation_key().unwrap();

        let (alice_ciphertext, alice_secret) =
            pub_key.encapsulate().expect("encapsulate successful");

        // Decapsulate using the reconstructed key
        let bob_secret = priv_key_from_bytes
            .decapsulate(alice_ciphertext)
            .expect("decapsulate successful");

        assert_eq!(alice_secret.as_ref(), bob_secret.as_ref());
    }
}

#[test]
fn test_serialized_kem_e2e() {
    for algorithm in [&ML_KEM_512, &ML_KEM_768, &ML_KEM_1024] {
        let priv_key = DecapsulationKey::generate(algorithm).unwrap();
        assert_eq!(priv_key.algorithm(), algorithm);

        let pub_key = priv_key.encapsulation_key().unwrap();

        // Generate public key bytes to send to bob
        let pub_key_bytes = pub_key.key_bytes().unwrap();

        // Generate private key bytes for alice to store securely
        let priv_key_bytes = priv_key.key_bytes().unwrap();

        // Test that priv_key's EVP_PKEY isn't entirely freed since we remove this pub_key's reference.
        drop(pub_key);
        drop(priv_key);

        let retrieved_pub_key = EncapsulationKey::new(algorithm, pub_key_bytes.as_ref()).unwrap();
        let (ciphertext, bob_secret) = retrieved_pub_key
            .encapsulate()
            .expect("encapsulate successful");

        // Alice reconstructs her private key from stored bytes
        let retrieved_priv_key = DecapsulationKey::new(algorithm, priv_key_bytes.as_ref()).unwrap();
        let alice_secret = retrieved_priv_key
            .decapsulate(ciphertext)
            .expect("decapsulate successful");

        assert_eq!(alice_secret.as_ref(), bob_secret.as_ref());
    }
}

#[test]
fn test_decapsulation_key_serialization_roundtrip() {
    for algorithm in [&ML_KEM_512, &ML_KEM_768, &ML_KEM_1024] {
        // Generate original key
        let original_key = DecapsulationKey::generate(algorithm).unwrap();

        // Test key_bytes() returns correct size
        let key_bytes = original_key.key_bytes().unwrap();
        assert_eq!(key_bytes.as_ref().len(), sizes(algorithm).0);

        // Test round-trip serialization/deserialization
        let reconstructed_key = DecapsulationKey::new(algorithm, key_bytes.as_ref()).unwrap();

        // Verify algorithm consistency
        assert_eq!(original_key.algorithm(), reconstructed_key.algorithm());
        assert_eq!(original_key.algorithm(), algorithm);

        // Test serialization produces identical bytes (stability check)
        let key_bytes_2 = reconstructed_key.key_bytes().unwrap();
        assert_eq!(key_bytes.as_ref(), key_bytes_2.as_ref());

        // Test functional equivalence: both keys decrypt the same ciphertext identically
        let pub_key = original_key.encapsulation_key().unwrap();
        let (ciphertext, expected_secret) = pub_key.encapsulate().expect("encapsulate successful");

        let secret_from_original = original_key
            .decapsulate(Ciphertext::from(ciphertext.as_ref()))
            .expect("decapsulate with original key");
        let secret_from_reconstructed = reconstructed_key
            .decapsulate(Ciphertext::from(ciphertext.as_ref()))
            .expect("decapsulate with reconstructed key");

        // Verify both keys produce identical secrets
        assert_eq!(expected_secret.as_ref(), secret_from_original.as_ref());
        assert_eq!(expected_secret.as_ref(), secret_from_reconstructed.as_ref());

        // Verify secret length matches algorithm specification
        assert_eq!(expected_secret.as_ref().len(), sizes(algorithm).2);
    }
}

#[test]
fn test_decapsulation_key_zeroed_bytes() {
    // rind-aws-lc-rs: aws-lc-rs accepts zeroed bytes of the correct size and
    // fails only when the key decapsulates; rind refuses them when loaded,
    // as they are not a well-formed key (`H(ek)` does not match).
    for algorithm in [&ML_KEM_512, &ML_KEM_768, &ML_KEM_1024] {
        let zeroed_bytes = vec![0u8; sizes(algorithm).0];
        assert!(
            DecapsulationKey::new(algorithm, &zeroed_bytes).is_err(),
            "DecapsulationKey::new should refuse zeroed bytes for {:?}",
            algorithm.id()
        );
    }
}

#[test]
fn test_cross_algorithm_key_rejection() {
    // Test that keys from one algorithm are rejected when used with a different algorithm
    // due to size mismatches.
    let algorithms = [&ML_KEM_512, &ML_KEM_768, &ML_KEM_1024];

    for source_alg in &algorithms {
        let key = DecapsulationKey::generate(source_alg).unwrap();
        let key_bytes = key.key_bytes().unwrap();

        for target_alg in &algorithms {
            if source_alg.id() == target_alg.id() {
                // Same algorithm should succeed
                let result = DecapsulationKey::new(target_alg, key_bytes.as_ref());
                assert!(
                    result.is_ok(),
                    "Same algorithm should accept its own key bytes"
                );
            } else {
                // Different algorithm should fail due to size mismatch
                let result = DecapsulationKey::new(target_alg, key_bytes.as_ref());
                assert!(
                    result.is_err(),
                    "Algorithm {:?} should reject key bytes from {:?}",
                    target_alg.id(),
                    source_alg.id()
                );

                // Verify the error is size-related
                let err = result.err().unwrap();
                let source_size = sizes(source_alg).0;
                let target_size = sizes(target_alg).0;
                if source_size < target_size {
                    assert_eq!(
                        err.description_(),
                        "TooSmall",
                        "Smaller key should be rejected as too_small"
                    );
                } else {
                    assert_eq!(
                        err.description_(),
                        "TooLarge",
                        "Larger key should be rejected as too_large"
                    );
                }
            }
        }
    }

    // Also test EncapsulationKey cross-algorithm rejection for completeness
    for source_alg in &algorithms {
        let decap_key = DecapsulationKey::generate(source_alg).unwrap();
        let encap_key = decap_key.encapsulation_key().unwrap();
        let key_bytes = encap_key.key_bytes().unwrap();

        for target_alg in &algorithms {
            if source_alg.id() == target_alg.id() {
                let result = EncapsulationKey::new(target_alg, key_bytes.as_ref());
                assert!(
                    result.is_ok(),
                    "Same algorithm should accept its own encapsulation key bytes"
                );
            } else {
                let result = EncapsulationKey::new(target_alg, key_bytes.as_ref());
                assert!(
                    result.is_err(),
                    "Algorithm {:?} should reject encapsulation key bytes from {:?}",
                    target_alg.id(),
                    source_alg.id()
                );
            }
        }
    }
}

#[test]
fn test_debug_fmt() {
    let private = DecapsulationKey::generate(&ML_KEM_512).expect("successful generation");
    assert_eq!(
        format!("{private:?}"),
        "DecapsulationKey { algorithm: MlKem512, .. }"
    );
    assert_eq!(
        format!(
            "{:?}",
            private.encapsulation_key().expect("public key retrievable")
        ),
        "EncapsulationKey { algorithm: MlKem512, .. }"
    );
}
