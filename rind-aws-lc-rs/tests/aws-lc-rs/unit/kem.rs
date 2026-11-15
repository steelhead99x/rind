// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::kem::{Ciphertext, EncapsulationKey, ML_KEM_768};

// rind-aws-lc-rs: ML-KEM-512, ML-KEM-1024, `DecapsulationKey::new`, and
// `DecapsulationKey::key_bytes` are not offered, so the tests that need them
// are left out, and the rest run on ML-KEM-768 alone. `Ciphertext::new`,
// `SharedSecret::new`, and `KeyRejected::too_small` and `too_large` are
// private, so `shared_secret` is left out, `ciphertext` builds its second
// ciphertext with `From`, and the refusals compare their descriptions.

#[test]
fn ciphertext() {
    let ciphertext_bytes = vec![42u8; 4];
    let ciphertext = Ciphertext::from(ciphertext_bytes.as_ref());
    assert_eq!(ciphertext.as_ref(), &[42, 42, 42, 42]);
    drop(ciphertext);
}

#[test]
fn test_kem_wrong_sizes() {
    // rind-aws-lc-rs: `Algorithm::encapsulate_key_size` is private.
    const ENCAPSULATE_KEY_SIZE: usize = 1184;
    {
        let algorithm = &ML_KEM_768;
        // Test EncapsulationKey size validation
        let too_long_bytes = vec![0u8; ENCAPSULATE_KEY_SIZE + 1];
        let long_pub_key_from_bytes = EncapsulationKey::new(algorithm, &too_long_bytes);
        assert_eq!(
            long_pub_key_from_bytes.err().map(|e| e.description_()),
            Some("TooLarge")
        );

        let too_short_bytes = vec![0u8; ENCAPSULATE_KEY_SIZE - 1];
        let short_pub_key_from_bytes = EncapsulationKey::new(algorithm, &too_short_bytes);
        assert_eq!(
            short_pub_key_from_bytes.err().map(|e| e.description_()),
            Some("TooSmall")
        );
    }
}
