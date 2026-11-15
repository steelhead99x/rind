// Copyright 2015-2016 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::encoding::AsDer;
use aws_lc_rs::signature::{
    ECDSA_P256_SHA256_FIXED_SIGNING, ECDSA_P521_SHA512_FIXED_SIGNING, EcdsaKeyPair, KeyPair,
};

#[test]
fn test_reject_wrong_curve() {
    let supported_algs = [
        &ECDSA_P256_SHA256_FIXED_SIGNING,
        &ECDSA_P521_SHA512_FIXED_SIGNING,
    ];

    for marshal_alg in supported_algs {
        let key_pair = EcdsaKeyPair::generate(marshal_alg).unwrap();
        let key_pair_doc = key_pair.to_pkcs8v1().unwrap();
        let key_pair_bytes = key_pair_doc.as_ref();

        for parse_alg in supported_algs {
            if parse_alg == marshal_alg {
                continue;
            }

            let result = EcdsaKeyPair::from_private_key_der(parse_alg, key_pair_bytes);
            assert!(result.is_err());
        }
    }
}

#[test]
fn test_from_private_key_der() {
    let key_pair = EcdsaKeyPair::generate(&ECDSA_P256_SHA256_FIXED_SIGNING).unwrap();

    let bytes_5208 = key_pair.to_pkcs8v1().unwrap();
    let bytes_5915 = key_pair.private_key().as_der().unwrap();

    let key_pair_5208 =
        EcdsaKeyPair::from_private_key_der(&ECDSA_P256_SHA256_FIXED_SIGNING, bytes_5208.as_ref())
            .unwrap();
    let key_pair_5915 =
        EcdsaKeyPair::from_private_key_der(&ECDSA_P256_SHA256_FIXED_SIGNING, bytes_5915.as_ref())
            .unwrap();

    // rind-aws-lc-rs: `EcdsaKeyPair`'s fields are private, so the keys' public
    // keys and algorithms are compared.
    assert_eq!(
        key_pair.public_key().as_ref(),
        key_pair_5208.public_key().as_ref()
    );
    assert_eq!(
        key_pair.public_key().as_ref(),
        key_pair_5915.public_key().as_ref()
    );
    assert_eq!(
        key_pair_5208.public_key().as_ref(),
        key_pair_5915.public_key().as_ref()
    );
    assert_eq!(key_pair_5915.algorithm(), &ECDSA_P256_SHA256_FIXED_SIGNING);
}
