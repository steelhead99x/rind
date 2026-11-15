// Copyright 2015-2016 Brian Smith.
// SPDX-License-Identifier: ISC
// Modifications copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0 OR ISC

use aws_lc_rs::encoding::{AsBigEndian, AsDer, Pkcs8V1Der, Pkcs8V2Der, PublicKeyX509Der};
use aws_lc_rs::rand::SystemRandom;
use aws_lc_rs::signature::{ED25519, Ed25519KeyPair, KeyPair, UnparsedPublicKey};

use crate::test;

#[test]
fn test_generate() {
    const MESSAGE: &[u8] = b"test message";
    let key_pair = Ed25519KeyPair::generate().unwrap();
    let public_key = key_pair.public_key();
    let signature = key_pair.sign(MESSAGE);
    let unparsed_public_key = UnparsedPublicKey::new(&ED25519, public_key.as_ref());
    unparsed_public_key
        .verify(MESSAGE, signature.as_ref())
        .unwrap();
}

// rind-aws-lc-rs: `Ed25519KeyPair::public_key` is a private field, so its
// `KeyPair::public_key` is compared.
#[test]
fn test_generate_pkcs8() {
    let rng = SystemRandom::new();
    let document = Ed25519KeyPair::generate_pkcs8(&rng).unwrap();
    let kp1: Ed25519KeyPair = Ed25519KeyPair::from_pkcs8(document.as_ref()).unwrap();
    assert_eq!(
        document.as_ref(),
        AsDer::<Pkcs8V2Der>::as_der(&kp1).unwrap().as_ref()
    );
    let kp2: Ed25519KeyPair =
        Ed25519KeyPair::from_pkcs8_maybe_unchecked(document.as_ref()).unwrap();
    assert_eq!(
        kp1.seed().unwrap().as_be_bytes().unwrap().as_ref(),
        kp2.seed().unwrap().as_be_bytes().unwrap().as_ref(),
    );
    assert_eq!(kp1.public_key().as_ref(), kp2.public_key().as_ref());

    let document = Ed25519KeyPair::generate_pkcs8v1(&rng).unwrap();
    let kp1: Ed25519KeyPair = Ed25519KeyPair::from_pkcs8(document.as_ref()).unwrap();
    assert_eq!(
        document.as_ref(),
        AsDer::<Pkcs8V1Der>::as_der(&kp1).unwrap().as_ref()
    );
    let kp2: Ed25519KeyPair =
        Ed25519KeyPair::from_pkcs8_maybe_unchecked(document.as_ref()).unwrap();
    assert_eq!(
        kp1.seed().unwrap().as_be_bytes().unwrap().as_ref(),
        kp2.seed().unwrap().as_be_bytes().unwrap().as_ref(),
    );
    assert_eq!(kp1.public_key().as_ref(), kp2.public_key().as_ref());
    let seed = kp1.seed().unwrap();
    assert_eq!("Ed25519Seed()", format!("{seed:?}"));
}

#[test]
fn test_from_pkcs8() {
    struct TestCase {
        key: &'static str,
        expected_public: &'static str,
    }

    for case in [
        TestCase {
            key: "302e020100300506032b6570042204209d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
            expected_public: "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a",
        },
        TestCase {
            key: "3051020101300506032b657004220420756434bd5b824753007a138d27abbc14b5cc786adb78fb62435e6419a2b2e72b8121000faccd81e57de15fa6343a7fbb43b2b93f28be6435100ae8bd633c6dfee3d198",
            expected_public: "0faccd81e57de15fa6343a7fbb43b2b93f28be6435100ae8bd633c6dfee3d198",
        },
        TestCase {
            key: "304f020100300506032b657004220420d4ee72dbf913584ad5b6d8f1f769f8ad3afe7c28cbf1d4fbe097a88f44755842a01f301d060a2a864886f70d01090914310f0c0d437572646c6520436861697273",
            expected_public: "19bf44096984cdfe8541bac167dc3b96c85086aa30b6b6cb0c5c38ad703166e1",
        },
        TestCase {
            key: "3072020101300506032b657004220420d4ee72dbf913584ad5b6d8f1f769f8ad3afe7c28cbf1d4fbe097a88f44755842a01f301d060a2a864886f70d01090914310f0c0d437572646c652043686169727381210019bf44096984cdfe8541bac167dc3b96c85086aa30b6b6cb0c5c38ad703166e1",
            expected_public: "19bf44096984cdfe8541bac167dc3b96c85086aa30b6b6cb0c5c38ad703166e1",
        },
    ] {
        let key_pair = Ed25519KeyPair::from_pkcs8(&test::from_dirty_hex(case.key)).unwrap();
        assert_eq!(
            format!(
                r#"Ed25519KeyPair {{ public_key: PublicKey("{}") }}"#,
                case.expected_public
            ),
            format!("{key_pair:?}")
        );
        let key_pair =
            Ed25519KeyPair::from_pkcs8_maybe_unchecked(&test::from_dirty_hex(case.key)).unwrap();
        assert_eq!(
            format!(
                r#"Ed25519KeyPair {{ public_key: PublicKey("{}") }}"#,
                case.expected_public
            ),
            format!("{key_pair:?}")
        );
    }
}

#[test]
fn test_public_key_as_der_x509() {
    let key_pair = Ed25519KeyPair::from_pkcs8(&test::from_hex("302e020100300506032b6570042204209d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60").unwrap()).unwrap();
    let public_key = key_pair.public_key();
    let x509der = AsDer::<PublicKeyX509Der>::as_der(public_key).unwrap();
    assert_eq!(
        x509der.as_ref(),
        &[
            0x30, 0x2a, 0x30, 0x05, 0x06, 0x03, 0x2b, 0x65, 0x70, 0x03, 0x21, 0x00, 0xd7, 0x5a,
            0x98, 0x01, 0x82, 0xb1, 0x0a, 0xb7, 0xd5, 0x4b, 0xfe, 0xd3, 0xc9, 0x64, 0x07, 0x3a,
            0x0e, 0xe1, 0x72, 0xf3, 0xda, 0xa6, 0x23, 0x25, 0xaf, 0x02, 0x1a, 0x68, 0xf7, 0x07,
            0x51, 0x1a
        ]
    );
}
