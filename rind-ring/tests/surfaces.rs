//! Values cargo-mutants can replace without a round-trip noticing: lengths,
//! equality, `Debug`, and `Display`. Checked against ring, which rind-ring
//! offers. aws-lc-rs has changed some of those `Debug` strings.

use rind_ring as ours;
use ring as theirs;

#[test]
fn aead_algorithms_match_aws_lc() {
    let pairs = [
        (&ours::aead::AES_128_GCM, &theirs::aead::AES_128_GCM),
        (&ours::aead::AES_256_GCM, &theirs::aead::AES_256_GCM),
        (
            &ours::aead::CHACHA20_POLY1305,
            &theirs::aead::CHACHA20_POLY1305,
        ),
    ];
    for (ours_alg, theirs_alg) in pairs {
        assert_eq!(ours_alg.key_len(), theirs_alg.key_len());
        assert_eq!(ours_alg.tag_len(), theirs_alg.tag_len());
        assert_eq!(ours_alg.nonce_len(), theirs_alg.nonce_len());
        assert_eq!(format!("{ours_alg:?}"), format!("{theirs_alg:?}"));
        assert_eq!(ours_alg, ours_alg);
    }
    assert_ne!(ours::aead::AES_128_GCM, ours::aead::AES_256_GCM);
    assert_ne!(ours::aead::AES_128_GCM, ours::aead::CHACHA20_POLY1305);

    let nonce = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];
    assert_eq!(
        ours::aead::Nonce::assume_unique_for_key(nonce).as_ref(),
        &theirs::aead::Nonce::assume_unique_for_key(nonce).as_ref()[..]
    );
}

#[test]
fn quic_algorithms_match_aws_lc() {
    let pairs = [
        (&ours::aead::quic::AES_128, &theirs::aead::quic::AES_128),
        (&ours::aead::quic::AES_256, &theirs::aead::quic::AES_256),
        (&ours::aead::quic::CHACHA20, &theirs::aead::quic::CHACHA20),
    ];
    for (ours_alg, theirs_alg) in pairs {
        assert_eq!(ours_alg.key_len(), theirs_alg.key_len());
        assert_eq!(ours_alg.sample_len(), theirs_alg.sample_len());
        assert_eq!(format!("{ours_alg:?}"), format!("{theirs_alg:?}"));
        assert_eq!(ours_alg, ours_alg);
    }
    assert_ne!(ours::aead::quic::AES_128, ours::aead::quic::AES_256);
    assert_ne!(ours::aead::quic::AES_128, ours::aead::quic::CHACHA20);
}

#[test]
fn agreement_algorithms_and_public_keys_match_aws_lc() {
    let pairs = [
        (&ours::agreement::X25519, &theirs::agreement::X25519),
        (&ours::agreement::ECDH_P256, &theirs::agreement::ECDH_P256),
        (&ours::agreement::ECDH_P384, &theirs::agreement::ECDH_P384),
    ];
    let rng = ours::rand::SystemRandom::new();
    for (ours_alg, theirs_alg) in pairs {
        assert_eq!(format!("{ours_alg:?}"), format!("{theirs_alg:?}"));
        assert_eq!(ours_alg, ours_alg);

        let private = ours::agreement::EphemeralPrivateKey::generate(ours_alg, &rng).unwrap();
        let public = private.compute_public_key().unwrap();
        let bytes = public.as_ref();
        // `as_ref` replaced with an empty, zero, or one-filled buffer is none of these.
        assert!(bytes.len() > 1, "{ours_alg:?}");
        assert!(bytes.iter().any(|byte| *byte != 0), "{ours_alg:?}");
        assert!(bytes.iter().any(|byte| *byte != 1), "{ours_alg:?}");
        let rendered = format!("{public:?}");
        assert!(rendered.contains("PublicKey"), "{rendered}");
        assert!(rendered.contains(&format!("{ours_alg:?}")), "{rendered}");
    }
    assert_ne!(ours::agreement::X25519, ours::agreement::ECDH_P256);
    assert_ne!(ours::agreement::ECDH_P256, ours::agreement::ECDH_P384);
}

#[test]
fn digest_algorithms_match_aws_lc() {
    let pairs = [
        (
            &ours::digest::SHA1_FOR_LEGACY_USE_ONLY,
            &theirs::digest::SHA1_FOR_LEGACY_USE_ONLY,
        ),
        (&ours::digest::SHA256, &theirs::digest::SHA256),
        (&ours::digest::SHA384, &theirs::digest::SHA384),
        (&ours::digest::SHA512, &theirs::digest::SHA512),
        (&ours::digest::SHA512_256, &theirs::digest::SHA512_256),
    ];
    for (ours_alg, theirs_alg) in pairs {
        assert_eq!(ours_alg.block_len(), theirs_alg.block_len());
        assert_eq!(ours_alg.chaining_len(), theirs_alg.chaining_len());
        assert_eq!(ours_alg.output_len(), theirs_alg.output_len());
        assert_eq!(format!("{ours_alg:?}"), format!("{theirs_alg:?}"));
        assert_eq!(ours_alg, ours_alg);
    }
    assert_ne!(ours::digest::SHA256, ours::digest::SHA384);
    assert_ne!(ours::digest::SHA512, ours::digest::SHA512_256);
}

#[test]
fn hmac_and_pbkdf2_algorithms_match_aws_lc() {
    let hmac = [
        (
            ours::hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
            theirs::hmac::HMAC_SHA1_FOR_LEGACY_USE_ONLY,
        ),
        (ours::hmac::HMAC_SHA256, theirs::hmac::HMAC_SHA256),
        (ours::hmac::HMAC_SHA384, theirs::hmac::HMAC_SHA384),
        (ours::hmac::HMAC_SHA512, theirs::hmac::HMAC_SHA512),
    ];
    for (ours_alg, theirs_alg) in hmac {
        assert_eq!(
            ours_alg.digest_algorithm().output_len(),
            theirs_alg.digest_algorithm().output_len()
        );
        assert_eq!(format!("{ours_alg:?}"), format!("{theirs_alg:?}"));
        assert_eq!(ours_alg, ours_alg);
    }
    assert_ne!(ours::hmac::HMAC_SHA256, ours::hmac::HMAC_SHA384);

    let pbkdf2 = [
        (
            ours::pbkdf2::PBKDF2_HMAC_SHA1,
            theirs::pbkdf2::PBKDF2_HMAC_SHA1,
        ),
        (
            ours::pbkdf2::PBKDF2_HMAC_SHA256,
            theirs::pbkdf2::PBKDF2_HMAC_SHA256,
        ),
        (
            ours::pbkdf2::PBKDF2_HMAC_SHA384,
            theirs::pbkdf2::PBKDF2_HMAC_SHA384,
        ),
        (
            ours::pbkdf2::PBKDF2_HMAC_SHA512,
            theirs::pbkdf2::PBKDF2_HMAC_SHA512,
        ),
    ];
    for (ours_alg, _theirs_alg) in pbkdf2 {
        assert!(ours_alg == ours_alg);
    }
    assert!(ours::pbkdf2::PBKDF2_HMAC_SHA256 != ours::pbkdf2::PBKDF2_HMAC_SHA512);
}

#[test]
fn signature_algorithms_match_ring() {
    let verify = [
        (
            &ours::signature::ECDSA_P256_SHA256_ASN1,
            &theirs::signature::ECDSA_P256_SHA256_ASN1,
        ),
        (
            &ours::signature::ECDSA_P256_SHA256_FIXED,
            &theirs::signature::ECDSA_P256_SHA256_FIXED,
        ),
        (
            &ours::signature::ECDSA_P384_SHA384_ASN1,
            &theirs::signature::ECDSA_P384_SHA384_ASN1,
        ),
        (
            &ours::signature::ECDSA_P384_SHA384_FIXED,
            &theirs::signature::ECDSA_P384_SHA384_FIXED,
        ),
    ];
    for (ours_alg, theirs_alg) in verify {
        assert_eq!(format!("{ours_alg:?}"), format!("{theirs_alg:?}"));
    }

    let sign = [
        (
            &ours::signature::ECDSA_P256_SHA256_ASN1_SIGNING,
            &theirs::signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        ),
        (
            &ours::signature::ECDSA_P256_SHA256_FIXED_SIGNING,
            &theirs::signature::ECDSA_P256_SHA256_FIXED_SIGNING,
        ),
        (
            &ours::signature::ECDSA_P384_SHA384_ASN1_SIGNING,
            &theirs::signature::ECDSA_P384_SHA384_ASN1_SIGNING,
        ),
        (
            &ours::signature::ECDSA_P384_SHA384_FIXED_SIGNING,
            &theirs::signature::ECDSA_P384_SHA384_FIXED_SIGNING,
        ),
    ];
    for (ours_alg, theirs_alg) in sign {
        assert_eq!(format!("{ours_alg:?}"), format!("{theirs_alg:?}"));
        assert_eq!(ours_alg, ours_alg);
    }
    assert_ne!(
        ours::signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        ours::signature::ECDSA_P384_SHA384_ASN1_SIGNING
    );
    assert_ne!(
        ours::signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        ours::signature::ECDSA_P256_SHA256_FIXED_SIGNING
    );

    // ring derives a struct dump here. rind-ring prints the algorithm's name,
    // which is what a test can see; an empty `Debug` prints nothing.
    assert_eq!(
        format!("{:?}", ours::signature::RSA_PKCS1_2048_8192_SHA256),
        "RSA_PKCS1_2048_8192_SHA256"
    );
    assert_eq!(
        format!("{:?}", ours::signature::RSA_PSS_2048_8192_SHA256),
        "RSA_PSS_2048_8192_SHA256"
    );

    // Same as `RsaParameters`: rind-ring prints the name, ring a struct dump.
    assert_eq!(
        format!("{:?}", ours::signature::RSA_PKCS1_SHA256),
        "RSA_PKCS1_SHA256"
    );
    assert_eq!(
        format!("{:?}", ours::signature::RSA_PSS_SHA384),
        "RSA_PSS_SHA384"
    );
}

#[test]
fn unspecified_matches_aws_lc() {
    assert_eq!(
        ours::error::Unspecified.to_string(),
        theirs::error::Unspecified.to_string()
    );
}

#[test]
fn random_fills_the_value_it_returns() {
    // `as_mut_bytes` replaced with a leaked buffer leaves the array at zero.
    let rng = ours::rand::SystemRandom::new();
    let value: [u8; 32] = ours::rand::generate(&rng).unwrap().expose();
    assert_ne!(value, [0; 32]);
    assert_ne!(value, [1; 32]);
}
