//! Every symmetric key and keyed state's `Debug` names its algorithm and
//! never shows its bytes, and neither does any other secret's.

/// Formats `value`, whose secret bytes are all 0xff, failing if they show.
fn show(value: &impl core::fmt::Debug) -> String {
    let shown = format!("{value:?}");
    assert!(!shown.contains("255") && !shown.contains("ff"), "{shown}");
    shown
}

#[test]
fn aead() {
    use rind::aead::{
        AES_128_GCM, AES_192_GCM, AES_256_GCM, CHACHA20_POLY1305, Key, Nonce, RandomizedNonceKey,
    };
    for (algorithm, name) in [
        (&AES_128_GCM, "Aes128Gcm"),
        (&AES_192_GCM, "Aes192Gcm"),
        (&AES_256_GCM, "Aes256Gcm"),
        (&CHACHA20_POLY1305, "ChaCha20Poly1305"),
    ] {
        assert_eq!(
            format!("{algorithm:?}"),
            format!("Algorithm {{ id: {name} }}")
        );
        let key = Key::new(algorithm, &[0xff; 32][..algorithm.key_len()]).unwrap();
        assert_eq!(show(&key), format!("Key {{ algorithm: {name}, .. }}"));
    }
    let nonce = Nonce::assume_unique_for_key([0xff; 12]);
    assert_eq!(show(&nonce), "Nonce(..)");
    let key = RandomizedNonceKey::new(&[0xff; 32]);
    assert_eq!(show(&key), "RandomizedNonceKey { .. }");

    use rind::aead::gcm::{self, Iv, TagLength};
    use rind::cipher;
    for (algorithm, len) in [(&cipher::AES_128, 16), (&cipher::AES_256, 32)] {
        let key = gcm::Key::new(algorithm, &[0xff; 32][..len], TagLength::Full).unwrap();
        let algorithm = format!("Algorithm {{ key_len: {len} }}");
        assert_eq!(show(&key), format!("Key {{ algorithm: {algorithm}, .. }}"));
    }
    let iv = Iv::assume_unique_for_key(&[0xff; 12]).unwrap();
    assert_eq!(show(&iv), "Iv(..)");
    let key = gcm::Key::new(&cipher::AES_128, &[0xff; 16], TagLength::Full).unwrap();
    let iv = Iv::assume_unique_for_key(&[0xff; 12]).unwrap();
    let tag = key.seal_in_place_separate_tag(iv, &[], &mut []).unwrap();
    assert_eq!(show(&tag), "Tag { len: 16, .. }");

    use rind::aead::quic::{AES_128, AES_256, CHACHA20, HeaderProtectionKey};
    for (algorithm, name) in [
        (&AES_128, "Aes128"),
        (&AES_256, "Aes256"),
        (&CHACHA20, "ChaCha20"),
    ] {
        assert_eq!(
            format!("{algorithm:?}"),
            format!("Algorithm {{ id: {name} }}")
        );
        let key = HeaderProtectionKey::new(algorithm, &[0xff; 32][..algorithm.key_len()]).unwrap();
        let expected = format!("HeaderProtectionKey {{ algorithm: {name}, .. }}");
        assert_eq!(show(&key), expected);
    }
}

#[test]
fn cipher() {
    use rind::cipher::{AES_128, AES_256, Aes, AesCtr, ChaCha20};
    use rind::key_wrap::{self, AesKek};
    for (algorithm, kek, len) in [
        (&AES_128, &key_wrap::AES_128, 16),
        (&AES_256, &key_wrap::AES_256, 32),
    ] {
        let key = &[0xff; 32][..len];
        let algorithm_shown = format!("Algorithm {{ key_len: {len} }}");
        let aes = Aes::new(algorithm, key).unwrap();
        assert_eq!(
            show(&aes),
            format!("Aes {{ algorithm: {algorithm_shown}, .. }}")
        );
        let ctr = AesCtr::new(algorithm, key, 128).unwrap();
        assert_eq!(
            show(&ctr),
            format!("AesCtr {{ algorithm: {algorithm_shown}, .. }}")
        );
        let kek = AesKek::new(kek, key).unwrap();
        assert_eq!(
            show(&kek),
            format!("AesKek {{ algorithm: {algorithm_shown}, .. }}")
        );
    }
    assert_eq!(show(&ChaCha20::new(&[0xff; 32])), "ChaCha20 { .. }");
}

#[test]
fn hmac() {
    use rind::{digest, hkdf, hmac, pbkdf2};
    let key = hmac::Key::new(&hmac::HMAC_SHA384, &[0xff; 32]);
    assert_eq!(show(&key), "Key { algorithm: Sha384, .. }");
    let mut ctx = hmac::Context::with_key(&key);
    ctx.update(&[0xff; 3]);
    assert_eq!(show(&ctx), "Context { algorithm: Sha384, .. }");
    assert_eq!(show(&ctx.sign()), "Tag { algorithm: Sha384, .. }");

    let mut ctx = digest::Context::new(&digest::SHA512_256);
    ctx.update(&[0xff; 3]);
    assert_eq!(show(&ctx), "Context { algorithm: Sha512_256, .. }");
    assert_eq!(
        format!("{:?}", digest::SHA256),
        "Algorithm { id: Sha256, output_len: 32 }"
    );
    let hash = digest::digest(&digest::SHA256, b"");
    let bytes = format!("{:?}", hash.as_ref());
    assert_eq!(
        format!("{hash:?}"),
        format!("Digest {{ algorithm: Sha256, value: {bytes} }}")
    );

    let salt = hkdf::Salt::new(&hkdf::HKDF_SHA256, &[0xff; 32]);
    assert_eq!(show(&salt), "Salt { algorithm: Sha256, .. }");
    let prk = salt.extract(&[0xff; 32]);
    assert_eq!(show(&prk), "Prk { algorithm: Sha256, .. }");
    assert_eq!(show(&prk.expand(&[], 16)), "Okm { algorithm: Sha256, .. }");

    let secret = pbkdf2::Secret::new(&pbkdf2::PBKDF2_HMAC_SHA512, &[0xff; 8]);
    assert_eq!(show(&secret), "Secret { algorithm: Sha512, .. }");
    assert_eq!(format!("{:?}", hmac::HMAC_SHA384), "Algorithm(Sha384)");
}

#[test]
fn kem() {
    use rind::kem::{DecapsulationKey, ML_KEM_768};
    assert_eq!(format!("{ML_KEM_768:?}"), "MlKem768");
    let key = DecapsulationKey::generate(&ML_KEM_768).unwrap();
    assert_eq!(format!("{key:?}"), "DecapsulationKey { .. }");
    let public = key.public_key();
    let shown = format!("{:?}", public.as_ref());
    assert_eq!(format!("{public:?}"), format!("EncapsulationKey({shown})"));
    let (_, secret) = public.encapsulate().unwrap();
    assert_eq!(format!("{secret:?}"), "SharedSecret(..)");
}

#[test]
fn rsa() {
    use rind::rsa::{DecryptingKey, OAEP_SHA256};
    assert_eq!(format!("{OAEP_SHA256:?}"), "OaepAlgorithm(Sha256)");
    let der = include_bytes!("../src/high/rsa/rsa2048.der");
    let key = DecryptingKey::from_pkcs1(&OAEP_SHA256, der).unwrap();
    assert_eq!(
        format!("{key:?}"),
        "DecryptingKey { algorithm: OaepAlgorithm(Sha256), .. }"
    );
    let public = key.public_key();
    let bytes = format!("{:?}", public.as_ref());
    assert_eq!(
        format!("{public:?}"),
        format!("EncryptingKey {{ algorithm: OaepAlgorithm(Sha256), bytes: {bytes} }}")
    );
    let ciphertext = public.encrypt(&[0xff; 4], b"").unwrap();
    let bytes = format!("{:?}", ciphertext.as_ref());
    assert_eq!(format!("{ciphertext:?}"), format!("Ciphertext({bytes})"));
    let plaintext = key.decrypt(ciphertext.as_ref(), b"").unwrap();
    assert_eq!(show(&plaintext), "Plaintext(..)");
}

#[test]
fn signature() {
    use rind::signature::{EcdsaKeyPair, Ed25519KeyPair, RsaKeyPair, sign, verify};
    let ecdsa = r#"Ecdsa { curve: P256, hash: Sha256, encoding: Asn1 }"#;
    assert_eq!(
        format!("{:?}", verify::ECDSA_P256_SHA256_ASN1),
        format!("Ecdsa({ecdsa})")
    );
    assert_eq!(format!("{:?}", verify::ED25519), "Ed25519");
    let rsa =
        "Rsa { verification: Scheme(RsaScheme { padding: Pkcs1, hash: Sha256 }), min_bits: 2048 }";
    assert_eq!(format!("{:?}", verify::RSA_PKCS1_SHA256), rsa);
    assert_eq!(
        format!("{:?}", verify::RSA_PKCS1_SHA256.as_ref()),
        format!("Rsa({rsa})")
    );

    let algorithm = &sign::ECDSA_P256_SHA256_ASN1;
    assert_eq!(
        format!("{algorithm:?}"),
        format!("EcdsaSigningAlgorithm({ecdsa})")
    );
    let pair = EcdsaKeyPair::generate(algorithm).unwrap();
    let public = pair.public_key();
    let point = format!("{:?}", public.as_ref());
    assert_eq!(
        format!("{pair:?}"),
        format!("EcdsaKeyPair {{ algorithm: {ecdsa}, public_key: {point}, .. }}")
    );
    assert_eq!(
        format!("{public:?}"),
        format!("PublicKey {{ algorithm: {ecdsa}, bytes: {point} }}")
    );
    let signature = pair.sign(b"").unwrap();
    let bytes = format!("{:?}", signature.as_ref());
    assert_eq!(format!("{signature:?}"), format!("Signature({bytes})"));
    let spki = pair.to_spki();
    let bytes = format!("{:?}", spki.as_ref());
    assert_eq!(format!("{spki:?}"), format!("Spki({bytes})"));
    assert_eq!(format!("{:?}", pair.to_pkcs8()), "Pkcs8(..)");
    assert_eq!(format!("{:?}", pair.to_sec1()), "Sec1(..)");
    assert_eq!(format!("{:?}", pair.to_scalar()), "EcdsaScalar(..)");

    let pss = "RsaScheme { padding: Pss(Hash), hash: Sha256 }";
    assert_eq!(
        format!("{:?}", sign::RSA_PSS_SHA256),
        format!("RsaSigningAlgorithm({pss})")
    );
    let pair = RsaKeyPair::from_pkcs8(include_bytes!("../src/high/rsa/rsa2048.pkcs8.der")).unwrap();
    let public = pair.public_key(&sign::RSA_PSS_SHA256);
    let bytes = format!("{:?}", public.as_ref());
    assert_eq!(
        format!("{pair:?}"),
        format!("RsaKeyPair {{ public_key: {bytes}, .. }}")
    );
    assert_eq!(
        format!("{public:?}"),
        format!("PublicKey {{ algorithm: Scheme({pss}), bytes: {bytes} }}")
    );

    let pair = Ed25519KeyPair::generate().unwrap();
    let bytes = format!("{:?}", pair.public_key().as_ref());
    assert_eq!(
        format!("{pair:?}"),
        format!("Ed25519KeyPair {{ public_key: {bytes}, .. }}")
    );
    assert_eq!(format!("{:?}", pair.to_seed()), "Ed25519Seed(..)");

    use rind::signature::sign::{MlDsa65, MlDsaKeyPair};
    assert_eq!(format!("{:?}", verify::ML_DSA_65), "ML-DSA-65");
    let pair = MlDsaKeyPair::<MlDsa65>::generate().unwrap();
    assert_eq!(
        format!("{pair:?}"),
        "MlDsaKeyPair { algorithm: ML-DSA-65, .. }"
    );
    let public = pair.public_key();
    let bytes = format!("{:?}", public.as_ref());
    assert_eq!(
        format!("{public:?}"),
        format!("PublicKey {{ algorithm: ML-DSA-65, bytes: {bytes} }}")
    );
    let signature = pair.sign(b"").unwrap();
    let bytes = format!("{:?}", signature.as_ref());
    assert_eq!(format!("{signature:?}"), format!("MlDsaSignature({bytes})"));
    assert_eq!(format!("{:?}", pair.to_seed().unwrap()), "MlDsaSeed(..)");
    assert_eq!(format!("{:?}", pair.to_pkcs8()), "Pkcs8(..)");
}

#[test]
fn vrf() {
    use rind::vrf::{ECVRF_EDWARDS25519_SHA512_TAI, ECVRF_P256_SHA256_TAI, SecretKey};

    let edwards = SecretKey::from_bytes(&ECVRF_EDWARDS25519_SHA512_TAI, &[0xff; 32]).unwrap();
    let shown = format!("{edwards:?}");
    assert_eq!(
        shown,
        "SecretKey { algorithm: ECVRF-EDWARDS25519-SHA512-TAI, .. }"
    );
    assert!(!shown.contains("255, 255"), "{shown}");

    let seed = [
        0xff, 0xff, 0xff, 0xff, 0x00, 0x00, 0x00, 0x00, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff,
        0xff, 0xbc, 0xe6, 0xfa, 0xad, 0xa7, 0x17, 0x9e, 0x84, 0xf3, 0xb9, 0xca, 0xc2, 0xfc, 0x63,
        0x25, 0x50,
    ];
    // One below the P-256 order, so it is a key, and it is full of 0xff bytes.
    let p256 = SecretKey::from_bytes(&ECVRF_P256_SHA256_TAI, &seed).unwrap();
    let shown = format!("{p256:?}");
    assert_eq!(shown, "SecretKey { algorithm: ECVRF-P256-SHA256-TAI, .. }");
    assert!(!shown.contains("255, 255"), "{shown}");
}

#[test]
fn agreement() {
    use rind::agreement::{ECDH_P256, PrivateKey};
    assert_eq!(format!("{ECDH_P256:?}"), "EcdhP256");
    let key = PrivateKey::generate(&ECDH_P256).unwrap();
    assert_eq!(format!("{key:?}"), "PrivateKey { algorithm: EcdhP256, .. }");
    assert_eq!(format!("{:?}", key.to_scalar()), "Scalar(..)");
    let public = key.public_key();
    let bytes = format!("{:?}", public.as_ref());
    assert_eq!(format!("{public:?}"), format!("PublicKey({bytes})"));
    let secret = key.agree(public.as_ref()).unwrap();
    assert_eq!(format!("{secret:?}"), "SharedSecret(..)");
}
