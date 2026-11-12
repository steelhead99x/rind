//! Lengths, limits, and `Debug` that cargo-mutants can replace without a
//! handshake noticing, checked against rustls's aws-lc-rs provider.

use rustls::crypto::aws_lc_rs;
use rustls::crypto::cipher::{AeadKey, InboundOpaqueMessage, OutboundPlainMessage};
use rustls::pki_types::{PrivateKeyDer, PrivatePkcs1KeyDer, PrivatePkcs8KeyDer, PrivateSec1KeyDer};
use rustls::{CipherSuite, ContentType, ProtocolVersion, SupportedCipherSuite};

fn confidentiality_limit(suite: SupportedCipherSuite) -> u64 {
    match suite {
        SupportedCipherSuite::Tls12(suite) => suite.common.confidentiality_limit,
        SupportedCipherSuite::Tls13(suite) => suite.common.confidentiality_limit,
    }
}

fn tls12(suite: SupportedCipherSuite) -> &'static rustls::Tls12CipherSuite {
    match suite {
        SupportedCipherSuite::Tls12(suite) => suite,
        SupportedCipherSuite::Tls13(_) => panic!("not a TLS 1.2 suite"),
    }
}

#[test]
fn random_fill_replaces_the_buffer() {
    let mut buf = [0x5a; 32];
    rind_rustls::default_provider()
        .secure_random
        .fill(&mut buf)
        .unwrap();
    assert_ne!(buf, [0x5a; 32]);
}

#[test]
fn hpke_debug_names_the_suite() {
    for (ours, theirs) in rind_rustls::hpke::ALL_SUPPORTED_SUITES
        .iter()
        .zip(aws_lc_rs::hpke::ALL_SUPPORTED_SUITES)
    {
        let rendered = format!("{ours:?}");
        assert_eq!(rendered, format!("{theirs:?}"));
        assert!(!rendered.is_empty(), "{rendered}");
    }
}

fn find(suites: &[SupportedCipherSuite], id: CipherSuite) -> SupportedCipherSuite {
    *suites.iter().find(|suite| suite.suite() == id).unwrap()
}

#[test]
fn cipher_suite_limits_match_aws_lc() {
    let aws = aws_lc_rs::ALL_CIPHER_SUITES;
    for suite in rind_rustls::ALL_CIPHER_SUITES {
        let reference = find(aws, suite.suite());
        assert_eq!(
            confidentiality_limit(*suite),
            confidentiality_limit(reference),
            "{}",
            suite.suite().as_str().unwrap_or("?")
        );
    }
}

/// rustls's public `AeadKey` constructor takes 32 bytes, which is AES-256 and
/// ChaCha20. AES-128 uses the same TLS 1.2 encrypter type as AES-256.
fn aead_key() -> AeadKey {
    AeadKey::from([7u8; 32])
}

fn tls12_suites() -> [(SupportedCipherSuite, SupportedCipherSuite); 6] {
    [
        (
            rind_rustls::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
            aws_lc_rs::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_128_GCM_SHA256,
        ),
        (
            rind_rustls::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
            aws_lc_rs::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384,
        ),
        (
            rind_rustls::cipher_suite::TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
            aws_lc_rs::cipher_suite::TLS_ECDHE_ECDSA_WITH_CHACHA20_POLY1305_SHA256,
        ),
        (
            rind_rustls::cipher_suite::TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
            aws_lc_rs::cipher_suite::TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256,
        ),
        (
            rind_rustls::cipher_suite::TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
            aws_lc_rs::cipher_suite::TLS_ECDHE_RSA_WITH_AES_256_GCM_SHA384,
        ),
        (
            rind_rustls::cipher_suite::TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256,
            aws_lc_rs::cipher_suite::TLS_ECDHE_RSA_WITH_CHACHA20_POLY1305_SHA256,
        ),
    ]
}

#[test]
fn tls12_encrypted_payload_len_matches_aws_lc() {
    for (ours, theirs) in tls12_suites() {
        let ours = tls12(ours).aead_alg;
        let theirs = tls12(theirs).aead_alg;
        let shape = ours.key_block_shape();
        let theirs_shape = theirs.key_block_shape();
        assert_eq!(shape.enc_key_len, theirs_shape.enc_key_len);
        assert_eq!(shape.fixed_iv_len, theirs_shape.fixed_iv_len);
        assert_eq!(shape.explicit_nonce_len, theirs_shape.explicit_nonce_len);
        if shape.enc_key_len != 32 {
            continue;
        }
        let ours_enc = ours.encrypter(
            aead_key(),
            &vec![1u8; shape.fixed_iv_len],
            &vec![2u8; shape.explicit_nonce_len],
        );
        let theirs_enc = theirs.encrypter(
            aead_key(),
            &vec![1u8; shape.fixed_iv_len],
            &vec![2u8; shape.explicit_nonce_len],
        );
        for len in [0, 1, 2, 17, 64] {
            assert_eq!(
                ours_enc.encrypted_payload_len(len),
                theirs_enc.encrypted_payload_len(len),
                "{len}"
            );
        }
    }
}

#[test]
fn gcm_tls12_accepts_an_empty_plaintext_and_refuses_a_short_record() {
    // `payload.len() < overhead` becomes `<=` if an empty plaintext, whose
    // ciphertext is exactly the overhead, is refused, and `==` if a shorter
    // record is decrypted instead of refused.
    let suite = tls12(rind_rustls::cipher_suite::TLS_ECDHE_ECDSA_WITH_AES_256_GCM_SHA384);
    let shape = suite.aead_alg.key_block_shape();
    let iv = vec![1u8; shape.fixed_iv_len];
    let explicit = vec![2u8; shape.explicit_nonce_len];
    let mut enc = suite.aead_alg.encrypter(aead_key(), &iv, &explicit);
    let mut dec = suite.aead_alg.decrypter(aead_key(), &iv);

    let plain = OutboundPlainMessage {
        typ: ContentType::ApplicationData,
        version: ProtocolVersion::TLSv1_2,
        payload: (&[][..]).into(),
    };
    let sealed = enc.encrypt(plain, 1).unwrap();
    let mut payload = sealed.payload.as_ref().to_vec();
    let opened = dec
        .decrypt(
            InboundOpaqueMessage::new(sealed.typ, sealed.version, &mut payload),
            1,
        )
        .unwrap();
    assert!(opened.payload.is_empty());

    let mut short = vec![0u8; 8];
    let error = dec
        .decrypt(
            InboundOpaqueMessage::new(
                ContentType::ApplicationData,
                ProtocolVersion::TLSv1_2,
                &mut short,
            ),
            1,
        )
        .unwrap_err();
    assert!(matches!(error, rustls::Error::DecryptError), "{error:?}");
}

#[test]
fn quic_limits_match_aws_lc() {
    use rustls::crypto::cipher::Iv;

    let pairs = [
        (
            rind_rustls::cipher_suite::TLS13_AES_128_GCM_SHA256,
            aws_lc_rs::cipher_suite::TLS13_AES_128_GCM_SHA256,
        ),
        (
            rind_rustls::cipher_suite::TLS13_AES_256_GCM_SHA384,
            aws_lc_rs::cipher_suite::TLS13_AES_256_GCM_SHA384,
        ),
        (
            rind_rustls::cipher_suite::TLS13_CHACHA20_POLY1305_SHA256,
            aws_lc_rs::cipher_suite::TLS13_CHACHA20_POLY1305_SHA256,
        ),
    ];
    for (ours, theirs) in pairs {
        let ours = ours.tls13().unwrap().quic.unwrap();
        let theirs = theirs.tls13().unwrap().quic.unwrap();
        assert_eq!(ours.aead_key_len(), theirs.aead_key_len());
        // A 16-byte key cannot be built from rustls's public `AeadKey`.
        if ours.aead_key_len() != 32 {
            continue;
        }
        let ours_key = ours.packet_key(aead_key(), Iv::new([3u8; 12]));
        let theirs_key = theirs.packet_key(aead_key(), Iv::new([3u8; 12]));
        assert_eq!(ours_key.tag_len(), theirs_key.tag_len());
        assert_eq!(
            ours_key.confidentiality_limit(),
            theirs_key.confidentiality_limit()
        );
        assert_eq!(ours_key.integrity_limit(), theirs_key.integrity_limit());
    }
}

#[test]
fn hybrid_groups_match_aws_lc_versions() {
    let pairs = [
        (
            rind_rustls::kx_group::X25519MLKEM768,
            aws_lc_rs::kx_group::X25519MLKEM768,
        ),
        (
            rind_rustls::kx_group::SECP256R1MLKEM768,
            aws_lc_rs::kx_group::SECP256R1MLKEM768,
        ),
    ];
    for version in [ProtocolVersion::TLSv1_2, ProtocolVersion::TLSv1_3] {
        for (ours, theirs) in pairs {
            assert_eq!(
                ours.usable_for_version(version),
                theirs.usable_for_version(version),
                "{version:?}"
            );
        }
    }
}

#[test]
fn signing_key_debug_matches_aws_lc() {
    let ecdsa =
        rind::signature::EcdsaKeyPair::generate(&rind::signature::sign::ECDSA_P256_SHA256_ASN1)
            .unwrap();
    let pkcs8 = ecdsa.to_pkcs8();
    let der = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(pkcs8.as_ref().to_vec()));
    let ours = rind_rustls::sign::any_ecdsa_type(&der).unwrap();
    let theirs = aws_lc_rs::sign::any_ecdsa_type(&der).unwrap();
    let scheme = rustls::SignatureScheme::ECDSA_NISTP256_SHA256;
    // rustls's aws-lc-rs provider names the key `EcdsaSigningKey` and omits the
    // scheme. rind names the scheme. An empty `Debug` has neither.
    let rendered = format!("{ours:?}");
    assert!(rendered.contains("ECDSA_NISTP256_SHA256"), "{rendered}");
    let signer = format!("{:?}", ours.choose_scheme(&[scheme]).unwrap());
    assert!(signer.contains("Ecdsa"), "{signer}");
    assert_eq!(
        ours.choose_scheme(&[scheme]).unwrap().scheme(),
        theirs.choose_scheme(&[scheme]).unwrap().scheme()
    );

    let rsa = rind::signature::RsaKeyPair::generate(rind::rsa::KeySize::Rsa2048).unwrap();
    let pkcs8 = rsa.to_pkcs8();
    let der = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(pkcs8.as_ref().to_vec()));
    let ours = rind_rustls::sign::any_supported_type(&der).unwrap();
    let theirs = aws_lc_rs::sign::any_supported_type(&der).unwrap();
    let scheme = rustls::SignatureScheme::RSA_PKCS1_SHA256;
    let rendered = format!("{ours:?}");
    assert!(rendered.contains("RsaSigningKey"), "{rendered}");
    let signer = format!("{:?}", ours.choose_scheme(&[scheme]).unwrap());
    assert!(signer.contains("RsaSigner"), "{signer}");
    assert_eq!(
        ours.choose_scheme(&[scheme]).unwrap().scheme(),
        theirs.choose_scheme(&[scheme]).unwrap().scheme()
    );
}

#[test]
fn unsupported_encodings_name_the_encoding() {
    // Deleting a match arm in `unsupported` calls every encoding "private".
    let cases: [(&str, PrivateKeyDer<'_>); 3] = [
        (
            "PKCS#1",
            PrivateKeyDer::Pkcs1(PrivatePkcs1KeyDer::from(vec![0x30, 0x00])),
        ),
        (
            "SEC1",
            PrivateKeyDer::Sec1(PrivateSec1KeyDer::from(vec![0x30, 0x00])),
        ),
        (
            "PKCS#8",
            PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(vec![0x30, 0x00])),
        ),
    ];
    for (encoding, der) in cases {
        let error = rind_rustls::sign::any_supported_type(&der).unwrap_err();
        let rendered = error.to_string();
        assert!(
            rendered.contains(&format!("unsupported {encoding} key")),
            "{rendered}"
        );
    }
}
