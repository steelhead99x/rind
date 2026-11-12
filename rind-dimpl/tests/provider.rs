//! Calls the provider's components directly, for edges a handshake between
//! well-behaved peers never reaches.

use dimpl::crypto::{
    Aad, Buf, CryptoProvider, HashAlgorithm, NamedGroup, Nonce, SignatureAlgorithm, TmpBuf,
    aws_lc_rs,
};
use dimpl::{CryptoError, CryptoOperation};

fn rind() -> CryptoProvider {
    rind_dimpl::default_provider()
}

fn certificate(algorithm: &'static rcgen::SignatureAlgorithm) -> (Vec<u8>, Vec<u8>) {
    let key = rcgen::KeyPair::generate_for(algorithm).unwrap();
    let cert = rcgen::CertificateParams::new(Vec::<String>::new())
        .unwrap()
        .self_signed(&key)
        .unwrap();
    (cert.der().to_vec(), key.serialize_der())
}

#[test]
fn prefers_chacha20_without_aes_hardware() {
    // CI runs armv7 on a CPU model with the crypto extension and one without,
    // and aarch64 and x86_64 with AES hardware and with it denied, and names
    // which, so both orders are checked.
    let expected = match cfg!(target_arch = "x86_64") {
        true => std::env::var_os("RIND_TEST_X86_AES_HARDWARE"),
        false => std::env::var_os("RIND_TEST_ARM_CRYPTO_EXT"),
    };
    if let Some(expected) = expected {
        assert_eq!(rind::cpu::has_aes_hardware(), expected == "1");
    }

    use dimpl::crypto::{Dtls12CipherSuite as Dtls12, Dtls13CipherSuite as Dtls13};
    let mut dtls12 = vec![
        Dtls12::ECDHE_ECDSA_AES128_GCM_SHA256,
        Dtls12::ECDHE_ECDSA_AES256_GCM_SHA384,
        Dtls12::ECDHE_ECDSA_CHACHA20_POLY1305_SHA256,
    ];
    let mut dtls13 = vec![
        Dtls13::AES_128_GCM_SHA256,
        Dtls13::AES_256_GCM_SHA384,
        Dtls13::CHACHA20_POLY1305_SHA256,
    ];
    if !rind::cpu::has_aes_hardware() {
        dtls12.rotate_right(1);
        dtls13.rotate_right(1);
    }

    let provider = rind();
    assert_eq!(
        provider
            .cipher_suites
            .iter()
            .map(|s| s.suite())
            .collect::<Vec<_>>(),
        dtls12
    );
    assert_eq!(
        provider
            .dtls13_cipher_suites
            .iter()
            .map(|s| s.suite())
            .collect::<Vec<_>>(),
        dtls13
    );
}

#[test]
fn record_number_masks_match_aws_lc() {
    let aws_lc = aws_lc_rs::default_provider();
    for suite in rind().dtls13_cipher_suites {
        let reference = aws_lc
            .dtls13_cipher_suites
            .iter()
            .find(|s| s.suite() == suite.suite())
            .unwrap();
        let key: Vec<u8> = (0..suite.key_len() as u8).collect();
        // The all-ones sample puts ChaCha20's block counter at its maximum.
        for sample in [[0u8; 16], [0xff; 16], *b"0123456789abcdef"] {
            // aws-lc-rs fills only the five bytes QUIC uses for ChaCha20;
            // dimpl masks at most a two-byte sequence number.
            assert_eq!(
                suite.encrypt_sn(&key, &sample)[..5],
                reference.encrypt_sn(&key, &sample)[..5],
                "{:?} {sample:?}",
                suite.suite()
            );
        }
    }
}

#[test]
fn records_are_rejected_when_short_or_altered() {
    let provider = rind();
    for suite in provider.dtls13_cipher_suites {
        let label = format!("{:?}", suite.suite());
        let key = vec![7u8; suite.key_len()];
        let nonce = Nonce([1; 12]);
        let mut cipher = suite.create_cipher(&key).unwrap();

        let mut record = Buf::new();
        record.extend_from_slice(b"record");
        cipher
            .encrypt(&mut record, Aad(Default::default()), nonce)
            .unwrap();
        assert_eq!(record.len(), 6 + 16, "{label}");

        let mut opened = record.to_vec();
        let mut buf = TmpBuf::new(&mut opened);
        cipher
            .decrypt(&mut buf, Aad(Default::default()), nonce)
            .unwrap();
        assert_eq!(buf.as_ref(), b"record", "{label}");

        for i in [0, record.len() - 1] {
            let mut altered = record.to_vec();
            altered[i] ^= 1;
            let mut buf = TmpBuf::new(&mut altered);
            assert_eq!(
                cipher.decrypt(&mut buf, Aad(Default::default()), nonce),
                Err(CryptoError::OperationFailed(CryptoOperation::Decrypt)),
                "{label} byte {i}"
            );
        }

        let mut short = [0u8; 15];
        let mut buf = TmpBuf::new(&mut short);
        assert_eq!(
            cipher.decrypt(&mut buf, Aad(Default::default()), nonce),
            Err(CryptoError::CiphertextTooShort {
                minimum: 16,
                actual: 15
            }),
            "{label}"
        );
    }
}

#[test]
fn cipher_keys_of_the_wrong_length_are_refused() {
    let provider = rind();
    for suite in provider.dtls13_cipher_suites {
        // An AES-128 suite must not quietly run AES-256, nor the reverse.
        for len in [0, 15, 16, 24, 32, 33] {
            if len == suite.key_len() {
                continue;
            }
            assert!(
                suite.create_cipher(&vec![0; len]).is_err(),
                "{:?} accepted a {len}-byte key",
                suite.suite()
            );
        }
    }
}

#[test]
fn invalid_key_shares_are_refused() {
    let mut off_curve = vec![0x04];
    off_curve.extend_from_slice(&[0; 64]);
    let mut compressed = vec![0x02];
    compressed.extend_from_slice(&[0x11; 32]);

    let cases: [(NamedGroup, &[u8]); 6] = [
        // A low-order point makes the shared secret zero.
        (NamedGroup::X25519, &[0; 32]),
        (NamedGroup::X25519, &[9; 31]),
        (NamedGroup::Secp256r1, &off_curve),
        (NamedGroup::Secp256r1, &compressed),
        (NamedGroup::Secp384r1, &off_curve),
        (NamedGroup::Secp384r1, &[]),
    ];
    let provider = rind();
    for (group, peer) in cases {
        let kx = provider
            .kx_groups
            .iter()
            .find(|kx| kx.name() == group)
            .unwrap();
        let exchange = kx.start_exchange(Buf::new()).unwrap();
        assert_eq!(
            exchange.complete(peer, &mut Buf::new()),
            Err(CryptoError::InvalidPublicKey(group)),
            "{group:?} {peer:?}"
        );
    }
}

#[test]
fn signatures_are_checked_against_the_certificate() {
    let provider = rind();
    let (cert, key) = certificate(&rcgen::PKCS_ECDSA_P256_SHA256);
    let mut key = provider.key_provider.load_private_key(&key).unwrap();
    let mut signature = Buf::new();

    // A key signs only with the hash it was loaded for.
    assert_eq!(key.supported_hash_algorithms(), [HashAlgorithm::SHA256]);
    assert_eq!(
        key.sign(b"transcript", HashAlgorithm::SHA384, &mut signature),
        Err(CryptoError::SigningKeyHashMismatch {
            key_hash: HashAlgorithm::SHA256,
            requested: HashAlgorithm::SHA384,
        })
    );
    key.sign(b"transcript", HashAlgorithm::SHA256, &mut signature)
        .unwrap();

    let verify = |cert: &[u8], data: &[u8], signature: &[u8], hash, algorithm| {
        provider
            .signature_verification
            .verify_signature(cert, data, signature, hash, algorithm)
    };
    let ecdsa = SignatureAlgorithm::ECDSA;
    verify(
        &cert,
        b"transcript",
        &signature,
        HashAlgorithm::SHA256,
        ecdsa,
    )
    .unwrap();

    let failed = |hash| {
        Err(CryptoError::SignatureVerificationFailed {
            signature: ecdsa,
            hash,
            group: NamedGroup::Secp256r1,
        })
    };
    assert_eq!(
        verify(&cert, b"other", &signature, HashAlgorithm::SHA256, ecdsa),
        failed(HashAlgorithm::SHA256)
    );
    assert_eq!(
        verify(
            &cert,
            b"transcript",
            &signature,
            HashAlgorithm::SHA384,
            ecdsa
        ),
        failed(HashAlgorithm::SHA384)
    );
    let mut altered = signature.to_vec();
    *altered.last_mut().unwrap() ^= 1;
    assert_eq!(
        verify(&cert, b"transcript", &altered, HashAlgorithm::SHA256, ecdsa),
        failed(HashAlgorithm::SHA256)
    );

    assert_eq!(
        verify(
            &cert,
            b"transcript",
            &signature,
            HashAlgorithm::SHA512,
            ecdsa
        ),
        Err(CryptoError::UnsupportedSignatureVerification {
            signature: ecdsa,
            hash: HashAlgorithm::SHA512,
            group: NamedGroup::Secp256r1,
        })
    );
    assert_eq!(
        verify(
            &cert,
            b"transcript",
            &signature,
            HashAlgorithm::SHA256,
            SignatureAlgorithm::RSA
        ),
        Err(CryptoError::UnsupportedSignatureAlgorithm(
            SignatureAlgorithm::RSA
        ))
    );
    assert_eq!(
        verify(
            &cert[1..],
            b"transcript",
            &signature,
            HashAlgorithm::SHA256,
            ecdsa
        ),
        Err(CryptoError::CertificateParseFailed)
    );
    let (ed25519, _) = certificate(&rcgen::PKCS_ED25519);
    assert_eq!(
        verify(
            &ed25519,
            b"transcript",
            &signature,
            HashAlgorithm::SHA256,
            ecdsa
        ),
        Err(CryptoError::UnsupportedPublicKeyAlgorithm)
    );
}

#[test]
fn pem_pkcs8_loads_and_other_keys_are_refused() {
    let provider = rind();
    let (cert, p256) = certificate(&rcgen::PKCS_ECDSA_P256_SHA256);
    let pem = rcgen::KeyPair::try_from(p256.as_slice())
        .unwrap()
        .serialize_pem();
    let mut key = provider
        .key_provider
        .load_private_key(pem.as_bytes())
        .expect("PEM PKCS#8");
    let mut signature = Buf::new();
    key.sign(b"transcript", HashAlgorithm::SHA256, &mut signature)
        .unwrap();
    provider
        .signature_verification
        .verify_signature(
            &cert,
            b"transcript",
            &signature,
            HashAlgorithm::SHA256,
            SignatureAlgorithm::ECDSA,
        )
        .unwrap();

    let (cert384, p384) = certificate(&rcgen::PKCS_ECDSA_P384_SHA384);
    let pem384 = rcgen::KeyPair::try_from(p384.as_slice())
        .unwrap()
        .serialize_pem();
    let mut key = provider
        .key_provider
        .load_private_key(pem384.as_bytes())
        .expect("P-384 PEM PKCS#8");
    let mut signature = Buf::new();
    key.sign(b"transcript", HashAlgorithm::SHA384, &mut signature)
        .unwrap();
    provider
        .signature_verification
        .verify_signature(
            &cert384,
            b"transcript",
            &signature,
            HashAlgorithm::SHA384,
            SignatureAlgorithm::ECDSA,
        )
        .unwrap();

    let (_, ed25519) = certificate(&rcgen::PKCS_ED25519);
    let ed_pem = rcgen::KeyPair::try_from(ed25519.as_slice())
        .unwrap()
        .serialize_pem();

    for (key, what) in [
        (ed25519.as_slice(), "Ed25519"),
        (ed_pem.as_bytes(), "Ed25519 PEM"),
        (&p256[..p256.len() - 1], "truncated"),
        (b"".as_slice(), "empty"),
        (
            b"-----BEGIN PRIVATE KEY-----\n!!!!\n-----END PRIVATE KEY-----\n".as_slice(),
            "bad PEM",
        ),
    ] {
        assert_eq!(
            provider.key_provider.load_private_key(key).err(),
            Some(CryptoError::InvalidPrivateKey),
            "{what}"
        );
    }
}
