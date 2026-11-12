//! Each `OpenMlsCrypto` operation, compared with openmls_rust_crypto's: equal
//! outputs where they are deterministic, and each opening or verifying what
//! the other sealed or signed where they are not.

use openmls_traits::crypto::OpenMlsCrypto;
use openmls_traits::random::OpenMlsRand;
use openmls_traits::types::{
    AeadType, Ciphersuite, CryptoError, HashType, HpkeAeadType, HpkeConfig, HpkeKdfType,
    HpkeKemType, SignatureScheme,
};

const HASHES: [HashType; 3] = [HashType::Sha2_256, HashType::Sha2_384, HashType::Sha2_512];
const SCHEMES: [SignatureScheme; 3] = [
    SignatureScheme::ED25519,
    SignatureScheme::ECDSA_SECP256R1_SHA256,
    SignatureScheme::ECDSA_SECP384R1_SHA384,
];
const KEMS: [HpkeKemType; 3] = [
    HpkeKemType::DhKem25519,
    HpkeKemType::DhKemP256,
    HpkeKemType::DhKemP384,
];
const AEADS: [HpkeAeadType; 4] = [
    HpkeAeadType::AesGcm128,
    HpkeAeadType::AesGcm256,
    HpkeAeadType::ChaCha20Poly1305,
    HpkeAeadType::Export,
];

fn rind() -> rind_openmls::RustCrypto {
    rind_openmls::RustCrypto::default()
}

fn reference() -> openmls_rust_crypto::RustCrypto {
    openmls_rust_crypto::RustCrypto::default()
}

fn bytes(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i * 7 + 3) as u8).collect()
}

#[test]
fn hash_and_hmac() {
    for hash in HASHES {
        for len in [0, 1, 64, 127, 128, 129, 1000] {
            let data = bytes(len);
            assert_eq!(
                rind().hash(hash, &data).unwrap(),
                reference().hash(hash, &data).unwrap()
            );
            assert_eq!(
                rind().hmac(hash, &data, b"message").unwrap(),
                reference().hmac(hash, &data, b"message").unwrap()
            );
        }
    }
}

#[test]
fn hkdf() {
    for hash in HASHES {
        let prk = rind().hkdf_extract(hash, b"salt", b"ikm").unwrap();
        assert_eq!(
            prk,
            reference().hkdf_extract(hash, b"salt", b"ikm").unwrap()
        );
        assert_eq!(
            rind().hkdf_extract(hash, b"", b"").unwrap(),
            reference().hkdf_extract(hash, b"", b"").unwrap()
        );

        let size = hash.size();
        for len in [0, 1, size - 1, size, size + 1, 2 * size, 255 * size] {
            assert_eq!(
                rind()
                    .hkdf_expand(hash, prk.as_slice(), b"info", len)
                    .unwrap(),
                reference()
                    .hkdf_expand(hash, prk.as_slice(), b"info", len)
                    .unwrap(),
                "{hash:?} {len}",
            );
        }
        let long_prk = bytes(size + 5);
        assert_eq!(
            rind().hkdf_expand(hash, &long_prk, b"", 100).unwrap(),
            reference().hkdf_expand(hash, &long_prk, b"", 100).unwrap(),
        );

        // Both refuse a key shorter than the hash or an output too long.
        for (prk, len) in [(&prk.as_slice()[1..], 32), (prk.as_slice(), 255 * size + 1)] {
            assert_eq!(
                rind().hkdf_expand(hash, prk, b"info", len),
                Err(CryptoError::HkdfOutputLengthInvalid)
            );
            assert!(reference().hkdf_expand(hash, prk, b"info", len).is_err());
        }
    }
}

#[test]
fn aead() {
    for (alg, key_len) in [
        (AeadType::Aes128Gcm, 16),
        (AeadType::Aes256Gcm, 32),
        (AeadType::ChaCha20Poly1305, 32),
    ] {
        let key = bytes(key_len);
        let nonce = bytes(12);
        for len in [0, 1, 16, 100] {
            let data = bytes(len);
            let sealed = rind()
                .aead_encrypt(alg, &key, &data, &nonce, b"aad")
                .unwrap();
            assert_eq!(
                sealed,
                reference()
                    .aead_encrypt(alg, &key, &data, &nonce, b"aad")
                    .unwrap()
            );
            assert_eq!(
                rind()
                    .aead_decrypt(alg, &key, &sealed, &nonce, b"aad")
                    .unwrap(),
                data
            );

            let mut tampered = sealed.clone();
            tampered[0] ^= 1;
            assert_eq!(
                rind().aead_decrypt(alg, &key, &tampered, &nonce, b"aad"),
                Err(CryptoError::AeadDecryptionError)
            );
            assert_eq!(
                rind().aead_decrypt(alg, &key, &sealed, &nonce, b"other"),
                Err(CryptoError::AeadDecryptionError)
            );
        }

        // openmls_rust_crypto panics on a nonce of the wrong length.
        assert!(
            rind()
                .aead_encrypt(alg, &key, b"", &bytes(11), b"")
                .is_err()
        );
        assert!(
            rind()
                .aead_decrypt(alg, &key, &bytes(16), &bytes(13), b"")
                .is_err()
        );
        assert!(
            rind()
                .aead_encrypt(alg, &key[1..], b"", &nonce, b"")
                .is_err()
        );
        assert_eq!(
            rind().aead_decrypt(alg, &key, &bytes(15), &nonce, b""),
            Err(CryptoError::AeadDecryptionError)
        );
    }
}

#[test]
fn signatures() {
    for scheme in SCHEMES {
        let (rind_private, rind_public) = rind().signature_key_gen(scheme).unwrap();
        let (reference_private, reference_public) = reference().signature_key_gen(scheme).unwrap();
        assert_eq!(rind_private.len(), reference_private.len());
        assert_eq!(rind_public.len(), reference_public.len());

        let signature = rind().sign(scheme, b"data", &rind_private).unwrap();
        reference()
            .verify_signature(scheme, b"data", &rind_public, &signature)
            .unwrap();
        rind()
            .verify_signature(scheme, b"data", &rind_public, &signature)
            .unwrap();
        let signature = reference()
            .sign(scheme, b"data", &reference_private)
            .unwrap();
        rind()
            .verify_signature(scheme, b"data", &reference_public, &signature)
            .unwrap();
        // A key generated by one signs with the other.
        let signature = rind().sign(scheme, b"data", &reference_private).unwrap();
        reference()
            .verify_signature(scheme, b"data", &reference_public, &signature)
            .unwrap();

        assert_eq!(
            rind().verify_signature(scheme, b"other", &rind_public, &signature),
            Err(CryptoError::InvalidSignature)
        );
        assert_eq!(
            rind().verify_signature(scheme, b"data", &rind_public, &signature[1..]),
            Err(CryptoError::InvalidSignature)
        );
        assert_eq!(
            rind().verify_signature(scheme, b"data", &rind_public[1..], &signature),
            Err(CryptoError::CryptoLibraryError)
        );
        assert!(rind().sign(scheme, b"data", &rind_private[1..]).is_err());
        if scheme != SignatureScheme::ED25519 {
            // Above the group order.
            let out_of_range = vec![0xff; rind_private.len()];
            assert!(rind().sign(scheme, b"data", &out_of_range).is_err());

            // Both take the compressed point.
            let (x, y) = rind_public[1..].split_at(rind_private.len());
            let compressed = [&[2 | (y[y.len() - 1] & 1)], x].concat();
            let signature = rind().sign(scheme, b"data", &rind_private).unwrap();
            rind()
                .verify_signature(scheme, b"data", &compressed, &signature)
                .unwrap();
            reference()
                .verify_signature(scheme, b"data", &compressed, &signature)
                .unwrap();
        }
    }
    for scheme in [
        SignatureScheme::ED448,
        SignatureScheme::ECDSA_SECP521R1_SHA512,
    ] {
        assert_eq!(
            rind().signature_key_gen(scheme),
            Err(CryptoError::UnsupportedSignatureScheme)
        );
        assert_eq!(
            reference().signature_key_gen(scheme),
            Err(CryptoError::UnsupportedSignatureScheme)
        );
    }
}

#[test]
fn ed25519_small_order() {
    // The identity as the key, with R the identity and S zero, verifies any
    // message under cofactorless verification; both refuse it.
    let mut identity = [0u8; 32];
    identity[0] = 1;
    let signature = [&identity[..], &[0; 32]].concat();
    assert!(
        rind()
            .verify_signature(SignatureScheme::ED25519, b"data", &identity, &signature)
            .is_err()
    );
    assert!(
        reference()
            .verify_signature(SignatureScheme::ED25519, b"data", &identity, &signature)
            .is_err()
    );
}

#[test]
fn hpke() {
    for kem in KEMS {
        for kdf in [
            HpkeKdfType::HkdfSha256,
            HpkeKdfType::HkdfSha384,
            HpkeKdfType::HkdfSha512,
        ] {
            for aead in AEADS {
                let config = || HpkeConfig(kem, kdf, aead);
                let ikm = bytes(64);
                let key = rind().derive_hpke_keypair(config(), &ikm).unwrap();
                let reference_key = reference().derive_hpke_keypair(config(), &ikm).unwrap();
                assert_eq!(&*key.private, &*reference_key.private);
                assert_eq!(key.public, reference_key.public);

                let (enc, secret) = rind()
                    .hpke_setup_sender_and_export(config(), &key.public, b"info", b"context", 40)
                    .unwrap();
                let theirs = reference()
                    .hpke_setup_receiver_and_export(
                        config(),
                        &enc,
                        &key.private,
                        b"info",
                        b"context",
                        40,
                    )
                    .unwrap();
                assert_eq!(&*secret, &*theirs);
                let (enc, secret) = reference()
                    .hpke_setup_sender_and_export(config(), &key.public, b"info", b"context", 40)
                    .unwrap();
                let ours = rind()
                    .hpke_setup_receiver_and_export(
                        config(),
                        &enc,
                        &key.private,
                        b"info",
                        b"context",
                        40,
                    )
                    .unwrap();
                assert_eq!(&*secret, &*ours);

                if aead == HpkeAeadType::Export {
                    assert!(
                        rind()
                            .hpke_seal(config(), &key.public, b"", b"", b"")
                            .is_err()
                    );
                    continue;
                }
                let sealed = rind()
                    .hpke_seal(config(), &key.public, b"info", b"aad", b"plaintext")
                    .unwrap();
                assert_eq!(
                    reference()
                        .hpke_open(config(), &sealed, &key.private, b"info", b"aad")
                        .unwrap(),
                    b"plaintext"
                );
                let sealed = reference()
                    .hpke_seal(config(), &key.public, b"info", b"aad", b"plaintext")
                    .unwrap();
                assert_eq!(
                    rind()
                        .hpke_open(config(), &sealed, &key.private, b"info", b"aad")
                        .unwrap(),
                    b"plaintext"
                );
                assert_eq!(
                    rind().hpke_open(config(), &sealed, &key.private, b"other", b"aad"),
                    Err(CryptoError::HpkeDecryptionError)
                );
                assert_eq!(
                    rind().hpke_open(config(), &sealed, &key.private[1..], b"info", b"aad"),
                    Err(CryptoError::HpkeDecryptionError)
                );
                assert!(
                    rind()
                        .hpke_seal(config(), &key.public[1..], b"", b"", b"")
                        .is_err()
                );
            }
        }
    }
    for kem in [HpkeKemType::DhKem448, HpkeKemType::DhKemP521] {
        let config = || HpkeConfig(kem, HpkeKdfType::HkdfSha512, HpkeAeadType::AesGcm256);
        assert!(rind().derive_hpke_keypair(config(), &bytes(66)).is_err());
        assert!(
            reference()
                .derive_hpke_keypair(config(), &bytes(66))
                .is_err()
        );
    }
}

#[test]
fn hpke_export_length() {
    for (kdf, hash_len) in [
        (HpkeKdfType::HkdfSha256, 32),
        (HpkeKdfType::HkdfSha384, 48),
        (HpkeKdfType::HkdfSha512, 64),
    ] {
        let config = || HpkeConfig(HpkeKemType::DhKem25519, kdf, HpkeAeadType::Export);
        let key = rind().derive_hpke_keypair(config(), &bytes(32)).unwrap();
        // RFC 9180's longest export, 255 hash outputs, matches.
        let (enc, secret) = rind()
            .hpke_setup_sender_and_export(config(), &key.public, b"", b"", 255 * hash_len)
            .unwrap();
        let theirs = reference()
            .hpke_setup_receiver_and_export(config(), &enc, &key.private, b"", b"", 255 * hash_len)
            .unwrap();
        assert_eq!(&*secret, &*theirs);
        // A longer one, up to one that cannot be allocated, is refused first.
        for len in [255 * hash_len + 1, usize::MAX] {
            assert_eq!(
                rind()
                    .hpke_setup_sender_and_export(config(), &key.public, b"", b"", len)
                    .err(),
                Some(CryptoError::ExporterError)
            );
            assert_eq!(
                rind()
                    .hpke_setup_receiver_and_export(config(), &enc, &key.private, b"", b"", len)
                    .err(),
                Some(CryptoError::ExporterError)
            );
        }
    }
}

#[test]
fn ciphersuites() {
    for ciphersuite in [
        Ciphersuite::MLS_256_DHKEMX448_AES256GCM_SHA512_Ed448,
        Ciphersuite::MLS_256_DHKEMP521_AES256GCM_SHA512_P521,
        Ciphersuite::MLS_256_DHKEMX448_CHACHA20POLY1305_SHA512_Ed448,
        Ciphersuite::MLS_256_DHKEMP384_AES256GCM_SHA384_P384,
    ] {
        assert_eq!(
            rind().supports(ciphersuite),
            Err(CryptoError::UnsupportedCiphersuite)
        );
    }
    for ciphersuite in rind().supported_ciphersuites() {
        rind().supports(ciphersuite).unwrap();
    }
}

#[test]
fn random() {
    let a: [u8; 32] = rind().random_array().unwrap();
    let b: [u8; 32] = rind().random_array().unwrap();
    assert_ne!(a, b);
    assert_eq!(rind().random_vec(100).unwrap().len(), 100);
    assert!(rind().random_vec(0).unwrap().is_empty());
}

#[test]
fn rand_error_messages() {
    use openmls_rust_crypto::RandError as Reference;
    use rind_openmls::RandError;
    for (ours, theirs) in [
        (RandError::LockPoisoned, Reference::LockPoisoned),
        (
            RandError::NotEnoughRandomness,
            Reference::NotEnoughRandomness,
        ),
    ] {
        assert_eq!(ours.to_string(), theirs.to_string());
    }
}
