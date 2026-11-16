//! aws-lc's and BoringSSL's vector files for rind's algorithms, from
//! `thirdparty/vectors`, which `admin/sync-vectors` copies. Files that need
//! crate access run in `src/`: ECDSA, whose files give digests and nonces,
//! Poly1305, Miller-Rabin, and ML-KEM.

use rind::Error;
use rind::aead::{
    AES_128_GCM, AES_192_GCM, AES_256_GCM, Algorithm, CHACHA20_POLY1305, Key, Nonce, RandomNonce,
    RandomizedNonceKey, Tag, gcm,
};
use rind::agreement::{self, ECDH_P256, ECDH_P384, ECDH_P521};
use rind::cipher::{
    AES_128, AES_192, AES_256, Aes, AesCbcDecryptingKey, AesCbcEncryptingKey, AesCtr, CbcIv,
};
use rind::hmac;
use rind::key_wrap::{AesKek, Mode};
use rind::{ecdsa, ed25519, rsa};

#[path = "../src/test/file_test.rs"]
mod file_test;

use file_test::{Test, tests};

fn aes_algorithm(key: &[u8]) -> &'static rind::cipher::Algorithm {
    match key.len() {
        16 => &AES_128,
        24 => &AES_192,
        32 => &AES_256,
        len => panic!("unexpected AES key length {len}"),
    }
}

fn gcm_tag_length(len: usize) -> Option<gcm::TagLength> {
    Some(match len {
        16 => gcm::TagLength::Full,
        15 => gcm::TagLength::Truncated120,
        14 => gcm::TagLength::Truncated112,
        13 => gcm::TagLength::Truncated104,
        12 => gcm::TagLength::Truncated96,
        8 => gcm::TagLength::Truncated64,
        4 => gcm::TagLength::Truncated32,
        _ => return None,
    })
}

/// Checks AES-GCM through `gcm::Key`, which takes any IV and the tag lengths
/// SP 800-38D allows, and through `aead::Key` for 96-bit IVs and full tags.
/// aws-lc's EVP interface takes tags of any length, which rind refuses.
#[allow(clippy::too_many_arguments)]
fn check_aes_gcm(
    test: &Test,
    key: &[u8],
    iv: &[u8],
    aad: &[u8],
    pt: &[u8],
    ct: &[u8],
    tag: &[u8],
    valid: bool,
) {
    let Some(tag_length) = gcm_tag_length(tag.len()) else {
        assert!(
            gcm::Key::new(aes_algorithm(key), key, gcm::TagLength::Full).is_ok(),
            "{test}"
        );
        return;
    };

    let ctx = gcm::Key::new(aes_algorithm(key), key, tag_length).unwrap();
    let iv_ = || gcm::Iv::assume_unique_for_key(iv).unwrap();
    let mut got = ct.to_vec();
    let opened = ctx
        .open_in_place_separate_tag(iv_(), aad, tag, &mut got)
        .map(|pt| pt.to_vec());
    match valid {
        true => assert_eq!(opened.as_deref(), Ok(pt), "{test}"),
        false => assert_eq!(opened, Err(Error::DecryptFailed), "{test}"),
    }
    if valid {
        let mut got = pt.to_vec();
        let sealed = ctx
            .seal_in_place_separate_tag(iv_(), aad, &mut got)
            .unwrap();
        assert_eq!((&got[..], sealed.as_ref()), (ct, tag), "{test}");
    }

    let (Ok(nonce), 16) = (<[u8; 12]>::try_from(iv), tag.len()) else {
        return;
    };
    let algorithm: &Algorithm = match key.len() {
        16 => &AES_128_GCM,
        24 => &AES_192_GCM,
        _ => &AES_256_GCM,
    };
    check_aead(test, algorithm, key, nonce, aad, pt, ct, tag, valid);
}

/// Checks an `aead::Key` opens `ct` and `tag` to `pt`, and seals it back, or
/// for an invalid test refuses it.
#[allow(clippy::too_many_arguments)]
fn check_aead(
    test: &Test,
    algorithm: &'static Algorithm,
    key: &[u8],
    nonce: [u8; 12],
    aad: &[u8],
    pt: &[u8],
    ct: &[u8],
    tag: &[u8],
    valid: bool,
) {
    // aws-lc truncates tags on request, which rind refuses.
    if tag.len() != 16 {
        assert_eq!(Tag::try_from(tag).err(), Some(Error::WrongLength), "{test}");
        return;
    }
    let ctx = Key::new(algorithm, key).unwrap();
    let nonce = || Nonce::assume_unique_for_key(nonce);
    let mut got = ct.to_vec();
    let opened = Tag::try_from(tag).and_then(|tag| {
        ctx.open_in_place_separate_tag(nonce(), aad, tag, &mut got)
            .map(|pt| pt.to_vec())
    });
    match valid {
        true => assert_eq!(opened.as_deref(), Ok(pt), "{test}"),
        false => assert!(
            matches!(opened, Err(Error::DecryptFailed | Error::WrongLength)),
            "{test}: {opened:?}"
        ),
    }
    if valid {
        let mut got = pt.to_vec();
        let sealed = ctx
            .seal_in_place_separate_tag(nonce(), aad, &mut got)
            .unwrap();
        assert_eq!((&got[..], sealed.as_ref()), (ct, tag), "{test}");
    }
}

// AES-GCM, ChaCha20-Poly1305, and XChaCha20-Poly1305 through aws-lc's AEAD
// interface.
#[test]
fn aead() {
    for (file, algorithm) in [
        ("aes_128_gcm_tests.txt", &AES_128_GCM),
        ("aes_192_gcm_tests.txt", &AES_192_GCM),
        ("aes_256_gcm_tests.txt", &AES_256_GCM),
        ("chacha20_poly1305_tests.txt", &CHACHA20_POLY1305),
        ("xchacha20_poly1305_tests.txt", &CHACHA20_POLY1305),
    ] {
        for test in tests(&format!("aws-lc/crypto/cipher_extra/test/{file}")) {
            let (key, nonce, aad) = (test.bytes("KEY"), test.bytes("NONCE"), test.bytes("AD"));
            let (pt, ct, tag) = (test.bytes("IN"), test.bytes("CT"), test.bytes("TAG"));
            // Every test is valid: aws-lc checks that each fails once altered.
            if file.starts_with("aes") {
                check_aes_gcm(&test, &key, &nonce, &aad, &pt, &ct, &tag, true);
                let mut bad = tag.clone();
                bad[0] ^= 1;
                check_aes_gcm(&test, &key, &nonce, &aad, &pt, &ct, &bad, false);
            } else if file.starts_with("xchacha") {
                // rind takes only full tags.
                if tag.len() != 16 {
                    continue;
                }
                let ctx = RandomizedNonceKey::new(&key.try_into().unwrap());
                let nonce: [u8; 24] = nonce.try_into().unwrap();
                let mut sealed = [&ct[..], &tag[..]].concat();
                let opened = ctx.open_in_place(RandomNonce::from(nonce), &aad, &mut sealed);
                assert_eq!(opened.as_deref(), Ok(&pt[..]), "{test}");
                let mut sealed = [&ct[..], &tag[..]].concat();
                *sealed.last_mut().unwrap() ^= 1;
                let opened = ctx.open_in_place(RandomNonce::from(nonce), &aad, &mut sealed);
                assert_eq!(opened, Err(Error::DecryptFailed), "{test}");
            } else {
                let nonce: [u8; 12] = nonce.try_into().unwrap();
                check_aead(&test, algorithm, &key, nonce, &aad, &pt, &ct, &tag, true);
                let mut bad = tag.clone();
                bad[0] ^= 1;
                check_aead(&test, algorithm, &key, nonce, &aad, &pt, &ct, &bad, false);
            }
        }
    }
}

// The EVP cipher tests for the AES modes rind has; DES, RC4, and OFB it
// doesn't.
#[test]
fn cipher() {
    for test in tests("aws-lc/crypto/cipher_extra/test/cipher_tests.txt") {
        let cipher = test.str("Cipher");
        let (key, pt, ct) = (
            test.bytes("Key"),
            test.bytes("Plaintext"),
            test.bytes("Ciphertext"),
        );
        let algorithm = || aes_algorithm(&key);
        let iv = || -> [u8; 16] { test.bytes("IV").try_into().unwrap() };
        let invalid = test.get("Operation") == Some("InvalidDecrypt");
        let Some(mode) = cipher.strip_prefix("AES-") else {
            continue;
        };
        match mode {
            m if m.ends_with("-ECB") => {
                let aes = Aes::new(algorithm(), &key).unwrap();
                for (p, c) in pt.chunks(16).zip(ct.chunks(16)) {
                    let mut block: [u8; 16] = p.try_into().unwrap();
                    aes.encrypt_block(&mut block);
                    assert_eq!(block, c, "{test}");
                }
            }
            m if m.ends_with("-CBC") => {
                let mut got = pt.clone();
                let enc = AesCbcEncryptingKey::new(algorithm(), &key).unwrap();
                enc.encrypt_blocks(CbcIv::assume_unpredictable(iv()), &mut got)
                    .unwrap();
                assert_eq!(got, ct, "{test}");
                let dec = AesCbcDecryptingKey::new(algorithm(), &key).unwrap();
                dec.decrypt_blocks(&iv(), &mut got).unwrap();
                assert_eq!(got, pt, "{test}");
            }
            m if m.ends_with("-CTR") => {
                let ctr = AesCtr::new(algorithm(), &key, 128).unwrap();
                let mut got = pt.clone();
                ctr.apply_keystream(&iv(), &mut got).unwrap();
                assert_eq!(got, ct, "{test}");
            }
            m if m.ends_with("-GCM") => {
                let (aad, tag) = (test.bytes("AAD"), test.bytes("Tag"));
                let iv = test.bytes("IV");
                check_aes_gcm(&test, &key, &iv, &aad, &pt, &ct, &tag, !invalid);
            }
            m if m.ends_with("-OFB") => {}
            _ => panic!("{test}: unexpected cipher {cipher}"),
        }
    }
}

// The AES block, AES-KW, and AES-KWP.
#[test]
fn aes() {
    for test in tests("aws-lc/crypto/fipsmodule/aes/aes_tests.txt") {
        let (key, pt, ct) = (
            test.bytes("Key"),
            test.bytes("Plaintext"),
            test.bytes("Ciphertext"),
        );
        let algorithm = aes_algorithm(&key);
        match test.str("Mode") {
            "Raw" => {
                let mut block: [u8; 16] = pt.clone().try_into().unwrap();
                Aes::new(algorithm, &key).unwrap().encrypt_block(&mut block);
                assert_eq!(block, &ct[..], "{test}");
            }
            name @ ("KeyWrap" | "KeyWrapWithPadding") => {
                let mode = match name {
                    "KeyWrap" => Mode::Kw,
                    _ => Mode::Kwp,
                };
                let kek = AesKek::new(algorithm, &key).unwrap();
                let mut got = vec![0; ct.len()];
                kek.wrap_key(mode, &pt, &mut got).unwrap();
                assert_eq!(got, ct, "{test}");
                let mut got = vec![0; ct.len() - 8];
                assert_eq!(kek.unwrap_key(mode, &ct, &mut got).unwrap(), pt, "{test}");
            }
            mode => panic!("{test}: unexpected mode {mode}"),
        }
    }
}

// GCM with IVs of many lengths.
#[test]
fn gcm() {
    for test in tests("aws-lc/crypto/fipsmodule/modes/gcm_tests.txt") {
        let key = test.bytes("Key");
        let (iv, aad) = (test.bytes("Nonce"), test.bytes("AdditionalData"));
        let (pt, ct, tag) = (
            test.bytes("Plaintext"),
            test.bytes("Ciphertext"),
            test.bytes("Tag"),
        );
        check_aes_gcm(&test, &key, &iv, &aad, &pt, &ct, &tag, true);
    }
}

// HMAC with the hashes rind has. MD5, SHA-224, SHA-512/224, SHA-512/256,
// and SHA-3 it doesn't offer for HMAC.
#[test]
fn hmac() {
    for test in tests("aws-lc/crypto/hmac_extra/hmac_tests.txt") {
        let algorithm = match test.str("HMAC") {
            "SHA1" => &hmac::legacy::HMAC_SHA1,
            "SHA256" => &hmac::HMAC_SHA256,
            "SHA384" => &hmac::HMAC_SHA384,
            "SHA512" => &hmac::HMAC_SHA512,
            "MD5" | "SHA224" | "SHA512/224" | "SHA512/256" | "SHA3-224" | "SHA3-256"
            | "SHA3-384" | "SHA3-512" => continue,
            other => panic!("{test}: unexpected hash {other}"),
        };
        let key = hmac::Key::new(algorithm, &test.bytes("Key"));
        let tag = hmac::sign(&key, &test.bytes("Input"));
        assert_eq!(tag.as_ref(), test.bytes("Output"), "{test}");
    }
}

// Ed25519 signing and verification, from the reference implementation's
// `sign.input`.
#[test]
fn ed25519() {
    for test in tests("aws-lc/crypto/fipsmodule/curve25519/ed25519_tests.txt") {
        let (private, public) = (test.bytes("PRIV"), test.bytes("PUB"));
        let (msg, sig) = (test.bytes("MESSAGE"), test.bytes("SIG"));
        let key = ed25519::KeyPair::from_seed_and_public_key(&private[..32], &public).unwrap();
        assert_eq!(key.sign(&msg).as_ref(), sig, "{test}");
        let public = ed25519::PublicKey::new(&public).unwrap();
        public.verify(&msg, &sig).unwrap();
    }
}

fn uncompressed(test: &Test, x: &str, y: &str) -> Vec<u8> {
    [&[4][..], &test.bytes(x), &test.bytes(y)].concat()
}

// Public keys of edge-case scalars. aws-lc multiplies by any scalar, but
// refuses a private key outside 1 to n - 1, as rind does. P-224 and secp256k1
// rind doesn't offer.
#[test]
fn ec_scalar_base_mult() {
    for test in tests("aws-lc/crypto/fipsmodule/ec/ec_scalar_base_mult_tests.txt") {
        let (algorithm, order) = match test.str("Curve") {
            "P-256" => (
                &ECDH_P256,
                "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551",
            ),
            "P-384" => (
                &ECDH_P384,
                "ffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf\
                 581a0db248b0a77aecec196accc52973",
            ),
            "P-521" => (
                &ECDH_P521,
                "01ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff\
                 fffa51868783bf2f966b7fcc0148f709a5d03bb5c9b8899c47aebb6fb71e9138\
                 6409",
            ),
            "P-224" | "secp256k1" => continue,
            other => panic!("{test}: unexpected curve {other}"),
        };
        let order = hex::decode(order).unwrap();
        let n = test.bytes("N");
        let n = &n[n.iter().position(|b| *b != 0).unwrap_or(n.len())..];
        let scalar = [&vec![0; order.len().saturating_sub(n.len())][..], n].concat();
        let key = agreement::PrivateKey::from_scalar(algorithm, &scalar);
        if n.is_empty() || scalar.len() > order.len() || scalar >= order {
            assert!(key.is_err(), "{test}");
            continue;
        }
        assert_eq!(
            key.unwrap().public_key().as_ref(),
            uncompressed(&test, "X", "Y"),
            "{test}"
        );
    }
}

// NIST's ECDH vectors. P-224 and secp256k1 rind doesn't offer.
#[test]
fn ecdh() {
    for test in tests("aws-lc/crypto/ecdh_extra/ecdh_tests.txt") {
        let algorithm = match test.str("Curve") {
            "P-256" => &ECDH_P256,
            "P-384" => &ECDH_P384,
            "P-521" => &ECDH_P521,
            "P-224" | "secp256k1" => continue,
            other => panic!("{test}: unexpected curve {other}"),
        };
        let key = agreement::PrivateKey::from_scalar(algorithm, &test.bytes("Private")).unwrap();
        assert_eq!(
            key.public_key().as_ref(),
            uncompressed(&test, "X", "Y"),
            "{test}"
        );
        let secret = key.agree(&uncompressed(&test, "PeerX", "PeerY")).unwrap();
        assert_eq!(secret.as_ref(), test.bytes("Z"), "{test}");
    }
}

/// A key of an EVP test file, kept encoded: rind parses each for the
/// algorithm an operation names.
#[derive(Clone)]
enum EvpKey {
    Rsa {
        pkcs8: Option<Vec<u8>>,
        spki: Vec<u8>,
    },
    Ec {
        curve: usize,
        pkcs8: Option<Vec<u8>>,
        spki: Vec<u8>,
    },
    Ed25519 {
        pkcs8: Option<Vec<u8>>,
        spki: Vec<u8>,
    },
    X25519 {
        pkcs8: Option<Vec<u8>>,
        spki: Vec<u8>,
    },
}

const EC_CURVES: [(&agreement::Algorithm, &ecdsa::SigningAlgorithm); 3] = [
    (&ECDH_P256, &ecdsa::sign::P256_SHA256_ASN1),
    (&ECDH_P384, &ecdsa::sign::P384_SHA384_ASN1),
    (&ECDH_P521, &ecdsa::sign::P521_SHA512_ASN1),
];

/// Parses an RSA public key as rind verifies with it: a key under 2048 bits
/// parses, but verifies only under a legacy algorithm, so is refused here.
fn rsa_public_key(spki: &[u8]) -> Result<rsa::PublicKey, Error> {
    let key = rsa::PublicKey::from_spki(spki)?;
    match key.verify(&rsa::verify::PKCS1_SHA256, b"", &[]) {
        Err(e @ Error::KeyRejected(_)) => Err(e),
        _ => Ok(key),
    }
}

/// Parses an EVP test's key of type `kind`, a PKCS#8 private key or an SPKI
/// public one, as rind does: RSA, EC, Ed25519, or X25519.
fn parse_evp_key(kind: &str, der: &[u8], private: bool) -> Result<EvpKey, Error> {
    let pkcs8 = Some(der.to_vec());
    match (kind, private) {
        ("RSA", true) => rsa::KeyPair::from_pkcs8(der).map(|key| EvpKey::Rsa {
            pkcs8,
            spki: key.public_key().to_spki().as_ref().to_vec(),
        }),
        ("RSA", false) => rsa_public_key(der).map(|_| EvpKey::Rsa {
            pkcs8: None,
            spki: der.to_vec(),
        }),
        ("EC", _) => {
            let mut last = Error::Unsupported;
            for (curve, (ecdh, _)) in EC_CURVES.iter().enumerate() {
                let parsed = match private {
                    true => agreement::PrivateKey::from_pkcs8(ecdh, der)
                        .map(|key| key.public_key().to_spki().as_ref().to_vec()),
                    false => agreement::PublicKey::from_spki(ecdh, der).map(|_| der.to_vec()),
                };
                match parsed {
                    Ok(spki) => {
                        let pkcs8 = private.then(|| der.to_vec());
                        return Ok(EvpKey::Ec { curve, pkcs8, spki });
                    }
                    Err(e) => last = e,
                }
            }
            Err(last)
        }
        ("Ed25519", true) => ed25519::KeyPair::from_pkcs8(der).map(|key| EvpKey::Ed25519 {
            pkcs8,
            spki: key.public_key().to_spki().as_ref().to_vec(),
        }),
        ("Ed25519", false) => ed25519::PublicKey::from_spki(der).map(|_| EvpKey::Ed25519 {
            pkcs8: None,
            spki: der.to_vec(),
        }),
        ("X25519", true) => {
            agreement::PrivateKey::from_pkcs8(&agreement::X25519, der).map(|key| EvpKey::X25519 {
                pkcs8,
                spki: key.public_key().to_spki().as_ref().to_vec(),
            })
        }
        ("X25519", false) => {
            agreement::PublicKey::from_spki(&agreement::X25519, der).map(|_| EvpKey::X25519 {
                pkcs8: None,
                spki: der.to_vec(),
            })
        }
        _ => Err(Error::Unsupported),
    }
}

/// The RSA verification algorithm an EVP test names, if rind has it.
fn evp_rsa_verify(test: &Test) -> Option<&'static rsa::VerificationAlgorithm> {
    let digest = test.get("Digest")?;
    match test.get("RSAPadding").unwrap_or("PKCS1") {
        "PKCS1" => Some(match digest {
            "SHA1" => &rsa::verify::legacy::PKCS1_SHA1,
            "SHA256" => &rsa::verify::PKCS1_SHA256,
            "SHA384" => &rsa::verify::PKCS1_SHA384,
            "SHA512" => &rsa::verify::PKCS1_SHA512,
            _ => return None,
        }),
        "PSS" => {
            if test.get("MGF1Digest").is_some_and(|mgf| mgf != digest) {
                return None;
            }
            let (exact, any, len) = match digest {
                "SHA256" => (
                    &rsa::verify::PSS_SHA256,
                    &rsa::verify::PSS_SHA256_ANY_SALT,
                    "32",
                ),
                "SHA384" => (
                    &rsa::verify::PSS_SHA384,
                    &rsa::verify::PSS_SHA384_ANY_SALT,
                    "48",
                ),
                "SHA512" => (
                    &rsa::verify::PSS_SHA512,
                    &rsa::verify::PSS_SHA512_ANY_SALT,
                    "64",
                ),
                _ => return None,
            };
            // aws-lc's -1 is the digest's length, and -2 any length.
            match test.get("PSSSaltLength").unwrap_or("-1") {
                "-2" => Some(any),
                s if s == "-1" || s == len => Some(exact),
                _ => None,
            }
        }
        _ => None,
    }
}

/// The RSA signing algorithm an EVP test names, if rind has it.
fn evp_rsa_sign(test: &Test) -> Option<&'static rsa::SigningAlgorithm> {
    let digest = test.get("Digest")?;
    match test.get("RSAPadding").unwrap_or("PKCS1") {
        "PKCS1" => Some(match digest {
            "SHA256" => &rsa::sign::PKCS1_SHA256,
            "SHA384" => &rsa::sign::PKCS1_SHA384,
            "SHA512" => &rsa::sign::PKCS1_SHA512,
            _ => return None,
        }),
        "PSS" => {
            if test.get("MGF1Digest").is_some_and(|mgf| mgf != digest) {
                return None;
            }
            let (algorithm, len) = match digest {
                "SHA256" => (&rsa::sign::PSS_SHA256, "32"),
                "SHA384" => (&rsa::sign::PSS_SHA384, "48"),
                "SHA512" => (&rsa::sign::PSS_SHA512, "64"),
                _ => return None,
            };
            let salt = test.get("PSSSaltLength").unwrap_or("-1");
            (salt == "-1" || salt == len).then_some(algorithm)
        }
        _ => None,
    }
}

/// The ECDSA verification algorithm for `curve` and an EVP test's digest.
fn evp_ecdsa_verify(curve: usize, test: &Test) -> Option<&'static ecdsa::VerificationAlgorithm> {
    let algorithms = [
        [
            &ecdsa::verify::P256_SHA256_ASN1,
            &ecdsa::verify::P256_SHA384_ASN1,
            &ecdsa::verify::P256_SHA512_ASN1,
        ],
        [
            &ecdsa::verify::P384_SHA256_ASN1,
            &ecdsa::verify::P384_SHA384_ASN1,
            &ecdsa::verify::P384_SHA512_ASN1,
        ],
        [
            &ecdsa::verify::P521_SHA256_ASN1,
            &ecdsa::verify::P521_SHA384_ASN1,
            &ecdsa::verify::P521_SHA512_ASN1,
        ],
    ];
    let hash = match test.get("Digest")? {
        "SHA256" => 0,
        "SHA384" => 1,
        "SHA512" => 2,
        _ => return None,
    };
    Some(algorithms[curve][hash])
}

/// The OAEP algorithm an EVP test names, if rind has it: one hash for both
/// OAEP and MGF1. PKCS#1 v1.5 encryption and raw RSA rind refuses.
fn evp_oaep(test: &Test) -> Option<&'static rind::rsa::OaepAlgorithm> {
    if test.get("RSAPadding") != Some("OAEP") {
        return None;
    }
    let digest = test.get("OAEPDigest").unwrap_or("SHA1");
    if test.get("MGF1Digest").unwrap_or(digest) != digest {
        return None;
    }
    Some(match digest {
        "SHA1" => &rind::rsa::legacy::OAEP_SHA1,
        "SHA256" => &rind::rsa::OAEP_SHA256,
        "SHA384" => &rind::rsa::OAEP_SHA384,
        "SHA512" => &rind::rsa::OAEP_SHA512,
        _ => return None,
    })
}

/// Keys aws-lc takes that rind refuses, each for a reason it documents.
const EVP_REFUSED: &[(&str, &str)] = &[
    (
        "P-224-ExplicitParameters",
        "P-224, which rind doesn't offer",
    ),
    (
        "P-256-ExplicitParameters",
        "explicit curve parameters, which RFC 5480 forbids",
    ),
    (
        "P-256-ExplicitParameters-NoCofactor",
        "explicit curve parameters, which RFC 5480 forbids",
    ),
    (
        "P-256-SPKI-EXPLICIT",
        "explicit curve parameters, which RFC 5480 forbids",
    ),
    (
        "P-384-ExplicitParameters",
        "explicit curve parameters, which RFC 5480 forbids",
    ),
    (
        "P-521-ExplicitParameters",
        "explicit curve parameters, which RFC 5480 forbids",
    ),
    ("RSA-512", "a modulus under 2048 bits"),
    ("RSA-515", "a modulus under 2048 bits"),
    ("RSA-OAEP-1", "a modulus under 2048 bits"),
    ("RSA-OAEP-2", "a modulus under 2048 bits"),
    ("RSA-OAEP-3", "a modulus under 2048 bits"),
    ("RSA-OAEP-4", "a modulus under 2048 bits"),
    ("RSA-OAEP-5", "a modulus under 2048 bits"),
    ("RSA-OAEP-6", "a modulus under 2048 bits"),
    ("RSA-OAEP-7", "a modulus under 2048 bits"),
    ("RSA-OAEP-8", "a modulus under 2048 bits"),
    ("RSA-OAEP-9", "a modulus under 2048 bits"),
    ("RSA-PSS-1", "a modulus under 2048 bits"),
    ("RSA-PSS-2", "a modulus under 2048 bits"),
    ("RSA-PSS-3", "a modulus under 2048 bits"),
    ("RSA-PSS-4", "a modulus under 2048 bits"),
    ("RSA-PSS-5", "a modulus under 2048 bits"),
    ("RSA-PSS-6", "a modulus under 2048 bits"),
    ("RSA-PSS-7", "a modulus under 2048 bits"),
    ("RSA-PSS-8", "a modulus under 2048 bits"),
    ("RSA-PSS-9", "a modulus under 2048 bits"),
    ("RSA-PrimeMismatch", "a modulus under 2048 bits"),
    ("RSA-Swapped", "a modulus under 2048 bits"),
];

/// Keys BoringSSL refuses that rind takes, as aws-lc does.
const EVP_ACCEPTED: &[(&str, &str)] = &[(
    "RSA-2048-SPKI-Invalid",
    "rsaEncryption without its NULL parameters, which aws-lc takes as OpenSSL does",
)];

// aws-lc's and BoringSSL's EVP tests: parsing keys, signing and verifying
// messages, OAEP, and key agreement. rind refuses every key aws-lc does, and
// takes every one it does but those `EVP_REFUSED` lists. Their `Sign` and
// `Verify` tests give a digest without its message, which rind's API never
// takes, as it computes the digest itself.
#[test]
fn evp() {
    use std::collections::HashMap;

    let mut refused = std::collections::BTreeSet::new();
    let mut accepted = std::collections::BTreeSet::new();
    let mut ran: HashMap<&str, usize> = HashMap::new();
    for path in [
        "aws-lc/crypto/evp_extra/evp_tests.txt",
        "boringssl/crypto/evp/test/rsa_tests.txt",
        "boringssl/crypto/evp/test/ec_tests.txt",
        "boringssl/crypto/evp/test/ed25519_tests.txt",
        "boringssl/crypto/evp/test/x25519_tests.txt",
    ] {
        let mut keys: HashMap<String, EvpKey> = HashMap::new();
        for test in tests(path) {
            // A key: aws-lc's `PrivateKey`/`PublicKey` with `Input`, or
            // BoringSSL's `Key` with `PKCS8` or `SPKI`.
            let encoded = if let Some(name) = test.get("PrivateKey") {
                Some((name, test.get("Type"), test.bytes("Input"), true))
            } else if let Some(name) = test.get("PublicKey") {
                Some((name, test.get("Type"), test.bytes("Input"), false))
            } else if let Some(name) = test.get("Key") {
                let kind = test.get("Algorithm");
                match (test.get("PKCS8"), test.get("SPKI")) {
                    (Some(_), _) => Some((name, kind, test.bytes("PKCS8"), true)),
                    (None, Some(_)) => Some((name, kind, test.bytes("SPKI"), false)),
                    (None, None) => None,
                }
            } else {
                None
            };
            if let Some((name, kind, der, private)) = encoded {
                // A key without a type is any of them that parses. BoringSSL
                // names the curve where aws-lc says only `EC`.
                let kinds = match kind {
                    Some("EC-P-256" | "EC-P-384" | "EC-P-521") => vec!["EC"],
                    Some(kind) => vec![kind],
                    None => vec!["RSA", "EC", "Ed25519", "X25519"],
                };
                let parsed = kinds
                    .iter()
                    .find_map(|kind| parse_evp_key(kind, &der, private).ok());
                // With `PKCS8VersionOut`, the error is re-encoding's.
                let error = test
                    .get("Error")
                    .filter(|_| test.get("PKCS8VersionOut").is_none());
                match (error, parsed) {
                    (Some(_), None) => {}
                    (Some(_), Some(_)) => {
                        accepted.insert(name.to_string());
                    }
                    (None, Some(key)) => {
                        keys.insert(name.to_string(), key);
                    }
                    (None, None) => {
                        let offered = kinds
                            .iter()
                            .any(|k| ["RSA", "EC", "Ed25519", "X25519"].contains(k));
                        if offered {
                            refused.insert(name.to_string());
                        }
                    }
                }
                continue;
            }

            let key = |name: &str| keys.get(name.trim_end_matches("/Private")).cloned();
            if let Some(name) = test.get("VerifyMessage") {
                let Some(key) = key(name) else { continue };
                let (msg, sig) = (test.bytes("Input"), test.bytes("Output"));
                let result = match &key {
                    EvpKey::Rsa { spki, .. } => evp_rsa_verify(&test).map(|algorithm| {
                        rsa::PublicKey::from_spki(spki)
                            .and_then(|key| key.verify(algorithm, &msg, &sig))
                    }),
                    EvpKey::Ec { curve, spki, .. } => {
                        evp_ecdsa_verify(*curve, &test).map(|algorithm| {
                            ecdsa::PublicKey::from_spki(algorithm, spki)
                                .and_then(|key| key.verify(&msg, &sig))
                        })
                    }
                    EvpKey::Ed25519 { spki, .. } => Some(
                        ed25519::PublicKey::from_spki(spki).and_then(|key| key.verify(&msg, &sig)),
                    ),
                    EvpKey::X25519 { .. } => None,
                };
                *ran.entry("VerifyMessage").or_default() += usize::from(result.is_some());
                match (result, test.get("Error")) {
                    (None, _) => {}
                    (Some(result), None) => assert_eq!(result, Ok(()), "{test}"),
                    (Some(result), Some(_)) => assert!(result.is_err(), "{test}"),
                }
            } else if let Some(name) = test.get("SignMessage") {
                let Some(key) = key(name) else { continue };
                if test.get("Error").is_some() {
                    continue;
                }
                let msg = test.bytes("Input");
                match &key {
                    EvpKey::Rsa {
                        pkcs8: Some(pkcs8),
                        spki,
                    } => {
                        let (Some(algorithm), Some(verification)) =
                            (evp_rsa_sign(&test), evp_rsa_verify(&test))
                        else {
                            continue;
                        };
                        let pair = rsa::KeyPair::from_pkcs8(pkcs8).unwrap();
                        let sig = pair.sign(algorithm, &msg).unwrap();
                        // PKCS#1 v1.5 is deterministic; PSS takes a salt.
                        if test.get("RSAPadding").unwrap_or("PKCS1") == "PKCS1" {
                            assert_eq!(sig.as_ref(), test.bytes("Output"), "{test}");
                        }
                        let public = rsa::PublicKey::from_spki(spki).unwrap();
                        public.verify(verification, &msg, sig.as_ref()).unwrap();
                        *ran.entry("SignMessage").or_default() += 1;
                    }
                    EvpKey::Ec {
                        curve,
                        pkcs8: Some(pkcs8),
                        spki,
                    } => {
                        let Some(verification) = evp_ecdsa_verify(*curve, &test) else {
                            continue;
                        };
                        let algorithm = EC_CURVES[*curve].1;
                        let pair = ecdsa::KeyPair::from_pkcs8(algorithm, pkcs8).unwrap();
                        let public = ecdsa::PublicKey::from_spki(verification, spki).unwrap();
                        // A key pair signs with its curve's own hash.
                        if public
                            .verify(&msg, pair.sign(&msg).unwrap().as_ref())
                            .is_err()
                        {
                            assert_ne!(
                                *curve,
                                ["SHA256", "SHA384", "SHA512"]
                                    .iter()
                                    .position(|d| Some(*d) == test.get("Digest"))
                                    .unwrap(),
                                "{test}"
                            );
                        }
                    }
                    EvpKey::Ed25519 {
                        pkcs8: Some(pkcs8), ..
                    } => {
                        let pair = ed25519::KeyPair::from_pkcs8(pkcs8).unwrap();
                        assert_eq!(pair.sign(&msg).as_ref(), test.bytes("Output"), "{test}");
                        *ran.entry("SignMessage").or_default() += 1;
                    }
                    _ => {}
                }
            } else if let Some(name) = test.get("Decrypt") {
                let (
                    Some(EvpKey::Rsa {
                        pkcs8: Some(pkcs8), ..
                    }),
                    Some(algorithm),
                ) = (key(name), evp_oaep(&test))
                else {
                    continue;
                };
                let label = test
                    .get("OAEPLabel")
                    .map(|_| test.bytes("OAEPLabel"))
                    .unwrap_or_default();
                let key = rind::rsa::DecryptingKey::from_pkcs8(algorithm, &pkcs8).unwrap();
                let result = key
                    .decrypt(&test.bytes("Input"), &label)
                    .map(|pt| pt.as_ref().to_vec());
                *ran.entry("Decrypt").or_default() += 1;
                match test.get("Error") {
                    None => assert_eq!(result, Ok(test.bytes("Output")), "{test}"),
                    Some(_) => assert!(result.is_err(), "{test}"),
                }
            } else if let Some(name) = test.get("Encrypt") {
                let (
                    Some(EvpKey::Rsa {
                        pkcs8: Some(pkcs8), ..
                    }),
                    Some(algorithm),
                ) = (key(name), evp_oaep(&test))
                else {
                    continue;
                };
                let label = test
                    .get("OAEPLabel")
                    .map(|_| test.bytes("OAEPLabel"))
                    .unwrap_or_default();
                let key = rind::rsa::DecryptingKey::from_pkcs8(algorithm, &pkcs8).unwrap();
                let msg = test.bytes("Input");
                let ct = key.public_key().encrypt(&msg, &label).unwrap();
                assert_eq!(
                    key.decrypt(ct.as_ref(), &label).unwrap().as_ref(),
                    msg,
                    "{test}"
                );
                *ran.entry("Encrypt").or_default() += 1;
            } else if let Some(name) = test.get("Derive") {
                let (Some(private), Some(peer)) = (key(name), key(test.str("DerivePeer"))) else {
                    continue;
                };
                let (algorithm, pkcs8, peer) = match (private, peer) {
                    (
                        EvpKey::Ec {
                            curve,
                            pkcs8: Some(pkcs8),
                            ..
                        },
                        EvpKey::Ec {
                            spki,
                            curve: peer_curve,
                            ..
                        },
                    ) => {
                        if curve != peer_curve {
                            assert!(test.get("Error").is_some(), "{test}");
                            continue;
                        }
                        (EC_CURVES[curve].0, pkcs8, spki)
                    }
                    (
                        EvpKey::X25519 {
                            pkcs8: Some(pkcs8), ..
                        },
                        EvpKey::X25519 { spki, .. },
                    ) => (&agreement::X25519, pkcs8, spki),
                    _ => continue,
                };
                let private = agreement::PrivateKey::from_pkcs8(algorithm, &pkcs8).unwrap();
                let result = agreement::PublicKey::from_spki(algorithm, &peer)
                    .and_then(|peer| private.agree(peer.as_ref()))
                    .map(|secret| secret.as_ref().to_vec());
                *ran.entry("Derive").or_default() += 1;
                match test.get("Error") {
                    None => assert_eq!(result, Ok(test.bytes("Output")), "{test}"),
                    Some(_) => assert!(result.is_err(), "{test}"),
                }
            }
        }
        // An unrecognized `Algorithm` would skip every key a file holds.
        assert!(!keys.is_empty(), "{path}: no key parsed");
    }

    for kind in [
        "VerifyMessage",
        "SignMessage",
        "Decrypt",
        "Encrypt",
        "Derive",
    ] {
        assert!(ran.get(kind).is_some_and(|n| *n > 0), "no {kind} test ran");
    }

    let expected = EVP_REFUSED
        .iter()
        .map(|(name, _)| name.to_string())
        .collect();
    assert_eq!(refused, expected, "refused");
    let expected = EVP_ACCEPTED
        .iter()
        .map(|(name, _)| name.to_string())
        .collect();
    assert_eq!(accepted, expected, "accepted");
}
