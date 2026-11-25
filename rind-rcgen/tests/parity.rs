//! rind-rcgen's `KeyPair` against rcgen's own on its `aws_lc_rs` backend,
//! which the tests build: each loads, refuses, and generates alike, for
//! every key type, encoding, PKCS#8 version, and label a caller can give.

use rcgen::{
    Error, PKCS_ECDSA_P256_SHA256, PKCS_ECDSA_P384_SHA384, PKCS_ECDSA_P521_SHA512, PKCS_ED25519,
    PKCS_RSA_SHA256, PKCS_RSA_SHA384, PKCS_RSA_SHA512, PublicKeyData, SignatureAlgorithm,
    SigningKey,
};
use rind::ecdsa::{self, KeyPair as EcdsaKeyPair};
use rind_rcgen::KeyPair;
use rustls::pki_types::{PrivateKeyDer, PrivatePkcs1KeyDer, PrivatePkcs8KeyDer, PrivateSec1KeyDer};

/// The algorithms both name, which a key loads for.
const ALGORITHMS: [&SignatureAlgorithm; 6] = [
    &PKCS_ECDSA_P256_SHA256,
    &PKCS_ECDSA_P384_SHA384,
    &PKCS_ED25519,
    &PKCS_RSA_SHA256,
    &PKCS_RSA_SHA384,
    &PKCS_RSA_SHA512,
];

/// `der` with its first `INTEGER`, the PKCS#8 or SEC1 version, set to `version`.
fn with_version(der: &[u8], version: u8) -> Vec<u8> {
    let mut der = der.to_vec();
    let at = match der[1] {
        0x81 => 3,
        0x82 => 4,
        _ => 2,
    };
    assert_eq!(der[at..at + 2], [0x02, 0x01]);
    der[at + 2] = version;
    der
}

/// Every encoding of every key type a caller might hand either side.
fn encodings() -> Vec<(&'static str, Vec<u8>)> {
    let rsa_pkcs1 = include_bytes!("../../rind/src/high/rsa/rsa2048.der").to_vec();
    let rsa = rind::rsa::KeyPair::from_pkcs1(&rsa_pkcs1)
        .unwrap()
        .to_pkcs8();
    let ed25519 = rind::ed25519::KeyPair::generate().unwrap();
    let mut out = vec![
        ("RSA PKCS#1", rsa_pkcs1),
        ("RSA PKCS#8", rsa.as_ref().to_vec()),
        ("RSA PKCS#8 v2", with_version(rsa.as_ref(), 1)),
        ("Ed25519 PKCS#8 v2", ed25519.to_pkcs8().as_ref().to_vec()),
        ("Ed25519 PKCS#8 v1", ed25519.to_pkcs8v1().as_ref().to_vec()),
        (
            "Ed25519 PKCS#8 v2 without its public key",
            with_version(ed25519.to_pkcs8v1().as_ref(), 1),
        ),
        (
            "X25519 PKCS#8",
            rind::agreement::PrivateKey::generate(&rind::agreement::X25519)
                .unwrap()
                .to_pkcs8()
                .as_ref()
                .to_vec(),
        ),
        (
            "ML-DSA-44 PKCS#8",
            // RFC 9881's seed form, written out since this crate builds rind
            // without ML-DSA.
            [
                &[0x30, 0x34, 0x02, 0x01, 0x00, 0x30, 0x0b, 0x06, 0x09][..],
                &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x11],
                &[0x04, 0x22, 0x80, 0x20],
                &[0x42; 32],
            ]
            .concat(),
        ),
        ("garbage", vec![0x30, 0x03, 0x02, 0x01, 0x00]),
    ];
    for (name, alg) in [
        ("P-256", &ecdsa::sign::P256_SHA256_ASN1),
        ("P-384", &ecdsa::sign::P384_SHA384_ASN1),
        ("P-521", &ecdsa::sign::P521_SHA512_ASN1),
    ] {
        let key = EcdsaKeyPair::generate(alg).unwrap();
        let pkcs8 = key.to_pkcs8().as_ref().to_vec();
        out.push((name, pkcs8.clone()));
        out.push((name, with_version(&pkcs8, 1)));
        out.push((name, key.to_sec1().as_ref().to_vec()));
    }
    out
}

/// Keys rcgen loads through AWS-LC that rind refuses: curves given by
/// explicit parameters, and public points in X9.62's hybrid form.
fn refused() -> Vec<(&'static str, Vec<u8>)> {
    let key = EcdsaKeyPair::generate(&ecdsa::sign::P256_SHA256_ASN1).unwrap();
    let mut hybrid = key.to_sec1().as_ref().to_vec();
    // The public key's BIT STRING: 65 bytes after its unused-bits byte.
    let at = hybrid.len() - 65;
    assert_eq!(hybrid[at - 3..=at], [0x03, 0x42, 0x00, 0x04]);
    hybrid[at] = 0x06 | (hybrid[hybrid.len() - 1] & 1);
    vec![
        (
            "P-256 SEC1 with explicit parameters",
            include_bytes!("data/p256-explicit.sec1.der").to_vec(),
        ),
        (
            "P-256 PKCS#8 with explicit parameters",
            include_bytes!("data/p256-explicit.pkcs8.der").to_vec(),
        ),
        ("P-256 SEC1 with a hybrid public point", hybrid),
    ]
}

#[test]
fn refuses_what_rcgen_loads() {
    for (name, der) in refused() {
        let theirs = rcgen::KeyPair::from_der_and_sign_algo(
            &labels(&der)[if name.contains("PKCS#8") { 0 } else { 1 }],
            &PKCS_ECDSA_P256_SHA256,
        );
        assert!(theirs.is_ok(), "{name}: rcgen refuses it");
        for key in labels(&der) {
            assert!(KeyPair::try_from(&key).is_err(), "{name}");
            for alg in ALGORITHMS {
                assert!(
                    KeyPair::from_der_and_sign_algo(&key, alg).is_err(),
                    "{name}"
                );
            }
        }
    }
}

/// `der` under each label `rustls_pki_types` gives a private key.
fn labels(der: &[u8]) -> [PrivateKeyDer<'_>; 3] {
    [
        PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(der)),
        PrivateKeyDer::Sec1(PrivateSec1KeyDer::from(der)),
        PrivateKeyDer::Pkcs1(PrivatePkcs1KeyDer::from(der)),
    ]
}

/// Both loaded alike: refused by both, or loaded by both with the same
/// algorithm, public key, and serialized DER.
fn same(what: &str, ours: Result<KeyPair, Error>, theirs: Result<rcgen::KeyPair, Error>) {
    match (ours, theirs) {
        (Err(_), Err(_)) => {}
        (Ok(ours), Ok(theirs)) => {
            assert_eq!(ours.algorithm(), theirs.algorithm(), "{what}");
            assert_eq!(ours.public_key_raw(), theirs.public_key_raw(), "{what}");
            assert_eq!(ours.serialized_der(), theirs.serialized_der(), "{what}");
            assert_eq!(
                ours.subject_public_key_info(),
                theirs.subject_public_key_info(),
                "{what}"
            );
        }
        (ours, theirs) => panic!(
            "{what}: rind-rcgen {:?}, rcgen {:?}",
            ours.map(|k| k.algorithm()),
            theirs.map(|k| k.algorithm())
        ),
    }
}

#[test]
fn loads_as_rcgen() {
    for (name, der) in encodings() {
        for (label, key) in labels(&der).iter().enumerate() {
            let what = format!("{name} labeled {label}");
            let ours = KeyPair::try_from(key);
            let theirs = rcgen::KeyPair::try_from(key);
            if theirs
                .as_ref()
                .is_ok_and(|key| key.algorithm() == &PKCS_ECDSA_P521_SHA512)
            {
                // rcgen names P-521 only with its `aws_lc_rs` feature, which
                // builds AWS-LC.
                assert_eq!(ours.err(), Some(Error::CouldNotParseKeyPair), "{what}");
                continue;
            }
            same(&what, ours, theirs);

            for alg in ALGORITHMS {
                let what = format!("{what} for {alg:?}");
                same(
                    &what,
                    KeyPair::from_der_and_sign_algo(key, alg),
                    rcgen::KeyPair::from_der_and_sign_algo(key, alg),
                );
                let pkcs8 = PrivatePkcs8KeyDer::from(&der[..]);
                same(
                    &what,
                    KeyPair::from_pkcs8_der_and_sign_algo(&pkcs8, alg),
                    rcgen::KeyPair::from_pkcs8_der_and_sign_algo(&pkcs8, alg),
                );
            }
        }
    }
}

/// Each generates what the other loads, and refuses to generate alike.
#[test]
fn generates_as_rcgen() {
    for alg in ALGORITHMS {
        let ours = KeyPair::generate_for(alg).unwrap();
        let theirs = rcgen::KeyPair::generate_for(alg).unwrap();
        let pkcs8 = |der| PrivatePkcs8KeyDer::from(der);
        let reloaded =
            rcgen::KeyPair::from_pkcs8_der_and_sign_algo(&pkcs8(ours.serialize_der()), alg)
                .unwrap();
        assert_eq!(reloaded.public_key_raw(), ours.public_key_raw());
        let reloaded =
            KeyPair::from_pkcs8_der_and_sign_algo(&pkcs8(theirs.serialize_der()), alg).unwrap();
        assert_eq!(reloaded.public_key_raw(), theirs.public_key_raw());
        // An ECDSA signature's DER varies in length.
        if ![&PKCS_ECDSA_P256_SHA256, &PKCS_ECDSA_P384_SHA384].contains(&alg) {
            assert_eq!(
                ours.sign(b"message").unwrap().len(),
                theirs.sign(b"message").unwrap().len(),
                "{alg:?}"
            );
        }
    }

    for (ours, theirs) in [
        (rind_rcgen::RsaKeySize::_2048, rcgen::RsaKeySize::_2048),
        (rind_rcgen::RsaKeySize::_3072, rcgen::RsaKeySize::_3072),
    ] {
        assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));
        let key = KeyPair::generate_rsa_for(&PKCS_RSA_SHA384, ours).unwrap();
        let reference = rcgen::KeyPair::generate_rsa_for(&PKCS_RSA_SHA384, theirs).unwrap();
        assert_eq!(key.algorithm(), &PKCS_RSA_SHA384);
        assert_eq!(
            key.sign(b"message").unwrap().len(),
            reference.sign(b"message").unwrap().len()
        );
        let reloaded = rcgen::KeyPair::from_pkcs8_der_and_sign_algo(
            &PrivatePkcs8KeyDer::from(key.serialize_der()),
            &PKCS_RSA_SHA384,
        )
        .unwrap();
        assert_eq!(reloaded.public_key_raw(), key.public_key_raw());
    }

    for alg in [&PKCS_ECDSA_P256_SHA256, &PKCS_ED25519] {
        assert_eq!(
            KeyPair::generate_rsa_for(alg, rind_rcgen::RsaKeySize::_2048).err(),
            rcgen::KeyPair::generate_rsa_for(alg, rcgen::RsaKeySize::_2048).err(),
        );
    }
}
