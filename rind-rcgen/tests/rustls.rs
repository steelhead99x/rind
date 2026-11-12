//! Certificates signed by rind-rcgen verify under rind-rustls and under
//! rustls on aws-lc-rs, each key loads and matches its certificate, and keys
//! encode as rcgen's own do.

use std::sync::Arc;
use std::time::Duration;

use rcgen::{
    BasicConstraints, CertificateParams, Error, IsCa, Issuer, PKCS_ECDSA_P256_SHA256,
    PKCS_ECDSA_P384_SHA384, PKCS_ED25519, PKCS_RSA_SHA256, PKCS_RSA_SHA384, PKCS_RSA_SHA512,
    PublicKeyData, SerialNumber, SignatureAlgorithm,
};
use rind_rcgen::KeyPair;
use rustls::RootCertStore;
use rustls::client::WebPkiServerVerifier;
use rustls::client::danger::ServerCertVerifier;
use rustls::crypto::CryptoProvider;
use rustls::pki_types::{CertificateDer, PrivateKeyDer, PrivatePkcs8KeyDer, ServerName, UnixTime};
use rustls::sign::CertifiedKey;

/// Every algorithm rind-rcgen generates keys for.
const GENERATED: [&SignatureAlgorithm; 3] = [
    &PKCS_ECDSA_P256_SHA256,
    &PKCS_ECDSA_P384_SHA384,
    &PKCS_ED25519,
];

#[test]
fn self_signed() {
    for algorithm in GENERATED {
        let key = KeyPair::generate_for(algorithm).unwrap();
        let cert = params().self_signed(&key).unwrap();

        for provider in providers() {
            verify(&provider, cert.der(), cert.der()).unwrap();
            load(&provider, cert.der(), &key);
        }
    }
}

#[test]
fn signed_by_ca() {
    for algorithm in GENERATED {
        let ca_key = KeyPair::generate_for(algorithm).unwrap();
        let mut ca_params = params();
        ca_params.is_ca = IsCa::Ca(BasicConstraints::Unconstrained);
        let ca = ca_params.self_signed(&ca_key).unwrap();

        let key = KeyPair::generate_for(&PKCS_ECDSA_P256_SHA256).unwrap();
        let cert = params()
            .signed_by(&key, &Issuer::new(ca_params, &ca_key))
            .unwrap();

        for provider in providers() {
            verify(&provider, ca.der(), cert.der()).unwrap();
            load(&provider, cert.der(), &key);
        }
    }
}

#[test]
fn rsa_loads_but_does_not_generate() {
    let der = rsa_pkcs8();
    for algorithm in [&PKCS_RSA_SHA256, &PKCS_RSA_SHA384, &PKCS_RSA_SHA512] {
        let key = KeyPair::from_pkcs8_der_and_sign_algo(&der, algorithm).unwrap();
        let cert = params().self_signed(&key).unwrap();

        for provider in providers() {
            verify(&provider, cert.der(), cert.der()).unwrap();
            load(&provider, cert.der(), &key);
        }
        assert_eq!(
            KeyPair::generate_for(algorithm).unwrap_err(),
            Error::KeyGenerationUnavailable
        );
    }
}

#[test]
fn reloads_its_own_encoding() {
    for algorithm in GENERATED {
        let key = KeyPair::generate_for(algorithm).unwrap();
        let der = PrivatePkcs8KeyDer::from(key.serialize_der());
        let reloaded = KeyPair::from_pkcs8_der_and_sign_algo(&der, algorithm).unwrap();
        assert_eq!(reloaded.der_bytes(), key.der_bytes());
        assert_eq!(reloaded.serialized_der(), key.serialized_der());

        // Without an algorithm, as rcgen finds one.
        let found = KeyPair::try_from(key.serialized_der()).unwrap();
        assert_eq!(found.algorithm(), algorithm);
        assert_eq!(found.der_bytes(), key.der_bytes());
    }
}

#[test]
fn finds_rsa_as_sha256() {
    let key = KeyPair::try_from(&rsa_pkcs8()).unwrap();
    assert_eq!(key.algorithm(), &PKCS_RSA_SHA256);
    assert_eq!(
        KeyPair::try_from(&b"not a key"[..]).unwrap_err(),
        Error::CouldNotParseKeyPair
    );
}

#[cfg(feature = "pem")]
#[test]
fn matches_rcgen_pem() {
    let ours = KeyPair::generate().unwrap();
    let theirs = rcgen::KeyPair::try_from(ours.serialized_der()).unwrap();
    assert_eq!(ours.serialize_pem(), theirs.serialize_pem());
    assert_eq!(ours.public_key_pem(), theirs.public_key_pem());

    let reloaded = KeyPair::from_pem(&ours.serialize_pem()).unwrap();
    assert_eq!(reloaded.der_bytes(), ours.der_bytes());
}

/// PEM loads exactly where rcgen's `pem` crate parses it, whatever its
/// framing, wrapping, or whitespace.
#[cfg(feature = "pem")]
#[test]
fn parses_pem_as_rcgen() {
    let key = KeyPair::generate().unwrap();
    let pem = key.serialize_pem();
    let base64: String = pem.lines().filter(|l| !l.starts_with("-----")).collect();
    let wrap = |width: usize, sep: &str| {
        base64
            .as_bytes()
            .chunks(width)
            .map(|c| std::str::from_utf8(c).unwrap())
            .collect::<Vec<_>>()
            .join(sep)
    };
    let block = |label: &str, body: &str| {
        format!("-----BEGIN {label}-----\n{body}\n-----END {label}-----\n")
    };
    let mut corrupt = base64.clone();
    corrupt.replace_range(..1, "!");
    let unpadded = base64.trim_end_matches('=');

    let cases = [
        pem.clone(),
        pem.replace('\n', "\r\n"),
        block("PRIVATE KEY", &wrap(76, "\n")),
        block("PRIVATE KEY", &base64),
        block("PRIVATE KEY", &wrap(16, " \t\x0b\x0c\n")),
        block("PRIVATE KEY", &wrap(16, "\u{a0}\u{2028}")),
        block("EC PRIVATE KEY", &base64),
        format!("leading text\n{pem}trailing text"),
        block(
            "PRIVATE KEY",
            &format!("Proc-Type: 4,ENCRYPTED\n\n{base64}"),
        ),
        block("PRIVATE KEY", &format!("Proc-Type\n\n{base64}")),
        format!("-----BEGIN PRIVATE KEY-----\n{base64}\n-----END OTHER-----\n"),
        format!("------BEGIN PRIVATE KEY-----\n{base64}\n-----END PRIVATE KEY-----\n"),
        format!("-----BEGIN -----\n{base64}\n-----END -----\n"),
        block("PRIVATE KEY", &corrupt),
        block("PRIVATE KEY", unpadded),
        block("PRIVATE KEY", ""),
        String::new(),
    ];
    for case in cases {
        let ours = KeyPair::from_pem(&case).map(|k| k.serialize_der());
        let theirs = rcgen::KeyPair::from_pem(&case).map(|k| k.serialize_der());
        assert_eq!(
            ours.is_ok(),
            theirs.is_ok(),
            "{case:?}: {ours:?} vs {theirs:?}"
        );
        if let (Ok(ours), Ok(theirs)) = (ours, theirs) {
            assert_eq!(ours, theirs, "{case:?}");
        }
    }
}

#[test]
fn refusal_keeps_rinds_reason() {
    let p256 = PrivatePkcs8KeyDer::from(KeyPair::generate().unwrap());
    assert_eq!(
        KeyPair::from_pkcs8_der_and_sign_algo(&p256, &PKCS_ECDSA_P384_SHA384).unwrap_err(),
        Error::RingKeyRejected("mismatched PKCS#8 parameters".to_string())
    );
    assert_eq!(
        KeyPair::from_pkcs8_der_and_sign_algo(&p256, &PKCS_RSA_SHA256).unwrap_err(),
        Error::RingKeyRejected("mismatched PKCS#8 algorithm".to_string())
    );
}

fn rsa_pkcs8() -> PrivatePkcs8KeyDer<'static> {
    PrivatePkcs8KeyDer::from(&include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der")[..])
}

fn providers() -> [Arc<CryptoProvider>; 2] {
    [
        Arc::new(rind_rustls::default_provider()),
        Arc::new(rustls::crypto::aws_lc_rs::default_provider()),
    ]
}

fn params() -> CertificateParams {
    let mut params = CertificateParams::new(["localhost".to_string()]).unwrap();
    params.serial_number = Some(SerialNumber::from(1));
    params
}

fn verify(
    provider: &Arc<CryptoProvider>,
    root: &CertificateDer<'_>,
    cert: &CertificateDer<'_>,
) -> Result<(), rustls::Error> {
    let mut roots = RootCertStore::empty();
    roots.add(root.clone().into_owned()).unwrap();
    let verifier = WebPkiServerVerifier::builder_with_provider(roots.into(), provider.clone())
        .build()
        .unwrap();

    // Inside rcgen's default validity, without reading the wall clock.
    let now = UnixTime::since_unix_epoch(Duration::from_secs(1_800_000_000));
    let name = ServerName::try_from("localhost").unwrap();
    verifier
        .verify_server_cert(cert, &[], &name, &[], now)
        .map(|_| ())
}

#[test]
fn der_load_and_accessors() {
    for algorithm in GENERATED {
        let key = KeyPair::generate_for(algorithm).unwrap();
        let der = PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(key.serialize_der()));
        let loaded = KeyPair::from_der_and_sign_algo(&der, algorithm).unwrap();
        assert!(loaded.is_compatible(algorithm));
        assert!(!loaded.is_compatible(&PKCS_RSA_SHA256));
        assert_eq!(
            loaded.compatible_algs().collect::<Vec<_>>(),
            vec![algorithm]
        );
        let raw = loaded.public_key_raw();
        assert!(raw.len() > 1, "{}", raw.len());
        assert!(raw.iter().any(|byte| *byte != 0));
        assert!(raw.iter().any(|byte| *byte != 1));
        let rendered = format!("{loaded:?}");
        assert!(rendered.contains("KeyPair"), "{rendered}");
    }

    let key = KeyPair::generate_for(&PKCS_ECDSA_P256_SHA256).unwrap();
    let pkcs1 = PrivateKeyDer::Pkcs1(rustls::pki_types::PrivatePkcs1KeyDer::from(vec![
        0x30, 0x00,
    ]));
    assert!(KeyPair::from_der_and_sign_algo(&pkcs1, key.algorithm()).is_err());
}

fn load(provider: &CryptoProvider, cert: &CertificateDer<'_>, key: &KeyPair) {
    let key = PrivateKeyDer::Pkcs8(key.serialize_der().into());
    CertifiedKey::from_der(vec![cert.clone().into_owned()], key, provider).unwrap();
}
