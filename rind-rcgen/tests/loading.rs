//! The key loaders that take PEM or an owned `Vec`, and the conversion back to
//! rustls's key type, load and refuse as rcgen's own do.

use rcgen::{PKCS_ECDSA_P256_SHA256, PKCS_ECDSA_P384_SHA384, PKCS_ED25519, SignatureAlgorithm};
use rind_rcgen::KeyPair;
use rustls::pki_types::{PrivateKeyDer, PrivatePkcs8KeyDer};

const ALGORITHMS: [&SignatureAlgorithm; 3] = [
    &PKCS_ECDSA_P256_SHA256,
    &PKCS_ECDSA_P384_SHA384,
    &PKCS_ED25519,
];

#[cfg(feature = "pem")]
#[test]
fn pem_keys_load_for_their_algorithm() {
    for alg in ALGORITHMS {
        let key = KeyPair::generate_for(alg).unwrap();
        let pem = key.serialize_pem();
        for loaded in [
            KeyPair::from_pkcs8_pem_and_sign_algo(&pem, alg),
            KeyPair::from_pem_and_sign_algo(&pem, alg),
        ] {
            let loaded = loaded.unwrap();
            assert_eq!(loaded.algorithm(), alg);
            assert_eq!(loaded.serialize_der(), key.serialize_der());
        }
        assert!(rcgen::KeyPair::from_pem_and_sign_algo(&pem, alg).is_ok());
    }
}

/// Malformed PEM gives rcgen's error.
#[cfg(feature = "pem")]
#[test]
fn malformed_pem_is_refused_as_rcgen_refuses_it() {
    let key = KeyPair::generate_for(&PKCS_ECDSA_P256_SHA256).unwrap();
    let pem = key.serialize_pem();
    // Malformed base64 is a PEM error on both, whose message rind words in
    // its own way.
    let bad_base64 = "-----BEGIN PRIVATE KEY-----\n!!!!\n-----END PRIVATE KEY-----\n";
    for alg in ALGORITHMS {
        for result in [
            KeyPair::from_pem_and_sign_algo(bad_base64, alg).err(),
            KeyPair::from_pkcs8_pem_and_sign_algo(bad_base64, alg).err(),
            rcgen::KeyPair::from_pem_and_sign_algo(bad_base64, alg).err(),
        ] {
            assert!(matches!(result, Some(rcgen::Error::PemError(_))));
        }
    }

    let cases = [
        "-----BEGIN PRIVATE KEY-----\nMAA=\n-----END PRIVATE KEY-----\n".to_string(),
        pem.replace("-----END PRIVATE KEY-----", ""),
    ];
    for pem in &cases {
        for alg in ALGORITHMS {
            assert_eq!(
                KeyPair::from_pem_and_sign_algo(pem, alg).err(),
                rcgen::KeyPair::from_pem_and_sign_algo(pem, alg).err(),
                "{pem}"
            );
            assert!(
                KeyPair::from_pkcs8_pem_and_sign_algo(pem, alg).is_err(),
                "{pem}"
            );
        }
    }
}

#[test]
fn owned_der_loads_and_converts_back() {
    for alg in ALGORITHMS {
        let key = KeyPair::generate_for(alg).unwrap();
        let der = key.serialize_der();
        let loaded = KeyPair::try_from(der.clone()).unwrap();
        assert_eq!(loaded.algorithm(), alg);
        assert_eq!(
            PrivateKeyDer::from(loaded),
            PrivateKeyDer::Pkcs8(PrivatePkcs8KeyDer::from(der))
        );
    }
    assert_eq!(
        KeyPair::try_from(vec![0x30, 0x00]).err(),
        rcgen::KeyPair::try_from(vec![0x30, 0x00]).err()
    );
}
