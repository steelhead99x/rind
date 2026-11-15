//! ML-DSA refusals checked against aws-lc-rs 1.19: the `KeyRejected` name,
//! and the inputs aws-lc-rs accepts that rind refuses.
//!
//! aws-lc-rs 1.19.0 names a parsed non-PQDSA key `WrongAlgorithm`
//! (`parse_rfc5208_private_key` in `aws-lc-rs/src/evp_pkey.rs`) and a parsed
//! ML-DSA key of another parameter set `Unspecified` (`validate_pqdsa_evp_key`
//! in `aws-lc-rs/src/pqdsa.rs`). A public key that is neither a
//! SubjectPublicKeyInfo nor this parameter set's raw encoding is
//! `Unspecified` (`parse_pqdsa_public_key`).

#![cfg(not(any(miri, target_family = "wasm")))]

use std::sync::OnceLock;

use aws_lc_rs as theirs;
use ours::encoding::AsDer as _;
use ours::signature::KeyPair as _;
use rind_aws_lc_rs as ours;
use theirs::encoding::AsDer as _;
use theirs::signature::KeyPair as _;

fn rsa_pkcs8() -> &'static [u8] {
    static PKCS8: OnceLock<Vec<u8>> = OnceLock::new();
    PKCS8.get_or_init(|| {
        let key = theirs::rsa::KeyPair::generate(theirs::rsa::KeySize::Rsa2048).unwrap();
        let der: theirs::encoding::Pkcs8V1Der = key.as_der().unwrap();
        der.as_ref().to_vec()
    })
}

/// PKCS#8 v1 whose algorithm is `oid`, with `parameters` appended to the
/// algorithm identifier when present, and `private_key` as the private key.
fn pkcs8_private_key(oid: &[u8], parameters: Option<&[u8]>, private_key: &[u8]) -> Vec<u8> {
    let mut algorithm = der(0x06, oid);
    if let Some(parameters) = parameters {
        algorithm.extend_from_slice(parameters);
    }
    der(
        0x30,
        &[
            der(0x02, &[0]),
            der(0x30, &algorithm),
            der(0x04, private_key),
        ]
        .concat(),
    )
}

/// A DER element tagged `tag` holding `contents`.
fn der(tag: u8, contents: &[u8]) -> Vec<u8> {
    let len = contents.len();
    let mut out = vec![tag];
    match len {
        0..=0x7f => out.push(len as u8),
        0x80..=0xff => out.extend([0x81, len as u8]),
        _ => out.extend([0x82, (len >> 8) as u8, len as u8]),
    }
    out.extend_from_slice(contents);
    out
}

fn same_rejection<T, U>(
    ours: Result<T, ours::error::KeyRejected>,
    theirs: Result<U, theirs::error::KeyRejected>,
) {
    match (ours, theirs) {
        (Err(ours), Err(theirs)) => assert_eq!(
            ours.description_(),
            theirs.description_(),
            "{ours} vs {theirs}"
        ),
        (ours, theirs) => panic!(
            "expected both to fail, got ok {} {}",
            ours.is_ok(),
            theirs.is_ok()
        ),
    }
}

/// The PKCS#8 header of a seed-form key: version and algorithm identifier.
fn ml_dsa_pkcs8_header(seed_form: &[u8]) -> &[u8] {
    &seed_form[2..2 + 3 + 13]
}

/// Length and algorithm mismatches aws-lc-rs names the same way.
#[test]
fn ml_dsa_rejected() {
    use theirs::encoding::AsRawBytes;

    let algs = [
        (
            &ours::signature::ML_DSA_44_SIGNING,
            &theirs::signature::ML_DSA_44_SIGNING,
            &ours::signature::ML_DSA_65_SIGNING,
            &theirs::signature::ML_DSA_65_SIGNING,
        ),
        (
            &ours::signature::ML_DSA_65_SIGNING,
            &theirs::signature::ML_DSA_65_SIGNING,
            &ours::signature::ML_DSA_87_SIGNING,
            &theirs::signature::ML_DSA_87_SIGNING,
        ),
        (
            &ours::signature::ML_DSA_87_SIGNING,
            &theirs::signature::ML_DSA_87_SIGNING,
            &ours::signature::ML_DSA_44_SIGNING,
            &theirs::signature::ML_DSA_44_SIGNING,
        ),
    ];
    for (ours_sign, theirs_sign, ours_other, theirs_other) in algs {
        same_rejection(
            ours::signature::PqdsaKeyPair::from_seed(ours_sign, &[0; 31]),
            theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[0; 31]),
        );
        same_rejection(
            ours::signature::PqdsaKeyPair::from_seed(ours_sign, &[0; 33]),
            theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[0; 33]),
        );
        same_rejection(
            ours::signature::PqdsaKeyPair::from_seed(ours_sign, &[]),
            theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[]),
        );
        same_rejection(
            ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, &[7; 32]),
            theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, &[7; 32]),
        );
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &[]),
            theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &[]),
        );

        let seed = [4u8; 32];
        let other = theirs::signature::PqdsaKeyPair::from_seed(theirs_other, &seed).unwrap();
        let raw = other.private_key().as_raw_bytes().unwrap();
        same_rejection(
            ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, raw.as_ref()),
            theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, raw.as_ref()),
        );
        let pkcs8 = other.to_pkcs8v1().unwrap();
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, pkcs8.as_ref()),
            theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, pkcs8.as_ref()),
        );
        // The other parameter set still loads its own key.
        assert!(ours::signature::PqdsaKeyPair::from_pkcs8(ours_other, pkcs8.as_ref()).is_ok());

        // A correctly sized expanded key whose parts no longer agree.
        let good = theirs::signature::PqdsaKeyPair::from_seed(theirs_sign, &[6; 32]).unwrap();
        let raw = good.private_key().as_raw_bytes().unwrap();
        let raw = raw.as_ref();
        let mut flipped_tr = raw.to_vec();
        flipped_tr[64] ^= 0x01;
        let mut zero_rho = raw.to_vec();
        zero_rho[..32].fill(0);
        // s1 starts after rho, K, and tr. s2 follows s1. 0xff is outside eta's range.
        let s1 = 128;
        let s2 = s1
            + match ours_sign.public_key_len() {
                1312 => 4 * 96,  // ML-DSA-44: L polynomials, eta 2
                1952 => 5 * 128, // ML-DSA-65: L polynomials, eta 4
                2592 => 7 * 96,  // ML-DSA-87: L polynomials, eta 2
                len => panic!("unexpected ML-DSA public key length {len}"),
            };
        let mut bad_s1 = raw.to_vec();
        bad_s1[s1] = 0xff;
        let mut bad_s2 = raw.to_vec();
        bad_s2[s2] = 0xff;
        for corrupted in [&flipped_tr, &zero_rho, &bad_s1, &bad_s2] {
            same_rejection(
                ours::signature::PqdsaKeyPair::from_raw_private_key(ours_sign, corrupted),
                theirs::signature::PqdsaKeyPair::from_raw_private_key(theirs_sign, corrupted),
            );
        }
    }

    let ed25519 = theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[3; 32]).unwrap();
    for doc in [ed25519.to_pkcs8v1().unwrap(), ed25519.to_pkcs8().unwrap()] {
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(
                &ours::signature::ML_DSA_65_SIGNING,
                doc.as_ref(),
            ),
            theirs::signature::PqdsaKeyPair::from_pkcs8(
                &theirs::signature::ML_DSA_65_SIGNING,
                doc.as_ref(),
            ),
        );
    }
    // v2 whose public key does not match. Both refuse it, so this is
    // InvalidEncoding rather than WrongAlgorithm.
    let mut mismatched = ed25519.to_pkcs8().unwrap().as_ref().to_vec();
    let last = mismatched.len() - 1;
    mismatched[last] ^= 0x01;
    same_rejection(
        ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_65_SIGNING, &mismatched),
        theirs::signature::PqdsaKeyPair::from_pkcs8(
            &theirs::signature::ML_DSA_65_SIGNING,
            &mismatched,
        ),
    );

    let as_ml_dsa = |pkcs8: &[u8]| {
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, pkcs8),
            theirs::signature::PqdsaKeyPair::from_pkcs8(
                &theirs::signature::ML_DSA_44_SIGNING,
                pkcs8,
            ),
        );
    };
    // RFC 8410 X25519. aws-lc-rs does not encode one, so this is that document.
    as_ml_dsa(&pkcs8_private_key(
        &[0x2b, 0x65, 0x6e],
        None,
        &der(0x04, &[0x11; 32]),
    ));
    let rng = theirs::rand::SystemRandom::new();
    for algorithm in [
        &theirs::signature::ECDSA_P256_SHA256_ASN1_SIGNING,
        &theirs::signature::ECDSA_P384_SHA384_ASN1_SIGNING,
        &theirs::signature::ECDSA_P521_SHA512_ASN1_SIGNING,
    ] {
        let doc = theirs::signature::EcdsaKeyPair::generate_pkcs8(algorithm, &rng).unwrap();
        as_ml_dsa(doc.as_ref());
    }
    as_ml_dsa(rsa_pkcs8());

    // secp256k1 parses in aws-lc-rs. rind has no parser for it, so the
    // refusal names differ; the README lists that. A key aws-lc-rs also
    // rejects still agrees.
    let scalar = [0u8; 31].into_iter().chain([1u8]).collect::<Vec<_>>();
    let public = [
        0x04, 0x79, 0xbe, 0x66, 0x7e, 0xf9, 0xdc, 0xbb, 0xac, 0x55, 0xa0, 0x62, 0x95, 0xce, 0x87,
        0x0b, 0x07, 0x02, 0x9b, 0xfc, 0xdb, 0x2d, 0xce, 0x28, 0xd9, 0x59, 0xf2, 0x81, 0x5b, 0x16,
        0xf8, 0x17, 0x98, 0x48, 0x3a, 0xda, 0x77, 0x26, 0xa3, 0xc4, 0x65, 0x5d, 0xa4, 0xfb, 0xfc,
        0x0e, 0x11, 0x08, 0xa8, 0xfd, 0x17, 0xb4, 0x48, 0xa6, 0x85, 0x54, 0x19, 0x9c, 0x47, 0xd0,
        0x8f, 0xfb, 0x10, 0xd4, 0xb8,
    ];
    let secp256k1 = |scalar: &[u8], public: Option<&[u8]>| {
        let mut ec = [der(0x02, &[1]), der(0x04, scalar)].concat();
        if let Some(public) = public {
            ec.extend(der(0xa1, &der(0x03, &[&[0], public].concat())));
        }
        pkcs8_private_key(
            &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01],
            Some(&der(0x06, &[0x2b, 0x81, 0x04, 0x00, 0x0a])),
            &der(0x30, &ec),
        )
    };
    for pkcs8 in [secp256k1(&scalar, Some(&public)), secp256k1(&scalar, None)] {
        let ours =
            ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, &pkcs8)
                .unwrap_err();
        let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(
            &theirs::signature::ML_DSA_44_SIGNING,
            &pkcs8,
        )
        .unwrap_err();
        assert_eq!(ours.description_(), "InvalidEncoding");
        assert_eq!(theirs.description_(), "WrongAlgorithm");
    }
    as_ml_dsa(&secp256k1(&[0; 32], Some(&public)));
    let mut bad_public = public;
    bad_public[10] ^= 1;
    as_ml_dsa(&secp256k1(&scalar, Some(&bad_public)));

    // aws-lc parses these. rind has no implementation, so the names differ
    // and the README lists each one.
    let differs = |pkcs8: &[u8]| {
        let ours =
            ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, pkcs8)
                .unwrap_err();
        let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(
            &theirs::signature::ML_DSA_44_SIGNING,
            pkcs8,
        )
        .unwrap_err();
        assert_eq!(ours.description_(), "InvalidEncoding");
        assert_eq!(theirs.description_(), "WrongAlgorithm");
    };
    let ec_on = |curve: &[u8], scalar: &[u8]| {
        let ec = der(0x30, &[der(0x02, &[1]), der(0x04, scalar)].concat());
        pkcs8_private_key(
            &[0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01],
            Some(&der(0x06, curve)),
            &ec,
        )
    };
    let mut p224 = vec![0u8; 28];
    p224[27] = 1;
    differs(&ec_on(&[0x2b, 0x81, 0x04, 0x00, 0x21], &p224));
    as_ml_dsa(&ec_on(&[0x2b, 0x81, 0x04, 0x00, 0x21], &[0; 28]));
    let mut brainpool = vec![0u8; 32];
    brainpool[31] = 1;
    differs(&ec_on(
        &[0x2b, 0x24, 0x03, 0x03, 0x02, 0x08, 0x01, 0x01, 0x07],
        &brainpool,
    ));
    let k1 = theirs::signature::EcdsaKeyPair::generate_pkcs8(
        &theirs::signature::ECDSA_P256K1_SHA256_ASN1_SIGNING,
        &rng,
    )
    .unwrap();
    differs(k1.as_ref());

    let (_, body, _) = der_split(rsa_pkcs8()).unwrap();
    let (_, _, body) = der_split(body).unwrap();
    let (_, _, body) = der_split(body).unwrap();
    let (_, pkcs1, _) = der_split(body).unwrap();
    let rsa_as = |oid: &[u8], parameters: Option<&[u8]>| pkcs8_private_key(oid, parameters, pkcs1);
    let pss = [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0a];
    as_ml_dsa(&rsa_as(&pss, None));
    as_ml_dsa(&rsa_as(&pss, Some(&[0x30, 0x00])));
    as_ml_dsa(&rsa_as(&pss, Some(&[0x05, 0x00])));
    as_ml_dsa(&rsa_as(
        &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x07],
        Some(&[0x05, 0x00]),
    ));
    as_ml_dsa(&rsa_as(&[0x55, 0x08, 0x01, 0x01], Some(&[0x05, 0x00])));
    let sha256 = der(
        0x30,
        &[
            der(
                0x06,
                &[0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01],
            ),
            vec![0x05, 0x00],
        ]
        .concat(),
    );
    differs(&rsa_as(&pss, Some(&der(0x30, &der(0xa0, &sha256)))));

    let kem512 = [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x01];
    let seed = der(0x80, &[0x5a; 64]);
    for oid in [
        kem512,
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x02],
        [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x04, 0x03],
    ] {
        as_ml_dsa(&pkcs8_private_key(&oid, None, &seed));
    }
    as_ml_dsa(&pkcs8_private_key(&kem512, None, &der(0x80, &[0x5a; 63])));
    as_ml_dsa(&pkcs8_private_key(&kem512, Some(&[0x05, 0x00]), &seed));
    as_ml_dsa(&pkcs8_private_key(
        &kem512,
        None,
        &der(0x04, &vec![0x11; 1632]),
    ));
    as_ml_dsa(&pkcs8_private_key(
        &kem512,
        None,
        &der(0x04, &vec![0x11; 1631]),
    ));

    let q = der_uint(
        &[0x80]
            .into_iter()
            .chain([0u8; 18])
            .chain([1])
            .collect::<Vec<_>>(),
    );
    let p = der_uint(
        &[0x01]
            .into_iter()
            .chain([0u8; 19])
            .chain([1])
            .collect::<Vec<_>>(),
    );
    let dsa = [0x2a, 0x86, 0x48, 0xce, 0x38, 0x04, 0x01];
    let params = der(0x30, &[p, q, der_uint(&[2])].concat());
    differs(&pkcs8_private_key(&dsa, Some(&params), &der_uint(&[1])));
    let tiny = der(
        0x30,
        &[
            der_uint(
                &[0x01]
                    .into_iter()
                    .chain([0u8; 19])
                    .chain([1])
                    .collect::<Vec<_>>(),
            ),
            der_uint(&[3]),
            der_uint(&[2]),
        ]
        .concat(),
    );
    as_ml_dsa(&pkcs8_private_key(&dsa, Some(&tiny), &der_uint(&[1])));
    as_ml_dsa(&pkcs8_private_key(
        &[0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x03, 0x01],
        Some(&params),
        &der_uint(&[1]),
    ));
}

/// Public keys aws-lc-rs refuses, with the same `KeyRejected` name.
#[test]
fn ml_dsa_hostile_keys() {
    let ours_key =
        ours::signature::PqdsaKeyPair::from_seed(&ours::signature::ML_DSA_44_SIGNING, &[5; 32])
            .unwrap();
    let theirs_key =
        theirs::signature::PqdsaKeyPair::from_seed(&theirs::signature::ML_DSA_44_SIGNING, &[5; 32])
            .unwrap();
    assert_eq!(
        ours_key.public_key().as_ref(),
        theirs_key.public_key().as_ref()
    );
    let pk = theirs_key.public_key().as_ref().to_vec();
    let other =
        theirs::signature::PqdsaKeyPair::from_seed(&theirs::signature::ML_DSA_65_SIGNING, &[5; 32])
            .unwrap()
            .public_key()
            .as_ref()
            .to_vec();
    let truncated = pk[..pk.len() - 1].to_vec();
    let mut longer = pk.clone();
    longer.push(0);
    let mut wrong_oid = theirs_key.public_key().as_der().unwrap().as_ref().to_vec();
    let id44 = [
        0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x11,
    ];
    let id65 = [
        0x30, 0x0b, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03, 0x12,
    ];
    let at = wrong_oid
        .windows(id44.len())
        .position(|window| window == id44)
        .unwrap();
    wrong_oid[at..at + id44.len()].copy_from_slice(&id65);
    let ed25519 = theirs::signature::Ed25519KeyPair::from_seed_unchecked(&[3; 32])
        .unwrap()
        .public_key()
        .as_der()
        .unwrap();
    for (name, key) in [
        ("truncated", truncated.as_slice()),
        ("longer", longer.as_slice()),
        ("empty", &[][..]),
        ("wrong_oid", wrong_oid.as_slice()),
        ("ed25519", ed25519.as_ref()),
        ("other_raw", other.as_slice()),
    ] {
        let ours = ours::signature::ParsedPublicKey::new(&ours::signature::ML_DSA_44, key);
        let theirs = theirs::signature::ParsedPublicKey::new(&theirs::signature::ML_DSA_44, key);
        match (&ours, &theirs) {
            (Err(ours), Err(theirs)) if ours.description_() == theirs.description_() => {}
            _ => panic!(
                "{name} len {} ours {} ({}) theirs {} ({})",
                key.len(),
                ours.as_ref()
                    .err()
                    .map(|e| e.description_())
                    .unwrap_or("ok"),
                ours.as_ref()
                    .err()
                    .map(|e| e.to_string())
                    .unwrap_or_default(),
                theirs
                    .as_ref()
                    .err()
                    .map(|e| e.description_())
                    .unwrap_or("ok"),
                theirs
                    .as_ref()
                    .err()
                    .map(|e| e.to_string())
                    .unwrap_or_default(),
            ),
        }
        same_rejection(ours, theirs);
        same_rejection(
            ours::signature::UnparsedPublicKey::new(&ours::signature::ML_DSA_44, key).parse(),
            theirs::signature::UnparsedPublicKey::new(&theirs::signature::ML_DSA_44, key).parse(),
        );
    }
}

/// Generated keys, and malformed or mismatched inputs, against aws-lc-rs:
/// wrong-length public keys, SPKIs, and signatures, another parameter set's
/// keys and signatures, and a PKCS#8 v2 whose public key does not match.
///
/// Two refusals are rind's own, as the README lists: an SPKI or a PKCS#8
/// document with a byte after it, and a PKCS#8 v2 key whose public key does
/// not match, all of which aws-lc-rs accepts.
#[test]
fn ml_dsa_malformed() {
    use theirs::encoding::AsDer as _;

    let sets = [
        (
            &ours::signature::ML_DSA_44_SIGNING,
            &ours::signature::ML_DSA_44,
            &theirs::signature::ML_DSA_44_SIGNING,
            &theirs::signature::ML_DSA_44,
        ),
        (
            &ours::signature::ML_DSA_65_SIGNING,
            &ours::signature::ML_DSA_65,
            &theirs::signature::ML_DSA_65_SIGNING,
            &theirs::signature::ML_DSA_65,
        ),
        (
            &ours::signature::ML_DSA_87_SIGNING,
            &ours::signature::ML_DSA_87,
            &theirs::signature::ML_DSA_87_SIGNING,
            &theirs::signature::ML_DSA_87,
        ),
    ];
    let msg = b"malformed";

    // Each set's generated key pair, its raw public key, SPKI, signature,
    // and seed-form PKCS#8, from both sides.
    let keys: Vec<_> = sets
        .iter()
        .map(|&(ours_sign, _, theirs_sign, _)| {
            let ours = ours::signature::PqdsaKeyPair::generate(ours_sign).unwrap();
            let theirs = theirs::signature::PqdsaKeyPair::generate(theirs_sign).unwrap();
            assert_eq!(ours.public_key().as_ref().len(), ours_sign.public_key_len());
            assert_eq!(
                theirs.public_key().as_ref().len(),
                theirs_sign.public_key_len()
            );
            assert_ne!(ours.public_key().as_ref(), theirs.public_key().as_ref());

            // Each side's generated key loads on the other, with the same
            // public key.
            let ours_pkcs8 = ours.to_pkcs8v1().unwrap();
            let theirs_pkcs8 = theirs.to_pkcs8v1().unwrap();
            let loaded =
                theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, ours_pkcs8.as_ref())
                    .unwrap();
            assert_eq!(loaded.public_key().as_ref(), ours.public_key().as_ref());
            let loaded =
                ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, theirs_pkcs8.as_ref())
                    .unwrap();
            assert_eq!(loaded.public_key().as_ref(), theirs.public_key().as_ref());

            let mut sig = vec![0; ours_sign.signature_len()];
            assert_eq!(ours.sign(msg, &mut sig).unwrap(), sig.len());
            // A short output buffer is refused on both sides.
            let mut short = vec![0; ours_sign.signature_len() - 1];
            assert!(ours.sign(msg, &mut short).is_err());
            assert!(theirs.sign(msg, &mut short).is_err());

            let public = ours.public_key().as_ref().to_vec();
            let spki = ours.public_key().as_der().unwrap().as_ref().to_vec();
            let theirs_spki = theirs.public_key().as_der().unwrap().as_ref().to_vec();
            assert_eq!(
                ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, theirs_pkcs8.as_ref())
                    .unwrap()
                    .public_key()
                    .as_der()
                    .unwrap()
                    .as_ref(),
                &theirs_spki[..]
            );
            (public, spki, sig, theirs_pkcs8.as_ref().to_vec(), theirs)
        })
        .collect();

    for (i, &(ours_sign, ours_verify, theirs_sign, theirs_verify)) in sets.iter().enumerate() {
        let (public, spki, sig, _, _) = &keys[i];
        let verifies = |key: &[u8], sig: &[u8]| {
            let ours = ours::signature::UnparsedPublicKey::new(ours_verify, key).verify(msg, sig);
            let theirs =
                theirs::signature::UnparsedPublicKey::new(theirs_verify, key).verify(msg, sig);
            (ours.is_ok(), theirs.is_ok())
        };
        let agree = |key: &[u8], sig: &[u8]| {
            let (ours, theirs) = verifies(key, sig);
            assert_eq!(ours, theirs, "key {} sig {}", key.len(), sig.len());
            ours
        };

        assert!(agree(public, sig));
        assert!(agree(spki, sig));

        // Public keys and SPKIs a byte short, a raw key a byte long, or an
        // empty key.
        for key in [public, spki] {
            assert!(!agree(&key[..key.len() - 1], sig));
        }
        assert!(!agree(&[public, &[0][..]].concat(), sig));
        assert!(!agree(&[], sig));
        // aws-lc-rs ignores a byte after the SPKI; rind refuses it.
        assert_eq!(verifies(&[spki, &[0][..]].concat(), sig), (false, true));

        // Signatures a byte short or long, or empty.
        assert!(!agree(public, &sig[..sig.len() - 1]));
        assert!(!agree(public, &[&sig[..], &[0]].concat()));
        assert!(!agree(public, &[]));

        // Another parameter set's public key, SPKI, and signature.
        for (j, (other_public, other_spki, other_sig, other_pkcs8, other_key)) in
            keys.iter().enumerate()
        {
            if j == i {
                continue;
            }
            assert!(!agree(other_public, sig));
            assert!(!agree(other_spki, sig));
            assert!(!agree(public, other_sig));
            assert!(!agree(other_public, other_sig));
            assert!(!agree(other_spki, other_sig));

            // PKCS#8 v2: the key with its own public key loads on both.
            let (_, _, _, own_pkcs8, own_key) = &keys[i];
            let v2 = ml_dsa_pkcs8_v2(own_pkcs8, own_key.public_key().as_ref());
            let ours = ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &v2).unwrap();
            let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &v2).unwrap();
            assert_eq!(ours.public_key().as_ref(), theirs.public_key().as_ref());
            assert_eq!(ours.public_key().as_ref(), own_key.public_key().as_ref());

            // With another key's public key, aws-lc-rs ignores it and loads
            // the private key; rind refuses the mismatch.
            let v2 = ml_dsa_pkcs8_v2(own_pkcs8, other_key.public_key().as_ref());
            let ours = ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &v2).unwrap_err();
            assert_eq!(ours.description_(), "InvalidEncoding");
            assert_eq!(ours.to_string(), "mismatched PKCS#8 public key");
            assert!(theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &v2).is_ok());

            // Another parameter set's key, with its own public key, is
            // refused on both, as in seed form.
            let v2 = ml_dsa_pkcs8_v2(other_pkcs8, other_key.public_key().as_ref());
            same_rejection(
                ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, &v2),
                theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, &v2),
            );

            // Another parameter set's PKCS#8 whose seed is a byte short, and
            // one cut off inside its header, are refused for the same reason.
            let short = ml_dsa_short_seed(other_pkcs8);
            for pkcs8 in [&short[..], &other_pkcs8[..10]] {
                same_rejection(
                    ours::signature::PqdsaKeyPair::from_pkcs8(ours_sign, pkcs8),
                    theirs::signature::PqdsaKeyPair::from_pkcs8(theirs_sign, pkcs8),
                );
            }
        }
    }

    // An Ed25519 OID whose key is one byte short, an unknown OID, and a
    // truncated ML-DSA OID. aws-lc-rs has not parsed a key, so these are
    // `InvalidEncoding`, not `WrongAlgorithm`.
    let oid_key = |oid: &[u8], private_key: &[u8]| {
        der(
            0x30,
            &[
                der(0x02, &[0]),
                der(0x30, &der(0x06, oid)),
                der(0x04, private_key),
            ]
            .concat(),
        )
    };
    let ed25519_oid = [0x2b, 0x65, 0x70];
    let mldsa_oid_prefix = [0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x03];
    for pkcs8 in [
        oid_key(&ed25519_oid, &der(0x04, &[0; 31])),
        oid_key(
            &[&mldsa_oid_prefix[..], &[0x7f]].concat(),
            &der(0x04, &[0; 32]),
        ),
        oid_key(&mldsa_oid_prefix, &der(0x04, &[0; 32])),
    ] {
        same_rejection(
            ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, &pkcs8),
            theirs::signature::PqdsaKeyPair::from_pkcs8(
                &theirs::signature::ML_DSA_44_SIGNING,
                &pkcs8,
            ),
        );
    }

    // A byte after a complete document. aws-lc-rs ignores it.
    let (_, _, _, pkcs8_44, _) = &keys[0];
    let trailed = [pkcs8_44.as_slice(), &[0]].concat();
    assert_eq!(
        (
            ours::signature::PqdsaKeyPair::from_pkcs8(
                &ours::signature::ML_DSA_44_SIGNING,
                &trailed
            )
            .is_ok(),
            theirs::signature::PqdsaKeyPair::from_pkcs8(
                &theirs::signature::ML_DSA_44_SIGNING,
                &trailed
            )
            .is_ok(),
        ),
        (false, true)
    );
    // The same trailing byte on ML-DSA-65, loaded as ML-DSA-44. aws-lc-rs
    // still parses the key and then refuses the size. rind refuses the
    // trailing byte first.
    let (_, _, _, pkcs8_65, _) = &keys[1];
    let trailed = [pkcs8_65.as_slice(), &[0]].concat();
    let ours =
        ours::signature::PqdsaKeyPair::from_pkcs8(&ours::signature::ML_DSA_44_SIGNING, &trailed)
            .unwrap_err();
    let theirs = theirs::signature::PqdsaKeyPair::from_pkcs8(
        &theirs::signature::ML_DSA_44_SIGNING,
        &trailed,
    )
    .unwrap_err();
    assert_eq!(ours.description_(), "InvalidEncoding");
    assert_eq!(theirs.description_(), "Unspecified");
}

/// A seed-form PKCS#8 v1 document with its 32-byte seed cut to 31.
fn ml_dsa_short_seed(seed_form: &[u8]) -> Vec<u8> {
    let header = ml_dsa_pkcs8_header(seed_form);
    let seed = &seed_form[seed_form.len() - 32..];
    let choice = der(0x80, &seed[..31]);
    der(0x30, &[header, &der(0x04, &choice)].concat())
}

/// A positive INTEGER whose magnitude is `mag`.
fn der_uint(mag: &[u8]) -> Vec<u8> {
    let body = if mag.first().is_some_and(|b| *b >= 0x80) {
        [&[0u8][..], mag].concat()
    } else {
        mag.to_vec()
    };
    der(0x02, &body)
}

fn der_split(input: &[u8]) -> Option<(u8, &[u8], &[u8])> {
    let (len, header) = match *input.get(1)? {
        n @ 0..=0x7f => (usize::from(n), 2),
        0x81 => (usize::from(*input.get(2)?), 3),
        0x82 => (
            usize::from(u16::from_be_bytes([*input.get(2)?, *input.get(3)?])),
            4,
        ),
        _ => return None,
    };
    let rest = input.get(header..)?;
    let (body, rest) = rest.split_at_checked(len)?;
    Some((input[0], body, rest))
}

/// A seed-form PKCS#8 v1 document rewritten as v2 (RFC 5958) carrying
/// `public_key`.
fn ml_dsa_pkcs8_v2(seed_form: &[u8], public_key: &[u8]) -> Vec<u8> {
    // The v1 body after its version: the algorithm identifier and the
    // private key.
    let rest = &seed_form[2 + 3..];
    let public_key = der(0x81, &[&[0][..], public_key].concat());
    der(0x30, &[&[0x02, 0x01, 0x01][..], rest, &public_key].concat())
}
