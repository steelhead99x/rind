// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Signatures through the module agree with rind's, which its own tests
//! check against Wycheproof and aws-lc-rs: keys, encodings, and signatures
//! cross between the two, deterministic signatures match byte for byte, and
//! malformed input fails with the same error. The module refuses the RSA
//! moduli FIPS 186-5 does not approve, which rind takes.
#![cfg(rind_fips_module)]

use rind::signature as theirs;
use rind_fips::rsa::{KeySize, PublicKeyComponents};
use rind_fips::signature::sign::{MlDsa44, MlDsa65, MlDsa87, MlDsaKeyPair, MlDsaParameterSet};
use rind_fips::signature::{
    EcdsaKeyPair, EcdsaSigningAlgorithm, Ed25519KeyPair, PublicKey, RsaKeyPair,
    RsaSigningAlgorithm, VerificationAlgorithm, sign, verify,
};
use rind_fips::{Error, digest};

const MESSAGE: &[u8] = b"rind-fips differential test";

const P256: &[u8] = include_bytes!("../../rind/src/high/ecdsa/secp256r1.pkcs8.der");
const P384: &[u8] = include_bytes!("../../rind/src/high/ecdsa/secp384r1.pkcs8.der");
const P521: &[u8] = include_bytes!("../../rind/src/high/ecdsa/secp521r1.pkcs8.der");
const RSA2048: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2048.pkcs8.der");
const RSA2048_PKCS1: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2048.der");
const RSA2049: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2049.pkcs8.der");
const RSA2050: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2050.pkcs8.der");
const RSA2047_PUBLIC: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa2047.pub.der");
const RSA3072: &[u8] = include_bytes!("../../rind/src/high/rsa/rsa3072.pkcs8.der");

/// Both calls failed alike, or both succeeded.
#[track_caller]
fn same_error<A, B>(ours: &Result<A, Error>, theirs: &Result<B, rind::Error>) {
    assert_eq!(
        ours.as_ref().err().map(ToString::to_string),
        theirs.as_ref().err().map(ToString::to_string)
    );
}

/// The `Debug` of `ours` is `theirs`', plain and pretty.
#[track_caller]
fn same_debug(ours: &impl core::fmt::Debug, theirs: &impl core::fmt::Debug) {
    assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));
    assert_eq!(format!("{ours:#?}"), format!("{theirs:#?}"));
}

/// Our digest of `message` with `ours`, and rind's with `theirs`.
fn digests(
    ours: &'static digest::Algorithm,
    theirs: &'static rind::digest::Algorithm,
    message: &[u8],
) -> (digest::Digest, rind::digest::Digest) {
    (
        digest::digest(ours, message),
        rind::digest::digest(theirs, message),
    )
}

/// A verify algorithm, rind's, and a public key and a signature over
/// [`MESSAGE`] that rind made for it.
struct VerifyCase {
    ours: &'static VerificationAlgorithm,
    theirs: &'static theirs::VerificationAlgorithm,
    public_key: Vec<u8>,
    signature: Vec<u8>,
}

fn ecdsa_case(
    ours: &'static VerificationAlgorithm,
    theirs: &'static theirs::VerificationAlgorithm,
    signer: &'static theirs::EcdsaSigningAlgorithm,
    pkcs8: &[u8],
    hash: &'static rind::digest::Algorithm,
) -> VerifyCase {
    let key = theirs::EcdsaKeyPair::from_pkcs8(signer, pkcs8).unwrap();
    let digest = rind::digest::digest(hash, MESSAGE);
    VerifyCase {
        ours,
        theirs,
        public_key: key.public_key().as_ref().to_vec(),
        signature: key.sign_digest(&digest).unwrap().as_ref().to_vec(),
    }
}

fn rsa_case(
    ours: &'static impl AsRef<VerificationAlgorithm>,
    theirs: &'static theirs::RsaVerificationAlgorithm,
    signer: &'static theirs::RsaSigningAlgorithm,
    pkcs8: &[u8],
) -> VerifyCase {
    let key = theirs::RsaKeyPair::from_pkcs8(pkcs8).unwrap();
    VerifyCase {
        ours: ours.as_ref(),
        theirs: theirs.as_ref(),
        public_key: key.public_key(signer).as_ref().to_vec(),
        signature: key.sign(signer, MESSAGE).unwrap().as_ref().to_vec(),
    }
}

/// An RSASSA-PKCS1-v1_5 signature with SHA-1 over [`MESSAGE`], which rind
/// signs only as a raw RSA operation: a blind signature over the encoded
/// message.
fn rsa_sha1_case(
    ours: &'static impl AsRef<VerificationAlgorithm>,
    theirs: &'static theirs::RsaVerificationAlgorithm,
) -> VerifyCase {
    let key = rind::blind_rsa::KeyPair::from_pkcs8(
        &rind::blind_rsa::RSABSSA_SHA384_PSS_RANDOMIZED,
        RSA2048,
    )
    .unwrap();
    let digest = rind::digest::digest(&rind::digest::legacy::SHA1, MESSAGE);
    let info: &[u8] = &[
        0x30, 0x21, 0x30, 0x09, 0x06, 0x05, 0x2b, 0x0e, 0x03, 0x02, 0x1a, 0x05, 0x00, 0x04, 0x14,
    ];
    let mut encoded = vec![0xff; 256];
    encoded[..2].copy_from_slice(&[0x00, 0x01]);
    let at = 256 - info.len() - digest.as_ref().len();
    encoded[at - 1] = 0;
    encoded[at..at + info.len()].copy_from_slice(info);
    encoded[at + info.len()..].copy_from_slice(digest.as_ref());
    let rsa = theirs::RsaKeyPair::from_pkcs8(RSA2048).unwrap();
    VerifyCase {
        ours: ours.as_ref(),
        theirs: theirs.as_ref(),
        public_key: rsa
            .public_key(&theirs::sign::RSA_PKCS1_SHA256)
            .as_ref()
            .to_vec(),
        signature: key.blind_sign(&encoded).unwrap().as_ref().to_vec(),
    }
}

fn ed25519_case() -> VerifyCase {
    let key = theirs::Ed25519KeyPair::from_seed(&[9; 32]).unwrap();
    VerifyCase {
        ours: &verify::ED25519,
        theirs: &theirs::verify::ED25519,
        public_key: key.public_key().as_ref().to_vec(),
        signature: key.sign(MESSAGE).as_ref().to_vec(),
    }
}

fn ml_dsa_case<P: theirs::sign::MlDsaParameterSet>(
    ours: &'static VerificationAlgorithm,
    theirs: &'static theirs::VerificationAlgorithm,
) -> VerifyCase {
    let key = theirs::sign::MlDsaKeyPair::<P>::from_seed(&[5; 32]).unwrap();
    VerifyCase {
        ours,
        theirs,
        public_key: key.public_key().as_ref().to_vec(),
        signature: key.sign(MESSAGE).unwrap().as_ref().to_vec(),
    }
}

/// A case for every verify algorithm.
fn verify_cases() -> Vec<VerifyCase> {
    use rind::digest::{SHA256, SHA384, SHA512};
    let p256 = &theirs::sign::ECDSA_P256_SHA256_ASN1;
    let p384 = &theirs::sign::ECDSA_P384_SHA384_ASN1;
    let p521 = &theirs::sign::ECDSA_P521_SHA512_ASN1;
    vec![
        ecdsa_case(
            &verify::ECDSA_P256_SHA256_ASN1,
            &theirs::verify::ECDSA_P256_SHA256_ASN1,
            p256,
            P256,
            &SHA256,
        ),
        ecdsa_case(
            &verify::ECDSA_P256_SHA384_ASN1,
            &theirs::verify::ECDSA_P256_SHA384_ASN1,
            p256,
            P256,
            &SHA384,
        ),
        ecdsa_case(
            &verify::ECDSA_P256_SHA512_ASN1,
            &theirs::verify::ECDSA_P256_SHA512_ASN1,
            p256,
            P256,
            &SHA512,
        ),
        ecdsa_case(
            &verify::ECDSA_P384_SHA256_ASN1,
            &theirs::verify::ECDSA_P384_SHA256_ASN1,
            p384,
            P384,
            &SHA256,
        ),
        ecdsa_case(
            &verify::ECDSA_P384_SHA384_ASN1,
            &theirs::verify::ECDSA_P384_SHA384_ASN1,
            p384,
            P384,
            &SHA384,
        ),
        ecdsa_case(
            &verify::ECDSA_P384_SHA512_ASN1,
            &theirs::verify::ECDSA_P384_SHA512_ASN1,
            p384,
            P384,
            &SHA512,
        ),
        ecdsa_case(
            &verify::ECDSA_P521_SHA256_ASN1,
            &theirs::verify::ECDSA_P521_SHA256_ASN1,
            p521,
            P521,
            &SHA256,
        ),
        ecdsa_case(
            &verify::ECDSA_P521_SHA384_ASN1,
            &theirs::verify::ECDSA_P521_SHA384_ASN1,
            p521,
            P521,
            &SHA384,
        ),
        ecdsa_case(
            &verify::ECDSA_P521_SHA512_ASN1,
            &theirs::verify::ECDSA_P521_SHA512_ASN1,
            p521,
            P521,
            &SHA512,
        ),
        ecdsa_case(
            &verify::ECDSA_P256_SHA256_FIXED,
            &theirs::verify::ECDSA_P256_SHA256_FIXED,
            &theirs::sign::ECDSA_P256_SHA256_FIXED,
            P256,
            &SHA256,
        ),
        ecdsa_case(
            &verify::ECDSA_P384_SHA384_FIXED,
            &theirs::verify::ECDSA_P384_SHA384_FIXED,
            &theirs::sign::ECDSA_P384_SHA384_FIXED,
            P384,
            &SHA384,
        ),
        ecdsa_case(
            &verify::ECDSA_P521_SHA512_FIXED,
            &theirs::verify::ECDSA_P521_SHA512_FIXED,
            &theirs::sign::ECDSA_P521_SHA512_FIXED,
            P521,
            &SHA512,
        ),
        rsa_case(
            &verify::RSA_PKCS1_SHA256,
            &theirs::verify::RSA_PKCS1_SHA256,
            &theirs::sign::RSA_PKCS1_SHA256,
            RSA2048,
        ),
        rsa_case(
            &verify::RSA_PKCS1_SHA384,
            &theirs::verify::RSA_PKCS1_SHA384,
            &theirs::sign::RSA_PKCS1_SHA384,
            RSA2048,
        ),
        rsa_case(
            &verify::RSA_PKCS1_SHA512,
            &theirs::verify::RSA_PKCS1_SHA512,
            &theirs::sign::RSA_PKCS1_SHA512,
            RSA2048,
        ),
        rsa_case(
            &verify::RSA_PSS_SHA256,
            &theirs::verify::RSA_PSS_SHA256,
            &theirs::sign::RSA_PSS_SHA256,
            RSA2048,
        ),
        rsa_case(
            &verify::RSA_PSS_SHA384,
            &theirs::verify::RSA_PSS_SHA384,
            &theirs::sign::RSA_PSS_SHA384,
            RSA2048,
        ),
        rsa_case(
            &verify::RSA_PSS_SHA512,
            &theirs::verify::RSA_PSS_SHA512,
            &theirs::sign::RSA_PSS_SHA512,
            RSA2048,
        ),
        ed25519_case(),
        ml_dsa_case::<theirs::sign::MlDsa44>(&verify::ML_DSA_44, &theirs::verify::ML_DSA_44),
        ml_dsa_case::<theirs::sign::MlDsa65>(&verify::ML_DSA_65, &theirs::verify::ML_DSA_65),
        ml_dsa_case::<theirs::sign::MlDsa87>(&verify::ML_DSA_87, &theirs::verify::ML_DSA_87),
        rsa_sha1_case(
            &verify::legacy::RSA_PKCS1_SHA1,
            &theirs::verify::legacy::RSA_PKCS1_SHA1,
        ),
        rsa_sha1_case(
            &verify::legacy::RSA_PKCS1_1024_SHA1,
            &theirs::verify::legacy::RSA_PKCS1_1024_SHA1,
        ),
        rsa_case(
            &verify::legacy::RSA_PKCS1_1024_SHA256,
            &theirs::verify::legacy::RSA_PKCS1_1024_SHA256,
            &theirs::sign::RSA_PKCS1_SHA256,
            RSA2048,
        ),
        rsa_case(
            &verify::legacy::RSA_PKCS1_1024_SHA512,
            &theirs::verify::legacy::RSA_PKCS1_1024_SHA512,
            &theirs::sign::RSA_PKCS1_SHA512,
            RSA2048,
        ),
        rsa_case(
            &verify::legacy::RSA_PKCS1_3072_SHA384,
            &theirs::verify::legacy::RSA_PKCS1_3072_SHA384,
            &theirs::sign::RSA_PKCS1_SHA384,
            RSA3072,
        ),
    ]
}

#[test]
fn every_verify_algorithm_verifies_as_rind_does() {
    for case in verify_cases() {
        same_debug(case.ours, case.theirs);
        let reference = theirs::PublicKey::new(case.theirs, &case.public_key).unwrap();
        reference.verify(MESSAGE, &case.signature).unwrap();

        let key = PublicKey::new(case.ours, &case.public_key).unwrap();
        assert_eq!(key.as_ref(), reference.as_ref(), "{:?}", case.ours);
        same_debug(&key, &reference);
        key.verify(MESSAGE, &case.signature).unwrap();

        let spki = reference.to_spki();
        assert_eq!(key.to_spki().as_ref(), spki.as_ref());
        let from_spki = PublicKey::from_spki(case.ours, spki.as_ref()).unwrap();
        from_spki.verify(MESSAGE, &case.signature).unwrap();
        same_error(
            &PublicKey::from_spki(case.ours, &spki.as_ref()[1..]),
            &theirs::PublicKey::from_spki(case.theirs, &spki.as_ref()[1..]),
        );

        // A changed message or signature, a truncated one, and an empty one.
        let mut flipped = case.signature.clone();
        flipped[case.signature.len() / 2] ^= 1;
        let truncated = &case.signature[..case.signature.len() - 1];
        for signature in [&flipped[..], truncated, &[]] {
            same_error(
                &key.verify(MESSAGE, signature),
                &reference.verify(MESSAGE, signature),
            );
        }
        same_error(
            &key.verify(b"another", &case.signature),
            &reference.verify(b"another", &case.signature),
        );

        // Malformed keys.
        for bad in [
            &case.public_key[1..],
            &case.public_key[..case.public_key.len() - 1],
            &[],
        ] {
            same_error(
                &PublicKey::new(case.ours, bad),
                &theirs::PublicKey::new(case.theirs, bad),
            );
        }
    }
}

#[test]
fn ecdsa_verify_digest_matches_rind() {
    let reference =
        theirs::EcdsaKeyPair::from_pkcs8(&theirs::sign::ECDSA_P384_SHA384_ASN1, P384).unwrap();
    let key = PublicKey::new(
        &verify::ECDSA_P384_SHA384_ASN1,
        reference.public_key().as_ref(),
    )
    .unwrap();
    let pairs = [
        (&digest::SHA256, &rind::digest::SHA256),
        (&digest::SHA384, &rind::digest::SHA384),
        (&digest::SHA512, &rind::digest::SHA512),
        (&digest::SHA512_256, &rind::digest::SHA512_256),
        (&digest::SHA3_256, &rind::digest::SHA3_256),
    ];
    for (ours, theirs) in pairs {
        let (our_digest, their_digest) = digests(ours, theirs, MESSAGE);
        let signature = reference.sign_digest(&their_digest);
        let public = reference.public_key();
        match signature {
            Ok(signature) => {
                key.verify_digest(&our_digest, signature.as_ref()).unwrap();
                public
                    .verify_digest(&their_digest, signature.as_ref())
                    .unwrap();
            }
            Err(error) => {
                assert_eq!(error, rind::Error::Unsupported);
                same_error(
                    &key.verify_digest(&our_digest, &[0; 104]),
                    &public.verify_digest(&their_digest, &[0; 104]),
                );
            }
        }
    }

    // Keys other than ECDSA take no digest.
    let ed25519 = Ed25519KeyPair::from_seed(&[1; 32]).unwrap().public_key();
    let (digest, _) = digests(&digest::SHA256, &rind::digest::SHA256, MESSAGE);
    assert_eq!(
        ed25519.verify_digest(&digest, &[0; 64]),
        Err(Error::Unsupported)
    );
}

/// Our signing algorithm, rind's, and the verify algorithms of each.
type EcdsaPair = (
    &'static EcdsaSigningAlgorithm,
    &'static theirs::EcdsaSigningAlgorithm,
    &'static VerificationAlgorithm,
    &'static theirs::VerificationAlgorithm,
    &'static [u8],
);

const ECDSA: [EcdsaPair; 6] = [
    (
        &sign::ECDSA_P256_SHA256_ASN1,
        &theirs::sign::ECDSA_P256_SHA256_ASN1,
        &verify::ECDSA_P256_SHA256_ASN1,
        &theirs::verify::ECDSA_P256_SHA256_ASN1,
        P256,
    ),
    (
        &sign::ECDSA_P384_SHA384_ASN1,
        &theirs::sign::ECDSA_P384_SHA384_ASN1,
        &verify::ECDSA_P384_SHA384_ASN1,
        &theirs::verify::ECDSA_P384_SHA384_ASN1,
        P384,
    ),
    (
        &sign::ECDSA_P521_SHA512_ASN1,
        &theirs::sign::ECDSA_P521_SHA512_ASN1,
        &verify::ECDSA_P521_SHA512_ASN1,
        &theirs::verify::ECDSA_P521_SHA512_ASN1,
        P521,
    ),
    (
        &sign::ECDSA_P256_SHA256_FIXED,
        &theirs::sign::ECDSA_P256_SHA256_FIXED,
        &verify::ECDSA_P256_SHA256_FIXED,
        &theirs::verify::ECDSA_P256_SHA256_FIXED,
        P256,
    ),
    (
        &sign::ECDSA_P384_SHA384_FIXED,
        &theirs::sign::ECDSA_P384_SHA384_FIXED,
        &verify::ECDSA_P384_SHA384_FIXED,
        &theirs::verify::ECDSA_P384_SHA384_FIXED,
        P384,
    ),
    (
        &sign::ECDSA_P521_SHA512_FIXED,
        &theirs::sign::ECDSA_P521_SHA512_FIXED,
        &verify::ECDSA_P521_SHA512_FIXED,
        &theirs::verify::ECDSA_P521_SHA512_FIXED,
        P521,
    ),
];

#[test]
fn ecdsa_key_pairs_match_rind() {
    for (ours, theirs_alg, our_verify, their_verify, pkcs8) in ECDSA {
        same_debug(ours, theirs_alg);
        let reference = theirs::EcdsaKeyPair::from_pkcs8(theirs_alg, pkcs8).unwrap();
        let key = EcdsaKeyPair::from_pkcs8(ours, pkcs8).unwrap();
        same_debug(&key, &reference);
        same_debug(&key.public_key(), &reference.public_key());
        assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
        assert_eq!(key.to_sec1().as_ref(), reference.to_sec1().as_ref());
        assert_eq!(key.to_scalar().as_ref(), reference.to_scalar().as_ref());
        assert_eq!(key.to_spki().as_ref(), reference.to_spki().as_ref());
        same_debug(&key.to_pkcs8(), &reference.to_pkcs8());
        same_debug(&key.to_sec1(), &reference.to_sec1());
        same_debug(&key.to_scalar(), &reference.to_scalar());

        // Each loader takes what rind exports.
        let sec1 = reference.to_sec1();
        let scalar = reference.to_scalar();
        let public = reference.public_key();
        let loaded = [
            EcdsaKeyPair::from_sec1(ours, sec1.as_ref()).unwrap(),
            EcdsaKeyPair::from_scalar_and_public_key(ours, scalar.as_ref(), public.as_ref())
                .unwrap(),
        ];
        for loaded in loaded {
            assert_eq!(loaded.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
        }

        // Signatures cross both ways.
        let their_public = theirs::PublicKey::new(their_verify, key.public_key().as_ref()).unwrap();
        let our_public = PublicKey::new(our_verify, reference.public_key().as_ref()).unwrap();
        let signature = key.sign(MESSAGE).unwrap();
        their_public.verify(MESSAGE, signature.as_ref()).unwrap();
        key.public_key()
            .verify(MESSAGE, signature.as_ref())
            .unwrap();
        our_public
            .verify(MESSAGE, reference.sign(MESSAGE).unwrap().as_ref())
            .unwrap();

        let (our_digest, their_digest) = digests(&digest::SHA384, &rind::digest::SHA384, MESSAGE);
        let signature = key.sign_digest(&our_digest).unwrap();
        their_public
            .verify_digest(&their_digest, signature.as_ref())
            .unwrap();
        let (our_digest, their_digest) =
            digests(&digest::SHA3_256, &rind::digest::SHA3_256, MESSAGE);
        same_error(
            &key.sign_digest(&our_digest),
            &reference.sign_digest(&their_digest),
        );

        // Malformed and mismatched keys.
        let cases: [&[u8]; 4] = [&pkcs8[1..], &pkcs8[..pkcs8.len() - 1], &[], P384];
        for bad in cases {
            same_error(
                &EcdsaKeyPair::from_pkcs8(ours, bad),
                &theirs::EcdsaKeyPair::from_pkcs8(theirs_alg, bad),
            );
            same_error(
                &EcdsaKeyPair::from_sec1(ours, bad),
                &theirs::EcdsaKeyPair::from_sec1(theirs_alg, bad),
            );
        }
        let mut wrong = public.as_ref().to_vec();
        wrong[10] ^= 1;
        same_error(
            &EcdsaKeyPair::from_scalar_and_public_key(ours, scalar.as_ref(), &wrong),
            &theirs::EcdsaKeyPair::from_scalar_and_public_key(theirs_alg, scalar.as_ref(), &wrong),
        );
        let zero = vec![0; scalar.as_ref().len()];
        same_error(
            &EcdsaKeyPair::from_scalar_and_public_key(ours, &zero, public.as_ref()),
            &theirs::EcdsaKeyPair::from_scalar_and_public_key(theirs_alg, &zero, public.as_ref()),
        );
    }
}

#[test]
fn generated_ecdsa_keys_work_in_rind() {
    for (ours, theirs_alg, _, their_verify, _) in &ECDSA[..3] {
        let key = EcdsaKeyPair::generate(ours).unwrap();
        let reference =
            theirs::EcdsaKeyPair::from_pkcs8(theirs_alg, key.to_pkcs8().as_ref()).unwrap();
        assert_eq!(key.public_key().as_ref(), reference.public_key().as_ref());
        let signature = key.sign(MESSAGE).unwrap();
        theirs::PublicKey::new(*their_verify, key.public_key().as_ref())
            .unwrap()
            .verify(MESSAGE, signature.as_ref())
            .unwrap();
    }
}

const RSA_SIGNING: [(
    &RsaSigningAlgorithm,
    &theirs::RsaSigningAlgorithm,
    &rind_fips::signature::RsaVerificationAlgorithm,
    &theirs::RsaVerificationAlgorithm,
); 6] = [
    (
        &sign::RSA_PKCS1_SHA256,
        &theirs::sign::RSA_PKCS1_SHA256,
        &verify::RSA_PKCS1_SHA256,
        &theirs::verify::RSA_PKCS1_SHA256,
    ),
    (
        &sign::RSA_PKCS1_SHA384,
        &theirs::sign::RSA_PKCS1_SHA384,
        &verify::RSA_PKCS1_SHA384,
        &theirs::verify::RSA_PKCS1_SHA384,
    ),
    (
        &sign::RSA_PKCS1_SHA512,
        &theirs::sign::RSA_PKCS1_SHA512,
        &verify::RSA_PKCS1_SHA512,
        &theirs::verify::RSA_PKCS1_SHA512,
    ),
    (
        &sign::RSA_PSS_SHA256,
        &theirs::sign::RSA_PSS_SHA256,
        &verify::RSA_PSS_SHA256,
        &theirs::verify::RSA_PSS_SHA256,
    ),
    (
        &sign::RSA_PSS_SHA384,
        &theirs::sign::RSA_PSS_SHA384,
        &verify::RSA_PSS_SHA384,
        &theirs::verify::RSA_PSS_SHA384,
    ),
    (
        &sign::RSA_PSS_SHA512,
        &theirs::sign::RSA_PSS_SHA512,
        &verify::RSA_PSS_SHA512,
        &theirs::verify::RSA_PSS_SHA512,
    ),
];

#[test]
fn rsa_key_pairs_match_rind() {
    for pkcs8 in [RSA2048, RSA2050, RSA3072] {
        let reference = theirs::RsaKeyPair::from_pkcs8(pkcs8).unwrap();
        let key = RsaKeyPair::from_pkcs8(pkcs8).unwrap();
        same_debug(&key, &reference);
        assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
        assert_eq!(key.to_spki().as_ref(), reference.to_spki().as_ref());

        for (ours, theirs_alg, our_verify, their_verify) in RSA_SIGNING {
            same_debug(ours, theirs_alg);
            same_debug(our_verify, their_verify);
            same_debug(&key.public_key(ours), &reference.public_key(theirs_alg));
            assert_eq!(
                key.public_key(ours).as_ref(),
                reference.public_key(theirs_alg).as_ref()
            );

            let signature = key.sign(ours, MESSAGE).unwrap();
            let their_signature = reference.sign(theirs_alg, MESSAGE).unwrap();
            if format!("{ours:?}").contains("Pkcs1") {
                assert_eq!(signature.as_ref(), their_signature.as_ref());
            }
            theirs::PublicKey::new(their_verify, key.public_key(ours).as_ref())
                .unwrap()
                .verify(MESSAGE, signature.as_ref())
                .unwrap();
            key.public_key(ours)
                .verify(MESSAGE, their_signature.as_ref())
                .unwrap();
            PublicKey::new(our_verify, reference.public_key(theirs_alg).as_ref())
                .unwrap()
                .verify(MESSAGE, their_signature.as_ref())
                .unwrap();
        }
    }

    let reference = theirs::RsaKeyPair::from_pkcs1(RSA2048_PKCS1).unwrap();
    let key = RsaKeyPair::from_pkcs1(RSA2048_PKCS1).unwrap();
    assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());

    for bad in [&RSA2048[1..], &RSA2048[..RSA2048.len() - 1], &[], P256] {
        same_error(
            &RsaKeyPair::from_pkcs8(bad),
            &theirs::RsaKeyPair::from_pkcs8(bad),
        );
        same_error(
            &RsaKeyPair::from_pkcs1(bad),
            &theirs::RsaKeyPair::from_pkcs1(bad),
        );
    }
}

#[test]
fn large_rsa_keys_match_rind() {
    let keys: [&[u8]; 3] = [
        include_bytes!("../../rind/src/high/rsa/rsa4096.pkcs8.der"),
        include_bytes!("../../rind/src/high/rsa/rsa6144.pkcs8.der"),
        include_bytes!("../../rind/src/high/rsa/rsa8192.pkcs8.der"),
    ];
    for pkcs8 in keys {
        let reference = theirs::RsaKeyPair::from_pkcs8(pkcs8).unwrap();
        let key = RsaKeyPair::from_pkcs8(pkcs8).unwrap();
        assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
        let signature = key.sign(&sign::RSA_PKCS1_SHA512, MESSAGE).unwrap();
        let their_signature = reference
            .sign(&theirs::sign::RSA_PKCS1_SHA512, MESSAGE)
            .unwrap();
        assert_eq!(signature.as_ref(), their_signature.as_ref());
        key.public_key(&sign::RSA_PSS_SHA512)
            .verify(
                MESSAGE,
                key.sign(&sign::RSA_PSS_SHA512, MESSAGE).unwrap().as_ref(),
            )
            .unwrap();
    }
}

#[test]
fn generated_rsa_keys_work_in_rind() {
    same_debug(&KeySize::Rsa2048, &rind::rsa::KeySize::Rsa2048);
    let key = RsaKeyPair::generate(KeySize::Rsa2048).unwrap();
    let reference = theirs::RsaKeyPair::from_pkcs8(key.to_pkcs8().as_ref()).unwrap();
    assert_eq!(key.to_spki().as_ref(), reference.to_spki().as_ref());
    let signature = key.sign(&sign::RSA_PSS_SHA256, MESSAGE).unwrap();
    theirs::PublicKey::from_spki(&theirs::verify::RSA_PSS_SHA256, key.to_spki().as_ref())
        .unwrap()
        .verify(MESSAGE, signature.as_ref())
        .unwrap();
}

/// The modulus and exponent of PKCS#1 `RSAPublicKey` DER.
fn components(der: &[u8]) -> (Vec<u8>, Vec<u8>) {
    fn element(der: &[u8]) -> (&[u8], &[u8]) {
        let (len, at) = match der[1] {
            len @ 0..=0x7f => (len as usize, 2),
            0x81 => (der[2] as usize, 3),
            0x82 => (u16::from_be_bytes([der[2], der[3]]) as usize, 4),
            other => panic!("length form {other:#x}"),
        };
        (&der[at..at + len], &der[at + len..])
    }
    let (sequence, _) = element(der);
    let (n, rest) = element(sequence);
    let (e, _) = element(rest);
    let strip = |x: &[u8]| x[x.iter().position(|&b| b != 0).unwrap()..].to_vec();
    (strip(n), strip(e))
}

#[test]
fn rsa_components_match_rind() {
    let reference = theirs::RsaKeyPair::from_pkcs8(RSA2048).unwrap();
    let pkcs1 = reference.public_key(&theirs::sign::RSA_PKCS1_SHA256);
    let (n, e) = components(pkcs1.as_ref());
    let signature = reference
        .sign(&theirs::sign::RSA_PKCS1_SHA256, MESSAGE)
        .unwrap();

    let ours = PublicKeyComponents {
        n: &n[..],
        e: &e[..],
    };
    let theirs_components = rind::rsa::PublicKeyComponents {
        n: &n[..],
        e: &e[..],
    };
    same_debug(&ours, &theirs_components);
    let key = PublicKey::from_components(&verify::RSA_PKCS1_SHA256, &ours).unwrap();
    assert_eq!(key.as_ref(), pkcs1.as_ref());
    key.verify(MESSAGE, signature.as_ref()).unwrap();

    let even = PublicKeyComponents {
        n: &n[..],
        e: &[2u8][..],
    };
    same_error(
        &PublicKey::from_components(&verify::RSA_PKCS1_SHA256, &even),
        &theirs::PublicKey::from_components(
            &theirs::verify::RSA_PKCS1_SHA256,
            &rind::rsa::PublicKeyComponents {
                n: &n[..],
                e: &[2u8][..],
            },
        ),
    );
}

/// An RSA modulus of `bits` bits, odd, which no one can factor or need to.
fn modulus(bits: usize) -> Vec<u8> {
    let mut n = vec![0xa5; bits.div_ceil(8)];
    let top = bits % 8;
    n[0] = if top == 0 {
        0xc5
    } else {
        (0xc5 >> (8 - top)) | (1 << (top - 1))
    };
    *n.last_mut().unwrap() |= 1;
    n
}

#[test]
fn rsa_moduli_fips_does_not_approve_are_refused() {
    let refused = Error::KeyRejected(match RsaKeyPair::from_pkcs8(RSA2049) {
        Err(Error::KeyRejected(reason)) => reason,
        other => panic!("{other:?}"),
    });
    // rind's reason for a modulus too small.
    let reason =
        theirs::RsaKeyPair::from_pkcs8(include_bytes!("../../rind/src/high/rsa/rsa2047.pkcs8.der"));
    assert_eq!(
        Some(refused.to_string()),
        reason.err().map(|e| e.to_string())
    );

    // An odd length rind signs with.
    assert!(theirs::RsaKeyPair::from_pkcs8(RSA2049).is_ok());

    // rind verifies with an odd length, or one between 1024 and 2048 bits,
    // under the legacy algorithms.
    let e = [1, 0, 1];
    for bits in [1024, 1536, 2047, 2048, 2049, 3071, 3072] {
        let n = modulus(bits);
        let algorithms: [(
            &rind_fips::signature::RsaVerificationAlgorithm,
            &theirs::RsaVerificationAlgorithm,
        ); 3] = [
            (
                &verify::legacy::RSA_PKCS1_1024_SHA256,
                &theirs::verify::legacy::RSA_PKCS1_1024_SHA256,
            ),
            (&verify::RSA_PKCS1_SHA256, &theirs::verify::RSA_PKCS1_SHA256),
            (
                &verify::legacy::RSA_PKCS1_3072_SHA384,
                &theirs::verify::legacy::RSA_PKCS1_3072_SHA384,
            ),
        ];
        for (ours, theirs_alg) in algorithms {
            let our_key = PublicKey::from_components(
                ours,
                &PublicKeyComponents {
                    n: &n[..],
                    e: &e[..],
                },
            );
            let their_key = theirs::PublicKey::from_components(
                theirs_alg,
                &rind::rsa::PublicKeyComponents {
                    n: &n[..],
                    e: &e[..],
                },
            );
            let approved = bits == 1024 || (bits >= 2048 && bits % 2 == 0);
            match (approved, &their_key) {
                (true, _) | (false, Err(_)) => same_error(&our_key, &their_key),
                (false, Ok(_)) => assert_eq!(our_key.err(), Some(refused), "{bits} bits, {ours:?}"),
            }
        }
    }
    same_error(
        &PublicKey::new(&verify::RSA_PKCS1_SHA256, RSA2047_PUBLIC),
        &theirs::PublicKey::new(&theirs::verify::RSA_PKCS1_SHA256, RSA2047_PUBLIC),
    );
    assert_eq!(
        PublicKey::new(&verify::legacy::RSA_PKCS1_1024_SHA256, RSA2047_PUBLIC).err(),
        Some(refused)
    );
    assert!(
        theirs::PublicKey::new(
            &theirs::verify::legacy::RSA_PKCS1_1024_SHA256,
            RSA2047_PUBLIC
        )
        .is_ok()
    );
}

#[test]
fn ed25519_key_pairs_match_rind() {
    // RFC 8032's test 1.
    let seed: [u8; 32] = [
        0x9d, 0x61, 0xb1, 0x9d, 0xef, 0xfd, 0x5a, 0x60, 0xba, 0x84, 0x4a, 0xf4, 0x92, 0xec, 0x2c,
        0xc4, 0x44, 0x49, 0xc5, 0x69, 0x7b, 0x7f, 0xda, 0x41, 0x63, 0x3a, 0xb6, 0xe2, 0x2e, 0x1e,
        0x2f, 0x2f,
    ];
    let reference = theirs::Ed25519KeyPair::from_seed(&seed).unwrap();
    let key = Ed25519KeyPair::from_seed(&seed).unwrap();
    same_debug(&key, &reference);
    same_debug(&key.public_key(), &reference.public_key());
    assert_eq!(key.public_key().as_ref(), reference.public_key().as_ref());
    assert_eq!(key.sign(MESSAGE).as_ref(), reference.sign(MESSAGE).as_ref());
    same_debug(&key.sign(MESSAGE), &reference.sign(MESSAGE));
    assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
    assert_eq!(key.to_pkcs8v1().as_ref(), reference.to_pkcs8v1().as_ref());
    assert_eq!(key.to_seed().as_ref(), reference.to_seed().as_ref());
    same_debug(&key.to_seed(), &reference.to_seed());
    assert_eq!(key.to_spki().as_ref(), reference.to_spki().as_ref());

    for pkcs8 in [reference.to_pkcs8(), reference.to_pkcs8v1()] {
        let loaded = Ed25519KeyPair::from_pkcs8(pkcs8.as_ref()).unwrap();
        assert_eq!(
            loaded.sign(MESSAGE).as_ref(),
            reference.sign(MESSAGE).as_ref()
        );
    }
    let public = reference.public_key();
    Ed25519KeyPair::from_seed_and_public_key(&seed, public.as_ref()).unwrap();

    let mut wrong = public.as_ref().to_vec();
    wrong[0] ^= 1;
    same_error(
        &Ed25519KeyPair::from_seed_and_public_key(&seed, &wrong),
        &theirs::Ed25519KeyPair::from_seed_and_public_key(&seed, &wrong),
    );
    let pkcs8 = reference.to_pkcs8();
    let bad_cases: [&[u8]; 4] = [&seed[1..], &[], &pkcs8.as_ref()[1..], P256];
    for bad in bad_cases {
        same_error(
            &Ed25519KeyPair::from_seed(bad),
            &theirs::Ed25519KeyPair::from_seed(bad),
        );
        same_error(
            &Ed25519KeyPair::from_pkcs8(bad),
            &theirs::Ed25519KeyPair::from_pkcs8(bad),
        );
    }

    let generated = Ed25519KeyPair::generate().unwrap();
    let reference = theirs::Ed25519KeyPair::from_pkcs8(generated.to_pkcs8().as_ref()).unwrap();
    assert_eq!(
        generated.sign(MESSAGE).as_ref(),
        reference.sign(MESSAGE).as_ref()
    );
}

fn ml_dsa_matches_rind<P: MlDsaParameterSet, Q: theirs::sign::MlDsaParameterSet>(
    ours: &'static VerificationAlgorithm,
    theirs_alg: &'static theirs::VerificationAlgorithm,
) {
    let seed = [3; 32];
    let reference = theirs::sign::MlDsaKeyPair::<Q>::from_seed(&seed).unwrap();
    let key = MlDsaKeyPair::<P>::from_seed(&seed).unwrap();
    same_debug(&key, &reference);
    same_debug(&key.public_key(), &reference.public_key());
    assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
    assert_eq!(
        key.to_seed().unwrap().as_ref(),
        reference.to_seed().unwrap().as_ref()
    );
    same_debug(&key.to_seed(), &reference.to_seed());

    // Signatures are hedged, so cross rather than match.
    let signature = key.sign(MESSAGE).unwrap();
    assert_eq!(
        signature.as_ref().len(),
        reference.sign(MESSAGE).unwrap().as_ref().len()
    );
    theirs::PublicKey::new(theirs_alg, key.public_key().as_ref())
        .unwrap()
        .verify(MESSAGE, signature.as_ref())
        .unwrap();
    PublicKey::new(ours, reference.public_key().as_ref())
        .unwrap()
        .verify(MESSAGE, reference.sign(MESSAGE).unwrap().as_ref())
        .unwrap();
    let cloned = signature.clone();
    assert_eq!(format!("{cloned:?}"), format!("{signature:?}"));

    let loaded = MlDsaKeyPair::<P>::from_pkcs8(reference.to_pkcs8().as_ref()).unwrap();
    assert_eq!(
        loaded.public_key().as_ref(),
        reference.public_key().as_ref()
    );

    let generated = MlDsaKeyPair::<P>::generate().unwrap();
    let reloaded =
        theirs::sign::MlDsaKeyPair::<Q>::from_pkcs8(generated.to_pkcs8().as_ref()).unwrap();
    assert_eq!(
        generated.public_key().as_ref(),
        reloaded.public_key().as_ref()
    );

    let pkcs8 = reference.to_pkcs8();
    let bad_cases: [&[u8]; 4] = [&seed[1..], &[], &pkcs8.as_ref()[1..], P256];
    for bad in bad_cases {
        same_error(
            &MlDsaKeyPair::<P>::from_seed(bad),
            &theirs::sign::MlDsaKeyPair::<Q>::from_seed(bad),
        );
        same_error(
            &MlDsaKeyPair::<P>::from_pkcs8(bad),
            &theirs::sign::MlDsaKeyPair::<Q>::from_pkcs8(bad),
        );
    }
}

#[test]
fn ml_dsa_key_pairs_match_rind() {
    ml_dsa_matches_rind::<MlDsa44, theirs::sign::MlDsa44>(
        &verify::ML_DSA_44,
        &theirs::verify::ML_DSA_44,
    );
    ml_dsa_matches_rind::<MlDsa65, theirs::sign::MlDsa65>(
        &verify::ML_DSA_65,
        &theirs::verify::ML_DSA_65,
    );
    ml_dsa_matches_rind::<MlDsa87, theirs::sign::MlDsa87>(
        &verify::ML_DSA_87,
        &theirs::verify::ML_DSA_87,
    );
}
