// SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0

//! Signatures through the module agree with rind's, which its own tests
//! check against Wycheproof and aws-lc-rs: keys, encodings, and signatures
//! cross between the two, deterministic signatures match byte for byte, and
//! malformed input fails with the same error. The module refuses the RSA
//! moduli FIPS 186-5 does not approve, which rind takes.
#![cfg(rind_fips_module)]

use rind_fips::rsa::{KeySize, PublicKeyComponents};
use rind_fips::{Error, digest, ecdsa, ed25519, ml_dsa, rsa};

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

/// Both refuse, with the same error.
#[track_caller]
fn same_refusal<A, B>(ours: &Result<A, Error>, theirs: &Result<B, rind::Error>) {
    assert!(ours.is_err() && theirs.is_err(), "accepted");
    same_error(ours, theirs);
}

/// The `Debug` of `ours` is `theirs`', plain and pretty.
#[track_caller]
fn same_debug(ours: &impl core::fmt::Debug, theirs: &impl core::fmt::Debug) {
    assert_eq!(format!("{ours:?}"), format!("{theirs:?}"));
    assert_eq!(format!("{ours:#?}"), format!("{theirs:#?}"));
}

/// The module's verdicts match rind's: both verify `signature` over
/// [`MESSAGE`], and refuse alike a flipped, truncated, or empty one, or
/// another message.
#[track_caller]
fn same_verdicts(
    ours: impl Fn(&[u8], &[u8]) -> Result<(), Error>,
    theirs: impl Fn(&[u8], &[u8]) -> Result<(), rind::Error>,
    signature: &[u8],
) {
    ours(MESSAGE, signature).unwrap();
    theirs(MESSAGE, signature).unwrap();
    let mut flipped = signature.to_vec();
    flipped[signature.len() / 2] ^= 1;
    let truncated = &signature[..signature.len() - 1];
    for signature in [&flipped[..], truncated, &[]] {
        same_refusal(&ours(MESSAGE, signature), &theirs(MESSAGE, signature));
    }
    same_refusal(&ours(b"another", signature), &theirs(b"another", signature));
}

/// The module parses `encoded` as rind does, to the same bytes, and refuses
/// alike what rind refuses: it cut at either end, or empty.
#[track_caller]
fn same_parse<A: AsRef<[u8]>, B: AsRef<[u8]>>(
    ours: impl Fn(&[u8]) -> Result<A, Error>,
    theirs: impl Fn(&[u8]) -> Result<B, rind::Error>,
    encoded: &[u8],
) {
    assert_eq!(
        ours(encoded).unwrap().as_ref(),
        theirs(encoded).unwrap().as_ref()
    );
    for bad in [&encoded[1..], &encoded[..encoded.len() - 1], &[]] {
        same_refusal(&ours(bad), &theirs(bad));
    }
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

/// Our verify algorithm, rind's, and rind's signing algorithm, key, and
/// hash for a signature it verifies.
type EcdsaVerify = (
    &'static ecdsa::VerificationAlgorithm,
    &'static rind::ecdsa::VerificationAlgorithm,
    &'static rind::ecdsa::SigningAlgorithm,
    &'static [u8],
    &'static rind::digest::Algorithm,
);

const ECDSA_VERIFY: [EcdsaVerify; 12] = {
    use rind::digest::{SHA256, SHA384, SHA512};
    use rind::ecdsa::{sign, verify as theirs};
    use rind_fips::ecdsa::verify as ours;
    let p256 = &sign::P256_SHA256_ASN1;
    let p384 = &sign::P384_SHA384_ASN1;
    let p521 = &sign::P521_SHA512_ASN1;
    [
        (
            &ours::P256_SHA256_ASN1,
            &theirs::P256_SHA256_ASN1,
            p256,
            P256,
            &SHA256,
        ),
        (
            &ours::P256_SHA384_ASN1,
            &theirs::P256_SHA384_ASN1,
            p256,
            P256,
            &SHA384,
        ),
        (
            &ours::P256_SHA512_ASN1,
            &theirs::P256_SHA512_ASN1,
            p256,
            P256,
            &SHA512,
        ),
        (
            &ours::P384_SHA256_ASN1,
            &theirs::P384_SHA256_ASN1,
            p384,
            P384,
            &SHA256,
        ),
        (
            &ours::P384_SHA384_ASN1,
            &theirs::P384_SHA384_ASN1,
            p384,
            P384,
            &SHA384,
        ),
        (
            &ours::P384_SHA512_ASN1,
            &theirs::P384_SHA512_ASN1,
            p384,
            P384,
            &SHA512,
        ),
        (
            &ours::P521_SHA256_ASN1,
            &theirs::P521_SHA256_ASN1,
            p521,
            P521,
            &SHA256,
        ),
        (
            &ours::P521_SHA384_ASN1,
            &theirs::P521_SHA384_ASN1,
            p521,
            P521,
            &SHA384,
        ),
        (
            &ours::P521_SHA512_ASN1,
            &theirs::P521_SHA512_ASN1,
            p521,
            P521,
            &SHA512,
        ),
        (
            &ours::P256_SHA256_FIXED,
            &theirs::P256_SHA256_FIXED,
            &sign::P256_SHA256_FIXED,
            P256,
            &SHA256,
        ),
        (
            &ours::P384_SHA384_FIXED,
            &theirs::P384_SHA384_FIXED,
            &sign::P384_SHA384_FIXED,
            P384,
            &SHA384,
        ),
        (
            &ours::P521_SHA512_FIXED,
            &theirs::P521_SHA512_FIXED,
            &sign::P521_SHA512_FIXED,
            P521,
            &SHA512,
        ),
    ]
};

#[test]
fn ecdsa_public_keys_verify_as_rind_does() {
    for (ours, theirs, signer, pkcs8, hash) in ECDSA_VERIFY {
        same_debug(ours, theirs);
        let signer = rind::ecdsa::KeyPair::from_pkcs8(signer, pkcs8).unwrap();
        let signature = signer
            .sign_digest(&rind::digest::digest(hash, MESSAGE))
            .unwrap();
        let point = signer.public_key().as_ref();

        let reference = rind::ecdsa::PublicKey::new(theirs, point).unwrap();
        let key = ecdsa::PublicKey::new(ours, point).unwrap();
        same_debug(&key, &reference);
        same_verdicts(
            |m, s| key.verify(m, s),
            |m, s| reference.verify(m, s),
            signature.as_ref(),
        );
        same_parse(
            |b| ecdsa::PublicKey::new(ours, b),
            |b| rind::ecdsa::PublicKey::new(theirs, b),
            point,
        );

        let spki = reference.to_spki();
        assert_eq!(key.to_spki().as_ref(), spki.as_ref());
        same_parse(
            |b| ecdsa::PublicKey::from_spki(ours, b),
            |b| rind::ecdsa::PublicKey::from_spki(theirs, b),
            spki.as_ref(),
        );
    }
}

#[test]
fn ecdsa_verify_digest_matches_rind() {
    let reference =
        rind::ecdsa::KeyPair::from_pkcs8(&rind::ecdsa::sign::P384_SHA384_ASN1, P384).unwrap();
    let key = ecdsa::PublicKey::new(
        &ecdsa::verify::P384_SHA384_ASN1,
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
}

/// Our signing algorithm, rind's, and the verify algorithms of each.
type EcdsaPair = (
    &'static ecdsa::SigningAlgorithm,
    &'static rind::ecdsa::SigningAlgorithm,
    &'static ecdsa::VerificationAlgorithm,
    &'static rind::ecdsa::VerificationAlgorithm,
    &'static [u8],
);

const ECDSA: [EcdsaPair; 6] = {
    use rind::ecdsa::{sign as their_sign, verify as their_verify};
    use rind_fips::ecdsa::{sign, verify};
    [
        (
            &sign::P256_SHA256_ASN1,
            &their_sign::P256_SHA256_ASN1,
            &verify::P256_SHA256_ASN1,
            &their_verify::P256_SHA256_ASN1,
            P256,
        ),
        (
            &sign::P384_SHA384_ASN1,
            &their_sign::P384_SHA384_ASN1,
            &verify::P384_SHA384_ASN1,
            &their_verify::P384_SHA384_ASN1,
            P384,
        ),
        (
            &sign::P521_SHA512_ASN1,
            &their_sign::P521_SHA512_ASN1,
            &verify::P521_SHA512_ASN1,
            &their_verify::P521_SHA512_ASN1,
            P521,
        ),
        (
            &sign::P256_SHA256_FIXED,
            &their_sign::P256_SHA256_FIXED,
            &verify::P256_SHA256_FIXED,
            &their_verify::P256_SHA256_FIXED,
            P256,
        ),
        (
            &sign::P384_SHA384_FIXED,
            &their_sign::P384_SHA384_FIXED,
            &verify::P384_SHA384_FIXED,
            &their_verify::P384_SHA384_FIXED,
            P384,
        ),
        (
            &sign::P521_SHA512_FIXED,
            &their_sign::P521_SHA512_FIXED,
            &verify::P521_SHA512_FIXED,
            &their_verify::P521_SHA512_FIXED,
            P521,
        ),
    ]
};

#[test]
fn ecdsa_key_pairs_match_rind() {
    for (ours, theirs_alg, our_verify, their_verify, pkcs8) in ECDSA {
        same_debug(ours, theirs_alg);
        let reference = rind::ecdsa::KeyPair::from_pkcs8(theirs_alg, pkcs8).unwrap();
        let key = ecdsa::KeyPair::from_pkcs8(ours, pkcs8).unwrap();
        same_debug(&key, &reference);
        same_debug(key.public_key(), reference.public_key());
        assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
        assert_eq!(key.to_sec1().as_ref(), reference.to_sec1().as_ref());
        assert_eq!(key.to_scalar().as_ref(), reference.to_scalar().as_ref());
        assert_eq!(
            key.public_key().to_spki().as_ref(),
            reference.public_key().to_spki().as_ref()
        );
        same_debug(&key.to_pkcs8(), &reference.to_pkcs8());
        same_debug(&key.to_sec1(), &reference.to_sec1());
        same_debug(&key.to_scalar(), &reference.to_scalar());

        // Each loader takes what rind exports.
        let sec1 = reference.to_sec1();
        let scalar = reference.to_scalar();
        let public = reference.public_key();
        let loaded = [
            ecdsa::KeyPair::from_sec1(ours, sec1.as_ref()).unwrap(),
            ecdsa::KeyPair::from_scalar_and_public_key(ours, scalar.as_ref(), public.as_ref())
                .unwrap(),
        ];
        for loaded in loaded {
            assert_eq!(loaded.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
        }

        // Signatures cross both ways.
        let their_public =
            rind::ecdsa::PublicKey::new(their_verify, key.public_key().as_ref()).unwrap();
        let our_public = ecdsa::PublicKey::new(our_verify, public.as_ref()).unwrap();
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
                &ecdsa::KeyPair::from_pkcs8(ours, bad),
                &rind::ecdsa::KeyPair::from_pkcs8(theirs_alg, bad),
            );
            same_error(
                &ecdsa::KeyPair::from_sec1(ours, bad),
                &rind::ecdsa::KeyPair::from_sec1(theirs_alg, bad),
            );
        }
        let mut wrong = public.as_ref().to_vec();
        wrong[10] ^= 1;
        same_error(
            &ecdsa::KeyPair::from_scalar_and_public_key(ours, scalar.as_ref(), &wrong),
            &rind::ecdsa::KeyPair::from_scalar_and_public_key(theirs_alg, scalar.as_ref(), &wrong),
        );
        let zero = vec![0; scalar.as_ref().len()];
        same_error(
            &ecdsa::KeyPair::from_scalar_and_public_key(ours, &zero, public.as_ref()),
            &rind::ecdsa::KeyPair::from_scalar_and_public_key(theirs_alg, &zero, public.as_ref()),
        );
    }
}

#[test]
fn generated_ecdsa_keys_work_in_rind() {
    for (ours, theirs_alg, _, their_verify, _) in &ECDSA[..3] {
        let key = ecdsa::KeyPair::generate(ours).unwrap();
        let reference =
            rind::ecdsa::KeyPair::from_pkcs8(theirs_alg, key.to_pkcs8().as_ref()).unwrap();
        assert_eq!(key.public_key().as_ref(), reference.public_key().as_ref());
        let signature = key.sign(MESSAGE).unwrap();
        rind::ecdsa::PublicKey::new(their_verify, key.public_key().as_ref())
            .unwrap()
            .verify(MESSAGE, signature.as_ref())
            .unwrap();
    }
}

/// Our verify algorithm, rind's, and rind's signature over [`MESSAGE`] for
/// it with the key in `pkcs8`.
type RsaVerify = (
    &'static rsa::VerificationAlgorithm,
    &'static rind::rsa::VerificationAlgorithm,
    Vec<u8>,
    &'static [u8],
);

fn rsa_signature(algorithm: &rind::rsa::SigningAlgorithm, pkcs8: &[u8]) -> Vec<u8> {
    let key = rind::rsa::KeyPair::from_pkcs8(pkcs8).unwrap();
    key.sign(algorithm, MESSAGE).unwrap().as_ref().to_vec()
}

/// An RSASSA-PKCS1-v1_5 signature with SHA-1 over [`MESSAGE`] by the key
/// in [`RSA2048`], which rind signs only as a raw RSA operation: a blind
/// signature over the encoded message.
fn rsa_sha1_signature() -> Vec<u8> {
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
    key.blind_sign(&encoded).unwrap().as_ref().to_vec()
}

/// A case for every RSA verify algorithm.
fn rsa_verify_cases() -> Vec<RsaVerify> {
    use rind::rsa::{sign, verify as theirs};
    use rind_fips::rsa::verify as ours;
    vec![
        (
            &ours::PKCS1_SHA256,
            &theirs::PKCS1_SHA256,
            rsa_signature(&sign::PKCS1_SHA256, RSA2048),
            RSA2048,
        ),
        (
            &ours::PKCS1_SHA384,
            &theirs::PKCS1_SHA384,
            rsa_signature(&sign::PKCS1_SHA384, RSA2048),
            RSA2048,
        ),
        (
            &ours::PKCS1_SHA512,
            &theirs::PKCS1_SHA512,
            rsa_signature(&sign::PKCS1_SHA512, RSA2048),
            RSA2048,
        ),
        (
            &ours::PSS_SHA256,
            &theirs::PSS_SHA256,
            rsa_signature(&sign::PSS_SHA256, RSA2048),
            RSA2048,
        ),
        (
            &ours::PSS_SHA384,
            &theirs::PSS_SHA384,
            rsa_signature(&sign::PSS_SHA384, RSA2048),
            RSA2048,
        ),
        (
            &ours::PSS_SHA512,
            &theirs::PSS_SHA512,
            rsa_signature(&sign::PSS_SHA512, RSA2048),
            RSA2048,
        ),
        (
            &ours::legacy::PKCS1_SHA1,
            &theirs::legacy::PKCS1_SHA1,
            rsa_sha1_signature(),
            RSA2048,
        ),
        (
            &ours::legacy::PKCS1_1024_SHA1,
            &theirs::legacy::PKCS1_1024_SHA1,
            rsa_sha1_signature(),
            RSA2048,
        ),
        (
            &ours::legacy::PKCS1_1024_SHA256,
            &theirs::legacy::PKCS1_1024_SHA256,
            rsa_signature(&sign::PKCS1_SHA256, RSA2048),
            RSA2048,
        ),
        (
            &ours::legacy::PKCS1_1024_SHA512,
            &theirs::legacy::PKCS1_1024_SHA512,
            rsa_signature(&sign::PKCS1_SHA512, RSA2048),
            RSA2048,
        ),
        (
            &ours::legacy::PKCS1_3072_SHA384,
            &theirs::legacy::PKCS1_3072_SHA384,
            rsa_signature(&sign::PKCS1_SHA384, RSA3072),
            RSA3072,
        ),
    ]
}

#[test]
fn rsa_public_keys_verify_as_rind_does() {
    for (ours, theirs, signature, pkcs8) in rsa_verify_cases() {
        same_debug(ours, theirs);
        let signer = rind::rsa::KeyPair::from_pkcs8(pkcs8).unwrap();
        let pkcs1 = signer.public_key().as_ref();

        let reference = rind::rsa::PublicKey::new(pkcs1).unwrap();
        let key = rsa::PublicKey::new(pkcs1).unwrap();
        same_debug(&key, &reference);
        assert_eq!(key.modulus_len(), reference.modulus_len());
        same_verdicts(
            |m, s| key.verify(ours, m, s),
            |m, s| reference.verify(theirs, m, s),
            &signature,
        );
        same_parse(rsa::PublicKey::new, rind::rsa::PublicKey::new, pkcs1);

        let spki = reference.to_spki();
        assert_eq!(key.to_spki().as_ref(), spki.as_ref());
        same_parse(
            rsa::PublicKey::from_spki,
            rind::rsa::PublicKey::from_spki,
            spki.as_ref(),
        );
        // Each loader takes its own encoding alone, as rind's does.
        same_error(
            &rsa::PublicKey::new(spki.as_ref()),
            &rind::rsa::PublicKey::new(spki.as_ref()),
        );
        same_error(
            &rsa::PublicKey::from_spki(pkcs1),
            &rind::rsa::PublicKey::from_spki(pkcs1),
        );
    }
}

/// Our signing algorithm, rind's, and the verify algorithms of each.
type RsaPair = (
    &'static rsa::SigningAlgorithm,
    &'static rind::rsa::SigningAlgorithm,
    &'static rsa::VerificationAlgorithm,
    &'static rind::rsa::VerificationAlgorithm,
);

const RSA_SIGNING: [RsaPair; 6] = {
    use rind::rsa::{sign as their_sign, verify as their_verify};
    use rind_fips::rsa::{sign, verify};
    [
        (
            &sign::PKCS1_SHA256,
            &their_sign::PKCS1_SHA256,
            &verify::PKCS1_SHA256,
            &their_verify::PKCS1_SHA256,
        ),
        (
            &sign::PKCS1_SHA384,
            &their_sign::PKCS1_SHA384,
            &verify::PKCS1_SHA384,
            &their_verify::PKCS1_SHA384,
        ),
        (
            &sign::PKCS1_SHA512,
            &their_sign::PKCS1_SHA512,
            &verify::PKCS1_SHA512,
            &their_verify::PKCS1_SHA512,
        ),
        (
            &sign::PSS_SHA256,
            &their_sign::PSS_SHA256,
            &verify::PSS_SHA256,
            &their_verify::PSS_SHA256,
        ),
        (
            &sign::PSS_SHA384,
            &their_sign::PSS_SHA384,
            &verify::PSS_SHA384,
            &their_verify::PSS_SHA384,
        ),
        (
            &sign::PSS_SHA512,
            &their_sign::PSS_SHA512,
            &verify::PSS_SHA512,
            &their_verify::PSS_SHA512,
        ),
    ]
};

#[test]
fn rsa_key_pairs_match_rind() {
    for pkcs8 in [RSA2048, RSA2050, RSA3072] {
        let reference = rind::rsa::KeyPair::from_pkcs8(pkcs8).unwrap();
        let key = rsa::KeyPair::from_pkcs8(pkcs8).unwrap();
        same_debug(&key, &reference);
        same_debug(key.public_key(), reference.public_key());
        assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
        assert_eq!(
            key.public_key().to_spki().as_ref(),
            reference.public_key().to_spki().as_ref()
        );
        assert_eq!(
            key.public_key().modulus_len(),
            reference.public_key().modulus_len()
        );

        for (ours, theirs_alg, our_verify, their_verify) in RSA_SIGNING {
            same_debug(ours, theirs_alg);
            let signature = key.sign(ours, MESSAGE).unwrap();
            let their_signature = reference.sign(theirs_alg, MESSAGE).unwrap();
            if format!("{ours:?}").contains("Pkcs1") {
                assert_eq!(signature.as_ref(), their_signature.as_ref());
                same_debug(&signature, &their_signature);
            }
            reference
                .public_key()
                .verify(their_verify, MESSAGE, signature.as_ref())
                .unwrap();
            key.public_key()
                .verify(our_verify, MESSAGE, their_signature.as_ref())
                .unwrap();
        }
    }

    let reference = rind::rsa::KeyPair::from_pkcs1(RSA2048_PKCS1).unwrap();
    let key = rsa::KeyPair::from_pkcs1(RSA2048_PKCS1).unwrap();
    assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());

    for bad in [&RSA2048[1..], &RSA2048[..RSA2048.len() - 1], &[], P256] {
        same_error(
            &rsa::KeyPair::from_pkcs8(bad),
            &rind::rsa::KeyPair::from_pkcs8(bad),
        );
        same_error(
            &rsa::KeyPair::from_pkcs1(bad),
            &rind::rsa::KeyPair::from_pkcs1(bad),
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
        let reference = rind::rsa::KeyPair::from_pkcs8(pkcs8).unwrap();
        let key = rsa::KeyPair::from_pkcs8(pkcs8).unwrap();
        assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
        let signature = key.sign(&rsa::sign::PKCS1_SHA512, MESSAGE).unwrap();
        let their_signature = reference
            .sign(&rind::rsa::sign::PKCS1_SHA512, MESSAGE)
            .unwrap();
        assert_eq!(signature.as_ref(), their_signature.as_ref());
        let signature = key.sign(&rsa::sign::PSS_SHA512, MESSAGE).unwrap();
        key.public_key()
            .verify(&rsa::verify::PSS_SHA512, MESSAGE, signature.as_ref())
            .unwrap();
    }
}

#[test]
fn generated_rsa_keys_work_in_rind() {
    same_debug(&KeySize::Rsa2048, &rind::rsa::KeySize::Rsa2048);
    let key = rsa::KeyPair::generate(KeySize::Rsa2048).unwrap();
    let reference = rind::rsa::KeyPair::from_pkcs8(key.to_pkcs8().as_ref()).unwrap();
    let spki = key.public_key().to_spki();
    assert_eq!(spki.as_ref(), reference.public_key().to_spki().as_ref());
    let signature = key.sign(&rsa::sign::PSS_SHA256, MESSAGE).unwrap();
    rind::rsa::PublicKey::from_spki(spki.as_ref())
        .unwrap()
        .verify(&rind::rsa::verify::PSS_SHA256, MESSAGE, signature.as_ref())
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
    let reference = rind::rsa::KeyPair::from_pkcs8(RSA2048).unwrap();
    let pkcs1 = reference.public_key();
    let (n, e) = components(pkcs1.as_ref());
    let signature = reference
        .sign(&rind::rsa::sign::PKCS1_SHA256, MESSAGE)
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
    let key = rsa::PublicKey::from_components(&ours).unwrap();
    assert_eq!(key.as_ref(), pkcs1.as_ref());
    key.verify(&rsa::verify::PKCS1_SHA256, MESSAGE, signature.as_ref())
        .unwrap();

    let even = PublicKeyComponents {
        n: &n[..],
        e: &[2u8][..],
    };
    same_error(
        &rsa::PublicKey::from_components(&even),
        &rind::rsa::PublicKey::from_components(&rind::rsa::PublicKeyComponents {
            n: &n[..],
            e: &[2u8][..],
        }),
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
    let refused = Error::KeyRejected(match rsa::KeyPair::from_pkcs8(RSA2049) {
        Err(Error::KeyRejected(reason)) => reason,
        other => panic!("{other:?}"),
    });
    // rind's reason for a modulus too small.
    let reason =
        rind::rsa::KeyPair::from_pkcs8(include_bytes!("../../rind/src/high/rsa/rsa2047.pkcs8.der"));
    assert_eq!(
        Some(refused.to_string()),
        reason.err().map(|e| e.to_string())
    );

    // An odd length rind signs with.
    assert!(rind::rsa::KeyPair::from_pkcs8(RSA2049).is_ok());

    // rind parses a public key of an odd length, or between 1024 and 2048
    // bits, and verifies with it under an algorithm whose floor it meets.
    // The module parses only an even length from 2048 bits, or 1024 bits,
    // which verifies only under the legacy algorithms that name it.
    let e = [1, 0, 1];
    let algorithms: [(
        &rsa::VerificationAlgorithm,
        &rind::rsa::VerificationAlgorithm,
    ); 4] = [
        (
            &rsa::verify::legacy::PKCS1_1024_SHA256,
            &rind::rsa::verify::legacy::PKCS1_1024_SHA256,
        ),
        (
            &rsa::verify::legacy::PKCS1_SHA1,
            &rind::rsa::verify::legacy::PKCS1_SHA1,
        ),
        (&rsa::verify::PKCS1_SHA256, &rind::rsa::verify::PKCS1_SHA256),
        (
            &rsa::verify::legacy::PKCS1_3072_SHA384,
            &rind::rsa::verify::legacy::PKCS1_3072_SHA384,
        ),
    ];
    for bits in [1024, 1536, 2047, 2048, 2049, 3071, 3072] {
        let n = modulus(bits);
        let our_key = rsa::PublicKey::from_components(&PublicKeyComponents {
            n: &n[..],
            e: &e[..],
        });
        let their_key = rind::rsa::PublicKey::from_components(&rind::rsa::PublicKeyComponents {
            n: &n[..],
            e: &e[..],
        })
        .unwrap();
        if !(bits == 1024 || (bits >= 2048 && bits % 2 == 0)) {
            assert_eq!(our_key.err(), Some(refused), "{bits} bits");
            continue;
        }
        let our_key = our_key.unwrap();
        assert_eq!(our_key.modulus_len(), their_key.modulus_len());
        let signature = vec![0x5a; n.len()];
        for (ours, theirs) in algorithms {
            same_error(
                &our_key.verify(ours, MESSAGE, &signature),
                &their_key.verify(theirs, MESSAGE, &signature),
            );
        }
    }
    assert_eq!(rsa::PublicKey::new(RSA2047_PUBLIC).err(), Some(refused));
    assert!(rind::rsa::PublicKey::new(RSA2047_PUBLIC).is_ok());
}

#[test]
fn ed25519_public_keys_verify_as_rind_does() {
    let signer = rind::ed25519::KeyPair::from_seed(&[9; 32]).unwrap();
    let signature = signer.sign(MESSAGE);
    let encoded = signer.public_key().as_ref();

    let reference = rind::ed25519::PublicKey::new(encoded).unwrap();
    let key = ed25519::PublicKey::new(encoded).unwrap();
    same_debug(&key, &reference);
    same_verdicts(
        |m, s| key.verify(m, s),
        |m, s| reference.verify(m, s),
        signature.as_ref(),
    );
    same_parse(
        ed25519::PublicKey::new,
        rind::ed25519::PublicKey::new,
        encoded,
    );

    let spki = reference.to_spki();
    assert_eq!(key.to_spki().as_ref(), spki.as_ref());
    same_parse(
        ed25519::PublicKey::from_spki,
        rind::ed25519::PublicKey::from_spki,
        spki.as_ref(),
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
    let reference = rind::ed25519::KeyPair::from_seed(&seed).unwrap();
    let key = ed25519::KeyPair::from_seed(&seed).unwrap();
    same_debug(&key, &reference);
    same_debug(key.public_key(), reference.public_key());
    assert_eq!(key.sign(MESSAGE).as_ref(), reference.sign(MESSAGE).as_ref());
    same_debug(&key.sign(MESSAGE), &reference.sign(MESSAGE));
    assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
    assert_eq!(key.to_pkcs8v1().as_ref(), reference.to_pkcs8v1().as_ref());
    assert_eq!(key.to_seed().as_ref(), reference.to_seed().as_ref());
    same_debug(&key.to_seed(), &reference.to_seed());
    assert_eq!(
        key.public_key().to_spki().as_ref(),
        reference.public_key().to_spki().as_ref()
    );

    for pkcs8 in [reference.to_pkcs8(), reference.to_pkcs8v1()] {
        let loaded = ed25519::KeyPair::from_pkcs8(pkcs8.as_ref()).unwrap();
        assert_eq!(
            loaded.sign(MESSAGE).as_ref(),
            reference.sign(MESSAGE).as_ref()
        );
    }
    let public = reference.public_key();
    ed25519::KeyPair::from_seed_and_public_key(&seed, public.as_ref()).unwrap();

    let mut wrong = public.as_ref().to_vec();
    wrong[0] ^= 1;
    same_error(
        &ed25519::KeyPair::from_seed_and_public_key(&seed, &wrong),
        &rind::ed25519::KeyPair::from_seed_and_public_key(&seed, &wrong),
    );
    let pkcs8 = reference.to_pkcs8();
    let bad_cases: [&[u8]; 4] = [&seed[1..], &[], &pkcs8.as_ref()[1..], P256];
    for bad in bad_cases {
        same_error(
            &ed25519::KeyPair::from_seed(bad),
            &rind::ed25519::KeyPair::from_seed(bad),
        );
        same_error(
            &ed25519::KeyPair::from_pkcs8(bad),
            &rind::ed25519::KeyPair::from_pkcs8(bad),
        );
    }

    let generated = ed25519::KeyPair::generate().unwrap();
    let reference = rind::ed25519::KeyPair::from_pkcs8(generated.to_pkcs8().as_ref()).unwrap();
    assert_eq!(
        generated.sign(MESSAGE).as_ref(),
        reference.sign(MESSAGE).as_ref()
    );
}

fn ml_dsa_matches_rind<P: ml_dsa::ParameterSet, Q: rind::ml_dsa::ParameterSet>() {
    let seed = [3; 32];
    let reference = rind::ml_dsa::KeyPair::<Q>::from_seed(&seed).unwrap();
    let key = ml_dsa::KeyPair::<P>::from_seed(&seed).unwrap();
    same_debug(&key, &reference);
    same_debug(key.public_key(), reference.public_key());
    assert_eq!(key.to_pkcs8().as_ref(), reference.to_pkcs8().as_ref());
    assert_eq!(
        key.to_seed().unwrap().as_ref(),
        reference.to_seed().unwrap().as_ref()
    );
    assert!(key.has_seed());
    same_debug(&key.to_seed().unwrap(), &reference.to_seed().unwrap());

    // Signatures are hedged, so cross rather than match.
    let signature = key.sign(MESSAGE).unwrap();
    let their_signature = reference.sign(MESSAGE).unwrap();
    assert_eq!(signature.as_ref().len(), their_signature.as_ref().len());
    let cloned = signature.clone();
    assert_eq!(format!("{cloned:?}"), format!("{signature:?}"));

    // Public keys verify alike, and parse alike.
    let encoded = reference.public_key().as_ref();
    let our_public = ml_dsa::PublicKey::<P>::new(encoded).unwrap();
    let their_public = rind::ml_dsa::PublicKey::<Q>::new(encoded).unwrap();
    their_public.verify(MESSAGE, signature.as_ref()).unwrap();
    same_verdicts(
        |m, s| our_public.verify(m, s),
        |m, s| their_public.verify(m, s),
        their_signature.as_ref(),
    );
    same_parse(
        ml_dsa::PublicKey::<P>::new,
        rind::ml_dsa::PublicKey::<Q>::new,
        encoded,
    );
    let spki = their_public.to_spki();
    assert_eq!(our_public.to_spki().as_ref(), spki.as_ref());
    same_parse(
        ml_dsa::PublicKey::<P>::from_spki,
        rind::ml_dsa::PublicKey::<Q>::from_spki,
        spki.as_ref(),
    );

    let loaded = ml_dsa::KeyPair::<P>::from_pkcs8(reference.to_pkcs8().as_ref()).unwrap();
    assert_eq!(
        loaded.public_key().as_ref(),
        reference.public_key().as_ref()
    );

    let generated = ml_dsa::KeyPair::<P>::generate().unwrap();
    let reloaded = rind::ml_dsa::KeyPair::<Q>::from_pkcs8(generated.to_pkcs8().as_ref()).unwrap();
    assert_eq!(
        generated.public_key().as_ref(),
        reloaded.public_key().as_ref()
    );

    let pkcs8 = reference.to_pkcs8();
    let bad_cases: [&[u8]; 4] = [&seed[1..], &[], &pkcs8.as_ref()[1..], P256];
    for bad in bad_cases {
        same_error(
            &ml_dsa::KeyPair::<P>::from_seed(bad),
            &rind::ml_dsa::KeyPair::<Q>::from_seed(bad),
        );
        same_error(
            &ml_dsa::KeyPair::<P>::from_pkcs8(bad),
            &rind::ml_dsa::KeyPair::<Q>::from_pkcs8(bad),
        );
    }
}

#[test]
fn ml_dsa_key_pairs_match_rind() {
    use rind_fips::ml_dsa::{MlDsa44, MlDsa65, MlDsa87};
    ml_dsa_matches_rind::<MlDsa44, rind::ml_dsa::MlDsa44>();
    ml_dsa_matches_rind::<MlDsa65, rind::ml_dsa::MlDsa65>();
    ml_dsa_matches_rind::<MlDsa87, rind::ml_dsa::MlDsa87>();
}

#[test]
fn cloned_public_keys_outlive_their_key_pairs() {
    // A clone holds a handle of its own, as rind's owned copy is a value of
    // its own, so it verifies once its key pair is gone.
    let (key, signature) = {
        let pair = ecdsa::KeyPair::from_pkcs8(&ecdsa::sign::P256_SHA256_ASN1, P256).unwrap();
        (pair.public_key().clone(), pair.sign(MESSAGE).unwrap())
    };
    same_debug(&key, &key.clone());
    key.verify(MESSAGE, signature.as_ref()).unwrap();

    let (key, signature) = {
        let pair = rsa::KeyPair::from_pkcs8(RSA2048).unwrap();
        let signature = pair.sign(&rsa::sign::PSS_SHA256, MESSAGE).unwrap();
        (pair.public_key().clone(), signature)
    };
    assert_eq!(key.modulus_len(), 256);
    key.verify(&rsa::verify::PSS_SHA256, MESSAGE, signature.as_ref())
        .unwrap();

    let (key, signature) = {
        let pair = ed25519::KeyPair::from_seed(&[1; 32]).unwrap();
        (pair.public_key().clone(), pair.sign(MESSAGE))
    };
    key.verify(MESSAGE, signature.as_ref()).unwrap();

    let (key, signature) = {
        let pair = ml_dsa::KeyPair::<ml_dsa::MlDsa44>::from_seed(&[1; 32]).unwrap();
        (pair.public_key().clone(), pair.sign(MESSAGE).unwrap())
    };
    assert_eq!(key.clone().as_ref(), key.as_ref());
    key.verify(MESSAGE, signature.as_ref()).unwrap();
}
